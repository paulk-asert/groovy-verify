/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package verification

import groovy.transform.CompileStatic
import org.codehaus.groovy.ast.CodeVisitorSupport
import org.codehaus.groovy.ast.expr.CastExpression
import org.codehaus.groovy.ast.expr.ClassExpression
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.DeclarationExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.PropertyExpression
import org.codehaus.groovy.ast.expr.StaticMethodCallExpression
import org.codehaus.groovy.ast.expr.TupleExpression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.Statement

/**
 * Phase 289 — the BOUNDED ACTOR MAILBOX, the first send in {@code groovy.concurrent} that really blocks.
 *
 * <p>Everywhere else in this checker the deadlock certificate rests on "a send never blocks": a buffered
 * {@code AsyncChannel} queues and hands back an {@code Awaitable} the caller discards. That is not an
 * assumption, it is measured — {@code ActorMailboxSemanticsTest} drives eight sends into a capacity-2
 * channel with nothing draining and they all return. Capacity there is a hint to the reader, not a bound on
 * the sender. The one exception before this phase was a RENDEZVOUS channel ({@code create(0)}, Phase 272).
 *
 * <p>{@code ActorOptions.withBoundedMailbox(k, Overflow.BLOCK)} is the second, and it is a genuinely
 * different animal: the same test shows a send into a full BLOCK mailbox parking the calling thread until
 * space appears. So a burst into a bounded actor is a chain of blocking events, and the classic actor
 * footgun becomes a wait-for cycle the compiler can name: fill an actor's mailbox while its handler is
 * waiting for something only the filling process will send, and neither can move.
 *
 * <p>The other two policies do not block, and are modelled as what they are. {@code DROP_NEWEST} discards
 * silently; {@code FAIL} throws at the sender. Under either, a {@code sendAndGet} past the bound has its
 * reply bound to {@code IllegalStateException} (measured, and NOT documented on {@code Overflow} the way it
 * is on {@code StashOverflow}) — so the caller is not stranded, but a claim ABOUT that reply can only hold
 * by luck, which is refused in the same spirit as a correlated claim on a shared reply end (Phase 285).
 *
 * <p><b>Deliberately narrow.</b> Only a literal capacity and a literal policy are modelled; only sends in
 * the method body proper are counted, and only a handler that blocks on a channel receive is treated as
 * unable to drain. Anything else is left alone rather than guessed at — an actor whose handler always
 * returns drains its mailbox, and no claim is made about it either way.
 */
@CompileStatic
class ActorMailbox {

    /** One finding: the message Reporter has already formatted, and where to anchor it. */
    static class Finding {
        String message
        Expression anchor
        Finding(String m, Expression a) { this.message = m; this.anchor = a }
    }

    /** A recognised actor local: its mailbox bound, its overflow policy, and its handler body. */
    private static class ActorDecl {
        String name
        int capacity = -1              // -1 = unbounded (no withBoundedMailbox)
        String policy                  // BLOCK / DROP_NEWEST / FAIL, or null when unbounded
        ClosureExpression handler
        int line
    }

    /** A send to an actor, in program order within the method body. */
    private static class Send {
        String actor; int ord; int line; boolean andGet; boolean conditional
        Expression anchor
        String replyVar                // the local the sendAndGet Awaitable is bound to, or null
    }

    static Expression strip(Expression e) {
        Expression x = e
        while (x instanceof CastExpression) x = ((CastExpression) x).expression
        x
    }

    /** `Actor.reactor(…)` / `Actor.stateful(…)` however the parser spelled the static call. */
    private static TupleExpression actorFactoryArgs(Expression rhs) {
        Expression r = strip(rhs)
        if (r instanceof StaticMethodCallExpression) {
            StaticMethodCallExpression s = (StaticMethodCallExpression) r
            if (s.ownerType?.nameWithoutPackage == 'Actor' && (s.method == 'reactor' || s.method == 'stateful')) {
                return s.arguments instanceof TupleExpression ? (TupleExpression) s.arguments : null
            }
            return null
        }
        if (r instanceof MethodCallExpression) {
            MethodCallExpression m = (MethodCallExpression) r
            String mn = m.methodAsString
            if (mn != 'reactor' && mn != 'stateful') return null
            Expression o = m.objectExpression
            String owner = o instanceof ClassExpression ? ((ClassExpression) o).type.nameWithoutPackage :
                           (o instanceof VariableExpression ? ((VariableExpression) o).name : null)
            if (owner != 'Actor') return null
            return m.arguments instanceof TupleExpression ? (TupleExpression) m.arguments : null
        }
        null
    }

    /** The handler closure of an {@code Actor} factory call, else null. An actor's handler runs on the
     *  actor's own worker thread, concurrently with whatever forked it — so to every concurrency pass in
     *  this checker it is a PROCESS, exactly like an {@code async \{ … \}} arm, and its channel operations
     *  must be attributed to it rather than to the enclosing body. Without that, a handler that waits on a
     *  channel reads as a sequential receive in the caller and the caller is falsely accused of deadlock. */
    static ClosureExpression handlerClosure(Expression e) {
        TupleExpression args = actorFactoryArgs(e)
        if (args == null) return null
        for (Expression a : args.expressions) {
            Expression x = strip(a)
            if (x instanceof ClosureExpression) return (ClosureExpression) x
        }
        null
    }

    /** True when this expression is an {@code Actor} factory call — which returns an actor or throws, so a
     *  local bound to one is never null (the same justification as a constructor call, Phase 277). */
    static boolean isActorFactory(Expression e) { actorFactoryArgs(e) != null }

    /** Read `…withBoundedMailbox(k, ActorOptions.Overflow.X)` off an options expression. */
    private static void readBound(Expression opts, ActorDecl d) {
        Expression e = strip(opts)
        while (e instanceof MethodCallExpression) {
            MethodCallExpression m = (MethodCallExpression) e
            if (m.methodAsString == 'withBoundedMailbox' && m.arguments instanceof TupleExpression) {
                List<Expression> as = ((TupleExpression) m.arguments).expressions
                if (as.size() == 2) {
                    Expression cap = strip(as.get(0)), pol = strip(as.get(1))
                    if (cap instanceof ConstantExpression && ((ConstantExpression) cap).value instanceof Integer) {
                        d.capacity = (Integer) ((ConstantExpression) cap).value
                    }
                    if (pol instanceof PropertyExpression) d.policy = ((PropertyExpression) pol).propertyAsString
                    else if (pol instanceof VariableExpression) d.policy = ((VariableExpression) pol).name
                }
                return
            }
            e = strip(m.objectExpression)          // walk back down the builder chain
        }
    }

    /** The actors declared in this body, by local name. */
    private static Map<String, ActorDecl> actorsIn(BlockStatement body) {
        Map<String, ActorDecl> out = new LinkedHashMap<String, ActorDecl>()
        body.visit(new CodeVisitorSupport() {
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (de.leftExpression instanceof VariableExpression) {
                    TupleExpression args = actorFactoryArgs(de.rightExpression)
                    if (args != null) {
                        ActorDecl d = new ActorDecl()
                        d.name = ((VariableExpression) de.leftExpression).name
                        d.line = de.lineNumber
                        for (Expression a : args.expressions) {
                            Expression s = strip(a)
                            if (s instanceof ClosureExpression && d.handler == null) d.handler = (ClosureExpression) s
                        }
                        if (!args.expressions.isEmpty()) readBound(args.expressions.get(args.expressions.size() - 1), d)
                        out.put(d.name, d)
                    }
                }
                super.visitDeclarationExpression(de)
            }
        })
        out
    }

    /** Channels a closure BLOCKS on: a receive whose value it waits for. */
    private static Map<String, Integer> blockingReceivesIn(ClosureExpression cl) {
        Map<String, Integer> out = new LinkedHashMap<String, Integer>()
        if (cl?.code == null) return out
        cl.code.visit(new CodeVisitorSupport() {
            @Override void visitMethodCallExpression(MethodCallExpression call) {
                String mn = call.methodAsString
                if ((mn == 'first' || mn == 'receive') && strip(call.objectExpression) instanceof VariableExpression) {
                    String c = ((VariableExpression) strip(call.objectExpression)).name
                    if (!out.containsKey(c)) out.put(c, call.lineNumber)
                }
                super.visitMethodCallExpression(call)
            }
        })
        out
    }

    /**
     * The check. Returns the findings; the caller reports them (so this file stays free of the STC API).
     */
    static List<Finding> check(String methodName, BlockStatement body) {
        List<Finding> out = new ArrayList<Finding>()
        Map<String, ActorDecl> actors = actorsIn(body)
        if (actors.isEmpty()) return out

        // Program-order pass over the body's own statements: sends to each actor, and sends on each channel.
        List<Send> sends = new ArrayList<Send>()
        Map<String, Integer> channelSendOrd = new LinkedHashMap<String, Integer>()
        Map<String, Integer> channelSendLine = new LinkedHashMap<String, Integer>()
        List<Statement> stmts = body.statements
        for (int i = 0; i < stmts.size(); i++) {
            final int ord = i
            stmts.get(i).visit(new CodeVisitorSupport() {
                @Override void visitClosureExpression(ClosureExpression ce) { /* a closure is another process */ }
                @Override void visitDeclarationExpression(DeclarationExpression de) {
                    Expression r = strip(de.rightExpression)
                    if (r instanceof MethodCallExpression && de.leftExpression instanceof VariableExpression) {
                        noteCall((MethodCallExpression) r, ord, ((VariableExpression) de.leftExpression).name)
                    }
                    super.visitDeclarationExpression(de)
                }
                @Override void visitMethodCallExpression(MethodCallExpression call) {
                    noteCall(call, ord, null)
                    super.visitMethodCallExpression(call)
                }
                private void noteCall(MethodCallExpression call, int o, String bound) {
                    String mn = call.methodAsString
                    Expression recv = strip(call.objectExpression)
                    if (!(recv instanceof VariableExpression)) return
                    String target = ((VariableExpression) recv).name
                    if ((mn == 'send' || mn == 'sendAndGet') && actors.containsKey(target)) {
                        Send s = new Send()
                        s.actor = target; s.ord = o; s.line = call.lineNumber
                        s.andGet = (mn == 'sendAndGet'); s.anchor = call; s.replyVar = bound
                        sends.add(s)
                    } else if (mn == 'send' && !actors.containsKey(target)) {
                        if (!channelSendOrd.containsKey(target)) {
                            channelSendOrd.put(target, o); channelSendLine.put(target, call.lineNumber)
                        }
                    }
                }
            })
        }

        for (ActorDecl d : actors.values()) {
            List<Send> mine = sends.findAll { Send s -> s.actor == d.name }.toList()
            if (mine.isEmpty()) continue

            if (d.capacity < 0) continue                      // unbounded: a send never blocks, nothing to say

            if (d.policy == null) {                           // bounded, but the policy is not a literal
                out.add(new Finding(Reporter.formatActorMailboxSkipped(methodName, d.name,
                    'its overflow policy is not a literal ActorOptions.Overflow constant'), mine.get(0).anchor))
                continue
            }

            if (d.policy == 'BLOCK') {
                // One message can be in the handler and `capacity` more in the box, so the (capacity + 2)-th
                // send is the first that must wait for the handler to take one.
                int blockAt = d.capacity + 2
                if (mine.size() < blockAt) continue           // the burst fits: nothing blocks, nothing to report
                Send blocked = mine.get(blockAt - 1)
                Map<String, Integer> waits = blockingReceivesIn(d.handler)
                for (Map.Entry<String, Integer> w : waits.entrySet()) {
                    Integer feedOrd = channelSendOrd.get(w.key)
                    if (feedOrd != null && feedOrd > blocked.ord) {
                        out.add(new Finding(Reporter.formatActorMailboxDeadlock(methodName, d.name, d.capacity,
                            blocked.line, blockAt, w.key, w.value, channelSendLine.get(w.key)), blocked.anchor))
                        break
                    }
                }
                continue
            }

            // DROP_NEWEST / FAIL — nothing blocks, but a send past the bound is lost or throws, and the
            // measured behaviour is that such a sendAndGet's reply is bound to IllegalStateException.
            int lossAt = d.capacity + 2
            if (mine.size() < lossAt) continue
            for (int i = lossAt - 1; i < mine.size(); i++) {
                Send s = mine.get(i)
                if (s.andGet && s.replyVar != null) {
                    out.add(new Finding(Reporter.formatActorMailboxLossy(methodName, d.name, d.capacity,
                        d.policy, s.line, s.replyVar), s.anchor))
                    break
                }
            }
        }
        out
    }
}
