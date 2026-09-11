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
import org.codehaus.groovy.ast.Parameter
import org.codehaus.groovy.ast.expr.BinaryExpression
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
import org.codehaus.groovy.ast.stmt.EmptyStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.IfStatement
import org.codehaus.groovy.ast.stmt.ReturnStatement
import org.codehaus.groovy.ast.stmt.Statement
import org.codehaus.groovy.syntax.Types

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
        Expression handlerExpr         // the handler argument as written — a closure, or a behaviour local (Phase 292)
        boolean stateful               // Actor.stateful: the context is the first of THREE handler params
        int stashCapacity = -1         // -1 = unbounded stash (no withStashBound) — Phase 292 slice 2
        String stashPolicy             // FAIL / DROP_OLDEST / REJECT, or null
    }

    /** A send to an actor, in program order within the method body. */
    private static class Send {
        String actor; int ord; int line; boolean andGet; boolean conditional
        Expression anchor
        String replyVar                // the local the sendAndGet Awaitable is bound to, or null
        Expression arg                 // the message, when the send has exactly one argument (Phase 292 slice 2)
        boolean topLevel               // the send IS a statement of the body — not nested in an if / loop / closure
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

    /**
     * Phase 292 — the context parameters of context-aware actor callbacks, by name. The {@code ActorContext} the
     * runtime passes a handler, a {@code become} target or a context-aware {@code onError} is the dispatch's own
     * context and never null — without this, the Groovy docs' own FSM example carried an undischargeable deref
     * obligation on every {@code ctx.become(…)} / {@code ctx.stash()}. Recognised by: a first parameter typed
     * {@code ActorContext}; a closure cast to {@code ReactorHandler} (context first of 2) or {@code StatefulHandler}
     * (first of 3), which covers the docs' untyped {@code { ctx, s, m -> … } as StatefulHandler}; an actor factory's
     * handler literal with the context-aware arity; and a three-parameter {@code onError} callback.
     */
    static Set<String> contextParamNames(Statement code) {
        Set<String> out = new HashSet<String>()
        if (code == null) return out
        code.visit(new CodeVisitorSupport() {
            private void addFirst(Expression e, int arity) {
                Expression x = strip(e)
                if (!(x instanceof ClosureExpression)) return
                Parameter[] ps = ((ClosureExpression) x).parameters
                if (ps != null && ps.length == arity) out.add(ps[0].name)
            }
            private void factoryHandler(Expression call, String method) {
                TupleExpression args = actorFactoryArgs(call)
                if (args == null) return
                boolean stateful = method == 'stateful'
                int hi = stateful ? 1 : 0
                if (args.expressions.size() > hi) addFirst(args.expressions.get(hi), stateful ? 3 : 2)
            }
            @Override void visitClosureExpression(ClosureExpression cl) {
                Parameter[] ps = cl.parameters
                if (ps != null && ps.length > 0 && !ps[0].isDynamicTyped()
                        && ps[0].type?.nameWithoutPackage == 'ActorContext') out.add(ps[0].name)
                super.visitClosureExpression(cl)
            }
            @Override void visitCastExpression(CastExpression ce) {
                String t = ce.type?.nameWithoutPackage
                if (t == 'ReactorHandler') addFirst(ce.expression, 2)
                else if (t == 'StatefulHandler') addFirst(ce.expression, 3)
                super.visitCastExpression(ce)
            }
            @Override void visitStaticMethodCallExpression(StaticMethodCallExpression call) {
                factoryHandler(call, call.method)
                super.visitStaticMethodCallExpression(call)
            }
            @Override void visitMethodCallExpression(MethodCallExpression call) {
                factoryHandler(call, call.methodAsString)
                if (call.methodAsString == 'onError' && call.arguments instanceof TupleExpression) {
                    for (Expression a : ((TupleExpression) call.arguments).expressions) addFirst(a, 3)
                }
                super.visitMethodCallExpression(call)
            }
        })
        out
    }

    /** Read `…withBoundedMailbox(k, ActorOptions.Overflow.X)` and `…withStashBound(n, ActorOptions.StashOverflow.Y)`
     *  off an options expression — anywhere in the builder chain, the outermost call of each kind winning. */
    private static void readBound(Expression opts, ActorDecl d) {
        Expression e = strip(opts)
        boolean mailboxSeen = false, stashSeen = false
        while (e instanceof MethodCallExpression) {
            MethodCallExpression m = (MethodCallExpression) e
            String mn = m.methodAsString
            boolean mailbox = mn == 'withBoundedMailbox' && !mailboxSeen
            boolean stash = mn == 'withStashBound' && !stashSeen   // Phase 292 slice 2
            if ((mailbox || stash) && m.arguments instanceof TupleExpression) {
                List<Expression> as = ((TupleExpression) m.arguments).expressions
                if (as.size() == 2) {
                    Expression cap = strip(as.get(0)), pol = strip(as.get(1))
                    Integer c = cap instanceof ConstantExpression && ((ConstantExpression) cap).value instanceof Integer ?
                        (Integer) ((ConstantExpression) cap).value : null
                    String p = pol instanceof PropertyExpression ? ((PropertyExpression) pol).propertyAsString :
                               pol instanceof VariableExpression ? ((VariableExpression) pol).name : null
                    if (mailbox) {
                        if (c != null) d.capacity = c
                        d.policy = p
                        mailboxSeen = true
                    } else {
                        if (c != null) d.stashCapacity = c
                        d.stashPolicy = p
                        stashSeen = true
                    }
                }
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
                        d.stateful = factoryMethod(de.rightExpression) == 'stateful'
                        int hi = d.stateful ? 1 : 0            // reactor(handler[, opts]) / stateful(init, handler[, opts])
                        if (args.expressions.size() > hi) d.handlerExpr = strip(args.expressions.get(hi))
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

    // ── Phase 292 — stash conservation ──────────────────────────────────────────────────────────────────────

    /** The factory method an actor declaration used ({@code reactor} / {@code stateful}), else null. */
    private static String factoryMethod(Expression rhs) {
        Expression r = strip(rhs)
        if (r instanceof StaticMethodCallExpression) return ((StaticMethodCallExpression) r).method
        if (r instanceof MethodCallExpression) return ((MethodCallExpression) r).methodAsString
        null
    }

    /** Behaviour locals: every closure a local is declared with or later assigned (`x = { … }`), by name — the
     *  documented FSM idiom declares its phases first and assigns them afterwards, so both forms count. */
    private static Map<String, List<ClosureExpression>> behaviourLocals(BlockStatement body) {
        Map<String, List<ClosureExpression>> out = new HashMap<String, List<ClosureExpression>>()
        body.visit(new CodeVisitorSupport() {
            @Override void visitBinaryExpression(BinaryExpression be) {
                Expression rhs = strip(be.rightExpression)
                if (be.operation.type == Types.ASSIGN && be.leftExpression instanceof VariableExpression
                        && rhs instanceof ClosureExpression) {
                    String n = ((VariableExpression) be.leftExpression).name
                    List<ClosureExpression> cls = out.get(n)
                    if (cls == null) { cls = new ArrayList<ClosureExpression>(); out.put(n, cls) }
                    cls.add((ClosureExpression) rhs)
                }
                super.visitBinaryExpression(be)
            }
        })
        out
    }

    /** The closures a handler / become argument denotes: itself if a literal, a behaviour local's closures, or
     *  null when it is opaque (a method result, a field, a parameter) — and then nothing may be claimed. */
    private static List<ClosureExpression> resolveBehaviour(Expression e, Map<String, List<ClosureExpression>> locals) {
        Expression x = e == null ? null : strip(e)
        if (x instanceof ClosureExpression) return [(ClosureExpression) x]
        if (x instanceof VariableExpression) return locals.get(((VariableExpression) x).name)
        null
    }

    /** A behaviour's context parameter: the first of a context-aware handler (reactor: 2 params, stateful: 3). */
    private static String ctxParam(ClosureExpression cl, boolean stateful) {
        Parameter[] ps = cl.parameters
        ps != null && ps.length == (stateful ? 3 : 2) ? ps[0].name : null
    }

    private static class BehaviourScan {
        MethodCallExpression stash
        List<Expression> becomeTargets = new ArrayList<Expression>()
        boolean escapes
    }

    /** One behaviour's own body — not its inline become targets, which are behaviours of their own: its first
     *  {@code ctx.stash()}, its {@code ctx.become(…)} targets, and whether {@code ctx} ESCAPES (is used as
     *  anything but the receiver of a direct context call — handed to a helper that might unstash, say). */
    private static BehaviourScan scanBehaviour(ClosureExpression cl, String ctx) {
        BehaviourScan s = new BehaviourScan()
        cl.code?.visit(new CodeVisitorSupport() {
            @Override void visitMethodCallExpression(MethodCallExpression call) {
                Expression recv = strip(call.objectExpression)
                if (recv instanceof VariableExpression && ((VariableExpression) recv).name == ctx) {
                    List<Expression> args = call.arguments instanceof TupleExpression ?
                        ((TupleExpression) call.arguments).expressions : Collections.<Expression> emptyList()
                    if (call.methodAsString == 'stash' && args.isEmpty() && s.stash == null) s.stash = call
                    if (call.methodAsString == 'become' && args.size() == 1) {
                        s.becomeTargets.add(args.get(0))
                        if (strip(args.get(0)) instanceof ClosureExpression) return   // scanned as its own behaviour
                    }
                    call.arguments.visit(this)          // the receiver `ctx` is a direct use, not an escape
                    return
                }
                super.visitMethodCallExpression(call)
            }
            @Override void visitVariableExpression(VariableExpression ve) {
                if (ve.name == ctx) s.escapes = true
            }
        })
        s
    }

    /**
     * Phase 292 — stash conservation. A stashed message comes back ONLY through {@code unstashAll()} — measured,
     * {@code ActorStashSemanticsTest}: without it the message never reaches a handler again, and at {@code stop()}
     * a sendAndGet reply fails with IllegalStateException and a send is discarded. So an actor that stashes, none
     * of whose behaviours ever calls {@code unstashAll()}, loses every message it stashes: a definite loss, not a
     * possible one. The claim is made only when the whole behaviour family is visible — the handler and every
     * {@code ctx.become(…)} target, inline or a local of this method — and nothing is claimed when anything is
     * opaque: a become target from elsewhere, the context handed on, or an {@code unstashAll()} anywhere in the
     * method (a context-aware onError callback, say).
     */
    private static List<Finding> stashFindings(String methodName, BlockStatement body, Map<String, ActorDecl> actors) {
        List<Finding> out = new ArrayList<Finding>()
        boolean[] unstashAnywhere = [false] as boolean[]
        body.visit(new CodeVisitorSupport() {
            @Override void visitMethodCallExpression(MethodCallExpression call) {
                if (call.methodAsString == 'unstashAll') unstashAnywhere[0] = true
                super.visitMethodCallExpression(call)
            }
        })
        if (unstashAnywhere[0]) return out
        Map<String, List<ClosureExpression>> locals = behaviourLocals(body)
        for (ActorDecl d : actors.values()) {
            List<ClosureExpression> roots = resolveBehaviour(d.handlerExpr, locals)
            if (roots == null) continue
            Set<ClosureExpression> family = Collections.newSetFromMap(new IdentityHashMap<ClosureExpression, Boolean>())
            Deque<ClosureExpression> todo = new ArrayDeque<ClosureExpression>(roots)
            boolean opaque = false
            MethodCallExpression firstStash = null
            while (!todo.isEmpty() && !opaque) {
                ClosureExpression cl = todo.poll()
                if (!family.add(cl)) continue
                String ctx = ctxParam(cl, d.stateful)
                if (ctx == null) continue                     // no context: this behaviour can neither stash nor become
                BehaviourScan scan = scanBehaviour(cl, ctx)
                if (scan.escapes) { opaque = true; break }
                if (firstStash == null && scan.stash != null) firstStash = scan.stash
                for (Expression target : scan.becomeTargets) {
                    List<ClosureExpression> next = resolveBehaviour(target, locals)
                    if (next == null) { opaque = true; break }
                    todo.addAll(next)
                }
            }
            if (opaque || firstStash == null) continue
            out.add(new Finding(Reporter.formatStashNeverReplayed(methodName, d.name, firstStash.lineNumber), firstStash))
        }
        out
    }

    // ── Phase 292 slice 2 — the stash bound ─────────────────────────────────────────────────────────────────

    private static final Object NO_TRIGGER = new Object()

    /** The literal a message is compared with in {@code m == LIT} / {@code LIT == m}, else NO_TRIGGER. */
    private static Object triggerLiteral(Expression cond, String msg) {
        if (!(cond instanceof BinaryExpression)) return NO_TRIGGER
        BinaryExpression be = (BinaryExpression) cond
        if (be.operation.type != Types.COMPARE_EQUAL) return NO_TRIGGER
        Expression l = strip(be.leftExpression), r = strip(be.rightExpression)
        if (l instanceof VariableExpression && ((VariableExpression) l).name == msg && r instanceof ConstantExpression) {
            return ((ConstantExpression) r).value
        }
        if (r instanceof VariableExpression && ((VariableExpression) r).name == msg && l instanceof ConstantExpression) {
            return ((ConstantExpression) l).value
        }
        NO_TRIGGER
    }

    /** {@code stmt} is — or a block beginning with — the statement {@code ctx.stash()}. */
    private static boolean isStashStatement(Statement stmt, String ctx) {
        Statement s = stmt
        if (s instanceof BlockStatement) {
            List<Statement> ss = ((BlockStatement) s).statements
            if (ss.isEmpty()) return false
            s = ss.get(0)
        }
        if (!(s instanceof ExpressionStatement)) return false
        Expression e = strip(((ExpressionStatement) s).expression)
        if (!(e instanceof MethodCallExpression)) return false
        MethodCallExpression c = (MethodCallExpression) e
        Expression recv = strip(c.objectExpression)
        c.methodAsString == 'stash' && recv instanceof VariableExpression && ((VariableExpression) recv).name == ctx &&
            (!(c.arguments instanceof TupleExpression) || ((TupleExpression) c.arguments).expressions.isEmpty())
    }

    private static boolean endsInReturn(Statement stmt) {
        if (stmt instanceof ReturnStatement) return true
        if (stmt instanceof BlockStatement) {
            List<Statement> ss = ((BlockStatement) stmt).statements
            return !ss.isEmpty() && ss.get(ss.size() - 1) instanceof ReturnStatement
        }
        false
    }

    /**
     * The "stash until LIT" handler — the documented idiom, recognised strictly: the handler's FIRST statement is
     * {@code if (m == LIT) { … return … }} followed directly by {@code ctx.stash()}, or {@code if (m == LIT) { … }
     * else { ctx.stash() … }}. Every message but LIT is then stashed, which is what makes a count of the messages
     * sent before LIT a count of the stash. Any other shape: NO_TRIGGER, and nothing is claimed.
     */
    private static Object stashTrigger(ClosureExpression h, boolean stateful) {
        Parameter[] ps = h?.parameters
        if (ps == null || ps.length != (stateful ? 3 : 2) || !(h.code instanceof BlockStatement)) return NO_TRIGGER
        String ctx = ps[0].name, msg = ps[ps.length - 1].name
        List<Statement> ss = ((BlockStatement) h.code).statements
        if (ss.isEmpty() || !(ss.get(0) instanceof IfStatement)) return NO_TRIGGER
        IfStatement ifs = (IfStatement) ss.get(0)
        Object lit = triggerLiteral(ifs.booleanExpression.expression, msg)
        if (lit.is(NO_TRIGGER)) return NO_TRIGGER
        boolean hasElse = ifs.elseBlock != null && !(ifs.elseBlock instanceof EmptyStatement)
        if (hasElse) return isStashStatement(ifs.elseBlock, ctx) ? lit : NO_TRIGGER
        endsInReturn(ifs.ifBlock) && ss.size() > 1 && isStashStatement(ss.get(1), ctx) ? lit : NO_TRIGGER
    }

    /** The actor local is used as anything but the receiver of its own send / sendAndGet / stop / close — handed on,
     *  stored, captured by a closure — so another sender could deliver the trigger first and the count means nothing. */
    private static boolean actorEscapes(String actor, BlockStatement body) {
        Set<String> own = ['send', 'sendAndGet', 'stop', 'close', 'isActive', 'isTerminated'] as Set<String>
        boolean[] escaped = [false] as boolean[]
        body.visit(new CodeVisitorSupport() {
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (de.leftExpression instanceof VariableExpression && ((VariableExpression) de.leftExpression).name == actor) {
                    de.rightExpression.visit(this)     // the declaration itself is not a use
                    return
                }
                super.visitDeclarationExpression(de)
            }
            @Override void visitMethodCallExpression(MethodCallExpression call) {
                Expression recv = strip(call.objectExpression)
                if (recv instanceof VariableExpression && ((VariableExpression) recv).name == actor && own.contains(call.methodAsString)) {
                    call.arguments.visit(this)
                    return
                }
                super.visitMethodCallExpression(call)
            }
            @Override void visitVariableExpression(VariableExpression ve) {
                if (ve.name == actor) escaped[0] = true
            }
        })
        escaped[0]
    }

    /**
     * Phase 292 slice 2 — a literal burst past {@code withStashBound(n, policy)}. For a "stash until LIT" handler, the
     * messages this method sends before LIT are exactly the ones stashed (a single sender's order is preserved), so
     * the (n+1)-th of them overruns the bound — and each policy's outcome is MEASURED (ActorStashSemanticsTest):
     * FAIL fails that message, DROP_OLDEST evicts the first stashed, REJECT refuses that message. In every policy
     * one message is lost. Nothing is claimed unless every send before LIT is a top-level literal (an unknown
     * message could BE the trigger) and the actor never escapes this method (another sender could send LIT first).
     */
    private static Finding stashOverflow(String methodName, ActorDecl d, List<Send> mine, BlockStatement body,
                                         Map<String, List<ClosureExpression>> behaviours) {
        if (d.stashCapacity < 0 || d.stashPolicy == null) return null
        List<ClosureExpression> hs = resolveBehaviour(d.handlerExpr, behaviours)
        if (hs == null || hs.size() != 1) return null
        Object lit = stashTrigger(hs.get(0), d.stateful)
        if (lit.is(NO_TRIGGER) || actorEscapes(d.name, body)) return null
        List<Send> stashed = new ArrayList<Send>()
        for (Send s : mine) {
            if (!s.topLevel || !(s.arg instanceof ConstantExpression)) return null
            if (((ConstantExpression) s.arg).value == lit) break
            stashed.add(s)
        }
        if (stashed.size() <= d.stashCapacity) return null
        Send over = stashed.get(d.stashCapacity)
        new Finding(Reporter.formatStashOverflow(methodName, d.name, lit, d.stashCapacity, d.stashPolicy,
            over.line, d.stashCapacity + 1, stashed.get(0).line), over.anchor)
    }

    /**
     * The check. Returns the findings; the caller reports them (so this file stays free of the STC API).
     */
    static List<Finding> check(String methodName, BlockStatement body) {
        List<Finding> out = new ArrayList<Finding>()
        Map<String, ActorDecl> actors = actorsIn(body)
        if (actors.isEmpty()) return out
        out.addAll(stashFindings(methodName, body, actors))   // Phase 292 — needs no sends, so it comes first
        Map<String, List<ClosureExpression>> behaviours = behaviourLocals(body)

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
                        List<Expression> sargs = call.arguments instanceof TupleExpression ?
                            ((TupleExpression) call.arguments).expressions : Collections.<Expression> emptyList()
                        s.arg = sargs.size() == 1 ? strip(sargs.get(0)) : null
                        Statement st = stmts.get(o)
                        Expression top = st instanceof ExpressionStatement ? strip(((ExpressionStatement) st).expression) : null
                        if (top instanceof DeclarationExpression) top = strip(((DeclarationExpression) top).rightExpression)
                        s.topLevel = top != null && top.is(call)
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

            // Phase 292 slice 2 — the stash bound, independent of the mailbox bound (so before its skips).
            Finding overflow = stashOverflow(methodName, d, mine, body, behaviours)
            if (overflow != null) out.add(overflow)

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
