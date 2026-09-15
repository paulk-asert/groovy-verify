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
import org.codehaus.groovy.ast.ASTNode
import org.codehaus.groovy.ast.ClassNode
import org.codehaus.groovy.ast.ConstructorNode
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.PropertyNode
import org.codehaus.groovy.ast.Variable
import org.codehaus.groovy.ast.FieldNode
import org.codehaus.groovy.syntax.Token
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
    private static List<Finding> stashFindings(String where, BlockStatement body, Map<String, ActorDecl> actors) {
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
            out.add(new Finding(Reporter.formatStashNeverReplayed(where, d.name, firstStash.lineNumber), firstStash))
        }
        out
    }

    // ── Phase 293 — the become-graph, for @Protocol conformance ────────────────────────────────────────────

    /** The actor locals of a body, by name (their declarations are what SessionChecker binds actor roles to). */
    static Set<String> actorNames(BlockStatement body) { new LinkedHashSet<String>(actorsIn(body).keySet()) }

    /** One arm of a phase: what an explicit {@code m == LIT} branch does with LIT. */
    static class Arm {
        int target = -1                 // the phase it moves to (-1: stays in this one)
        boolean stash, unstash, rejects
        Object reply = UNKNOWN_REPLY    // Phase 294 — the constant the arm returns, when it is one
        List<Timer> timers              // Phase 297 — the self-messages this arm schedules, if any
    }

    /** Phase 297 — a message an actor schedules FOR ITSELF: {@code ctx.scheduleOnce / scheduleAtFixedRate}. */
    static class Timer {
        String msg                      // the literal scheduled, or null when it is not one
        boolean repeats                 // scheduleAtFixedRate
        boolean discarded               // the Cancellable it returns is thrown away, so it can never be stopped
        Expression anchor
        int line
    }

    /** Phase 294 — the arm's return is not a readable constant, so nothing is claimed about the reply's label. */
    static final Object UNKNOWN_REPLY = new Object()

    /** One phase — a behaviour closure — of an actor's become-graph. */
    static class Phase {
        String name
        int line
        final Map<Object, Arm> on = new LinkedHashMap<Object, Arm>()   // literal message → its explicit arm
        String otherwise = 'handles'    // any other message: 'handles' (stays), 'stash', or 'rejects' (throws)
        Object otherwiseReply = UNKNOWN_REPLY                          // Phase 294 — the default branch's reply
        List<Timer> otherwiseTimers                                    // Phase 297 — the default branch's timers
        boolean timersUnreadable                                       // Phase 297 — an onError arms one: not modelled
        int onError = NO_ON_ERROR       // Phase 296 — the phase a throw recovers into; the edge is the ACTOR's,
    }                                   // measured global (it fires inside become targets too), so every phase carries it

    /** Phase 296 — no {@code onError} is installed: a throw is unhandled, and the message is simply rejected. */
    static final int NO_ON_ERROR = -2
    /** Phase 296 — the dispatch threw and an {@code onError} took it; the message was never processed. */
    static final Object THREW = new Object()

    /**
     * Phase 293 — an actor's become-graph, the automaton its role is checked with: the phases (the handler first,
     * then every {@code ctx.become(…)} target, inline or a behaviour local) and, per phase, what each literal
     * message does. Recognised strictly — a phase is a top-level chain of {@code if (m == LIT) { … }} arms, each
     * leaving (a {@code return}) or chained by {@code else}, then a default for every other message; a context-free
     * handler (a Function / BiFunction) is one catch-all phase. Null — nothing is claimed — for anything else: a
     * condition that is not {@code m == LIT}, a target that is not visible, a behaviour local assigned twice, an
     * arm or default whose effect cannot be read.
     */
    static List<Phase> becomeGraph(BlockStatement body, String actorName) {
        ActorDecl d = actorsIn(body).get(actorName)
        if (d == null) return null
        Map<String, List<ClosureExpression>> locals = behaviourLocals(body)
        List<Phase> phases = new ArrayList<Phase>()
        Map<ClosureExpression, Integer> index = new IdentityHashMap<ClosureExpression, Integer>()
        List<ClosureExpression> order = new ArrayList<ClosureExpression>()
        ClosureExpression root = singleBehaviour(d.handlerExpr, locals)
        if (root == null) return null
        String rootName = strip(d.handlerExpr) instanceof VariableExpression ? ((VariableExpression) strip(d.handlerExpr)).name : 'the handler'
        index.put(root, 0); order.add(root)
        Phase first = new Phase(); first.name = rootName; first.line = root.lineNumber; phases.add(first)
        // Phase 296 — the actor's onError callback, if any: a throw recovers into the phase it becomes (or stays
        // where it is). Registered before the worklist so a recovery phase is itself walked.
        int errorEdge = NO_ON_ERROR
        boolean errorTimers = false
        Expression cb = onErrorCallback(body, actorName)
        if (cb != null) {
            ClosureExpression ecl = singleBehaviour(cb, locals)
            if (ecl == null) return null
            Parameter[] eps = ecl.parameters
            if (eps == null || (eps.length != 2 && eps.length != 3)) return null
            if (eps.length == 2) errorEdge = -1                      // a (throwable, message) callback: no context
            else {
                if (!(ecl.code instanceof BlockStatement)) return null
                Arm ea = readArm((BlockStatement) ecl.code, eps[0].name, locals, index, order, phases)
                // a recovery that defers or replays is not modelled: the stash is Phase 292's, measured there
                if (ea == null || ea.stash || ea.unstash || ea.rejects) return null
                errorEdge = ea.target
                if (ea.timers != null) errorTimers = true               // Phase 297 — armed from any phase at all
            }
        }
        for (int i = 0; i < order.size(); i++) {
            ClosureExpression cl = order.get(i)
            Phase ph = phases.get(i)
            Parameter[] ps = cl.parameters
            int ctxArity = d.stateful ? 3 : 2
            if (ps == null || ps.length != ctxArity) {
                if (ps != null && ps.length == ctxArity - 1) continue   // context-free: one catch-all phase
                return null
            }
            String ctx = ps[0].name, msg = ps[ps.length - 1].name
            if (!(cl.code instanceof BlockStatement)) return null
            List<Statement> ss = ((BlockStatement) cl.code).statements
            int k = 0
            Statement defaultPart = null
            List<Statement> after = null
            Statement cur = ss.isEmpty() ? null : ss.get(0)
            while (cur instanceof IfStatement) {
                IfStatement ifs = (IfStatement) cur
                Object lit = triggerLiteral(ifs.booleanExpression.expression, msg)
                if (lit.is(NO_TRIGGER) || ph.on.containsKey(lit)) return null
                boolean hasElse = ifs.elseBlock != null && !(ifs.elseBlock instanceof EmptyStatement)
                // the arm must LEAVE the dispatch, by a return or (Phase 296) by throwing, else it falls through
                if (!hasElse && !endsInReturn(ifs.ifBlock) && !endsInThrow(ifs.ifBlock)) return null
                Arm arm = readArm(ifs.ifBlock, ctx, locals, index, order, phases)
                if (arm == null) return null
                if (arm.rejects && arm.target >= 0) return null   // Phase 296 — throws AND moves: which won is not readable
                ph.on.put(lit, arm)
                if (hasElse) {
                    if (ifs.elseBlock instanceof IfStatement) { cur = ifs.elseBlock; continue }
                    defaultPart = ifs.elseBlock
                    after = ss.subList(1, ss.size())                         // statements after an if/else run for all
                } else {
                    after = ss.subList(k + 1, ss.size())
                }
                break
            }
            if (!(ss.isEmpty() || ss.get(0) instanceof IfStatement)) after = ss
            // the default: the final else (if any) plus what follows the chain
            List<Statement> dflt = new ArrayList<Statement>()
            if (defaultPart != null) dflt.add(defaultPart)
            if (after != null) dflt.addAll(after)
            BlockStatement db = new BlockStatement(dflt, null)
            Arm da = readArm(db, ctx, locals, index, order, phases)
            if (da == null || da.target >= 0 || da.unstash) return null      // a default that moves or replays: not modelled
            ph.otherwise = da.rejects ? 'rejects' : da.stash ? 'stash' : 'handles'
            ph.otherwiseReply = da.reply                                 // Phase 294
            ph.otherwiseTimers = da.timers                               // Phase 297
            // an if/else's trailing statements also run for the matched message: fold their effect into each arm
            if (defaultPart != null && after != null && !after.isEmpty()) {
                Arm tail = readArm(new BlockStatement(new ArrayList<Statement>(after), null), ctx, locals, index, order, phases)
                if (tail == null || tail.target >= 0 || tail.unstash || tail.stash || tail.rejects) return null
            }
        }
        for (Phase ph : phases) { ph.onError = errorEdge; ph.timersUnreadable = errorTimers }   // Phase 296/297 — the actor's, not a phase's
        phases
    }

    /** Phase 296 — the callback of `actor.onError(…)` / `Actor.reactor(h).onError(…)`, else null. Two of them
     *  (the runtime keeps the last) are not modelled: the caller withholds the whole graph. */
    private static Expression onErrorCallback(BlockStatement body, String actorName) {
        final List<Expression> found = new ArrayList<Expression>()
        final boolean[] many = [false] as boolean[]
        body.visit(new CodeVisitorSupport() {
            @Override void visitMethodCallExpression(MethodCallExpression call) {
                super.visitMethodCallExpression(call)
                if (call.methodAsString != 'onError' || !(call.arguments instanceof TupleExpression)) return
                List<Expression> args = ((TupleExpression) call.arguments).expressions
                if (args.size() != 1) { many[0] = true; return }
                Expression recv = strip(call.objectExpression)
                boolean mine = (recv instanceof VariableExpression && ((VariableExpression) recv).name == actorName) ||
                               actorFactoryArgs(recv) != null      // chained straight off Actor.reactor(…)
                if (!mine) return
                if (!found.isEmpty()) many[0] = true
                found.add(args.get(0))
            }
        })
        many[0] ? NOT_MODELLED : (found.isEmpty() ? null : found.get(0))
    }

    /** A marker callback that makes {@link #becomeGraph} withhold the whole graph. */
    private static final Expression NOT_MODELLED = new ConstantExpression('not modelled')

    /** A behaviour argument that denotes exactly one closure (a literal, or a local assigned once), else null. */
    private static ClosureExpression singleBehaviour(Expression e, Map<String, List<ClosureExpression>> locals) {
        List<ClosureExpression> cls = resolveBehaviour(e, locals)
        cls != null && cls.size() == 1 ? cls.get(0) : null
    }

    /** What a block does, read for the protocol: its become target (registering a new phase), and whether it
     *  stashes, replays, or throws. Null when it is not readable — two targets, an opaque one, the context handed on. */
    private static Arm readArm(Statement block, String ctx, Map<String, List<ClosureExpression>> locals,
                               Map<ClosureExpression, Integer> index, List<ClosureExpression> order, List<Phase> phases) {
        Arm arm = new Arm()
        boolean[] bad = [false] as boolean[]
        List<Expression> targets = new ArrayList<Expression>()
        final Set<Expression> bare = discardedSchedules(block)          // Phase 297
        block.visit(new CodeVisitorSupport() {
            @Override void visitMethodCallExpression(MethodCallExpression call) {
                Expression recv = strip(call.objectExpression)
                if (recv instanceof VariableExpression && ((VariableExpression) recv).name == ctx) {
                    String mn = call.methodAsString
                    List<Expression> args = call.arguments instanceof TupleExpression ?
                        ((TupleExpression) call.arguments).expressions : Collections.<Expression> emptyList()
                    if (mn == 'stash') arm.stash = true
                    else if (mn == 'unstashAll') arm.unstash = true
                    else if (mn == 'become' && args.size() == 1) targets.add(args.get(0))
                    else if (mn == 'scheduleOnce' || mn == 'scheduleAtFixedRate') {          // Phase 297
                        Timer t = new Timer()
                        t.repeats = mn == 'scheduleAtFixedRate'
                        Expression m0 = args.isEmpty() ? null : strip(args.get(0))
                        t.msg = m0 instanceof ConstantExpression && ((ConstantExpression) m0).value != null ?
                            ((ConstantExpression) m0).value.toString() : null
                        t.anchor = call; t.line = call.lineNumber; t.discarded = bare.contains(call)
                        if (arm.timers == null) arm.timers = new ArrayList<Timer>()
                        arm.timers.add(t)
                    }
                    else if (mn != 'self') bad[0] = true
                    return                                   // a direct context call; its closure argument is a phase
                }
                super.visitMethodCallExpression(call)
            }
            @Override void visitVariableExpression(VariableExpression ve) { if (ve.name == ctx) bad[0] = true }
            @Override void visitThrowStatement(org.codehaus.groovy.ast.stmt.ThrowStatement ts) {
                arm.rejects = true
                super.visitThrowStatement(ts)
            }
            @Override void visitClosureExpression(ClosureExpression c) { }   // a nested closure is not this dispatch
        })
        if (bad[0] || targets.size() > 1) return null
        arm.reply = returnedConstant(block)                              // Phase 294
        if (targets.size() == 1) {
            ClosureExpression t = singleBehaviour(targets.get(0), locals)
            if (t == null) return null
            Integer ti = index.get(t)
            if (ti == null) {
                ti = order.size()
                index.put(t, ti); order.add(t)
                Phase p = new Phase()
                Expression te = strip(targets.get(0))
                p.name = te instanceof VariableExpression ? ((VariableExpression) te).name : "the phase at line ${t.lineNumber}".toString()
                p.line = t.lineNumber
                phases.add(p)
            }
            arm.target = ti
        }
        arm
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

    /**
     * Phase 294 — the constant a behaviour block yields: its terminal {@code return LIT} or trailing expression
     * {@code LIT}. For a REACTOR that value is the reply a {@code sendAndGet} is completed with (measured); for a
     * {@code stateful} actor it is the new STATE, so SessionChecker asks for it only of a reactor. UNKNOWN_REPLY
     * when it is not a readable constant — nothing is claimed about the reply's label then.
     */
    static Object returnedConstant(Statement stmt) {
        Statement last = stmt
        if (last instanceof BlockStatement) {
            List<Statement> ss = ((BlockStatement) last).statements
            if (ss.isEmpty()) return UNKNOWN_REPLY
            last = ss.get(ss.size() - 1)
        }
        Expression e = last instanceof ReturnStatement ? ((ReturnStatement) last).expression :
                       (last instanceof ExpressionStatement ? ((ExpressionStatement) last).expression : null)
        Expression v = e == null ? null : strip(e)
        v instanceof ConstantExpression && ((ConstantExpression) v).value != null ?
            ((ConstantExpression) v).value : UNKNOWN_REPLY
    }

    /** Phase 294 — true when the actor is a {@code reactor}: its handler's return IS the reply, not the state. */
    static boolean repliesAreValues(BlockStatement body, String actorName) {
        ActorDecl d = actorsIn(body).get(actorName)
        d != null && !d.stateful
    }

    /** Phase 296 — an arm that throws leaves the dispatch just as a return does (its message is not processed). */
    private static boolean endsInThrow(Statement stmt) {
        Statement last = stmt
        if (last instanceof BlockStatement) {
            List<Statement> ss = ((BlockStatement) last).statements
            if (ss.isEmpty()) return false
            last = ss.get(ss.size() - 1)
        }
        last instanceof org.codehaus.groovy.ast.stmt.ThrowStatement
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

    // ── Phase 297 — the actor's own timers ───────────────────────────────────────────────

    /** Every phase the actor can be in once {@code from} has run: become targets, transitively, plus the onError edge. */
    private static Set<Integer> reachableFrom(List<Phase> g, int from) {
        Set<Integer> seen = new LinkedHashSet<Integer>()
        List<Integer> todo = [from]
        while (!todo.isEmpty()) {
            int i = todo.remove(0)
            if (!seen.add(i)) continue
            Phase p = g.get(i)
            for (Arm a : p.on.values()) if (a.target >= 0) todo.add(a.target)
            if (p.onError >= 0) todo.add(p.onError)
        }
        seen
    }

    /** Phase 297 — the schedule calls made as bare STATEMENTS: their Cancellable is discarded, so nothing in the
     *  code can ever stop them. One whose result is kept (a local, a field, an array slot) may yet be cancelled,
     *  and nothing is claimed about it. */
    private static Set<Expression> discardedSchedules(Statement block) {
        final Set<Expression> out = Collections.newSetFromMap(new IdentityHashMap<Expression, Boolean>())
        block.visit(new CodeVisitorSupport() {
            @Override void visitExpressionStatement(ExpressionStatement es) {
                Expression e = strip(es.expression)
                if (e instanceof MethodCallExpression &&
                        ((MethodCallExpression) e).methodAsString in ['scheduleOnce', 'scheduleAtFixedRate']) out.add(e)
                super.visitExpressionStatement(es)
            }
            @Override void visitClosureExpression(ClosureExpression c) { }
        })
        out
    }

    /**
     * Phase 300 — why this method's sends are not the whole count for a field-held actor, or null when they are.
     * The field must be private (nothing outside the class can send to it) and exactly one method may send (no
     * sibling can interleave a trigger). Repeat CALLS of that one method are then the only other source, and
     * they can only repeat the same burst — which adds to a bound, never rescues one, so a refutation stands.
     */
    private static String exclusiveSenderReason(ClassNode owner, String actor, String methodName) {
        if (owner == null) return "it is not declared in this method and its class is unknown here"
        FieldNode f = owner.getField(actor)
        if (f == null) return "it is not declared in this method"
        // a field written without a modifier is a Groovy PROPERTY: the backing field is private but the generated
        // accessor is not, so the actor is reachable from outside and anyone may send to it.
        if (owner.getProperty(actor) != null || !f.private) {
            return "'${actor}' is ${owner.getProperty(actor) != null ? 'a property, so its generated accessor lets code outside' : 'not a private field, so code outside'} ${owner.nameWithoutPackage} send to it too".toString()
        }
        List<String> senders = sendingMethods(owner, actor)
        if (senders.size() > 1) {
            return "${senders.size()} methods of ${owner.nameWithoutPackage} send to '${actor}' (${senders.join(', ')}), so this method's sends are not the whole count — a sibling can interleave with them".toString()
        }
        null
    }

    /** Phase 300 — the names of the methods and constructors of a class that send to a given actor. */
    private static List<String> sendingMethods(ClassNode owner, String actor) {
        final Set<String> out = new LinkedHashSet<String>()
        List<MethodNode> all = new ArrayList<MethodNode>(owner.methods ?: Collections.<MethodNode> emptyList())
        all.addAll(owner.declaredConstructors ?: Collections.<ConstructorNode> emptyList())
        for (MethodNode mn : all) {
            if (mn.code == null) continue
            final String who = mn instanceof ConstructorNode ? "${owner.nameWithoutPackage}()".toString() : "${mn.name}()".toString()
            mn.code.visit(new CodeVisitorSupport() {
                @Override void visitMethodCallExpression(MethodCallExpression call) {
                    Expression recv = strip(call.objectExpression)
                    if ((call.methodAsString == 'send' || call.methodAsString == 'sendAndGet') &&
                            recv instanceof VariableExpression && ((VariableExpression) recv).name == actor) out.add(who)
                    super.visitMethodCallExpression(call)
                }
            })
        }
        new ArrayList<String>(out)
    }

    /** The explicit arm a phase has for a literal message, else null. */
    private static Arm armFor(Phase p, String msg) {
        for (Map.Entry<Object, Arm> e : p.on.entrySet()) if (String.valueOf(e.key) == msg) return e.value
        null
    }

    /**
     * Phase 297 — a message an actor schedules for ITSELF lands in whatever phase is current WHEN THE TIMER FIRES,
     * not the one that armed it (measured), and a repeat goes on firing across every {@code become} (measured). So
     * the question is what each phase reachable from the arming point does with that message:
     *
     * <ul><li>one that THROWS on it kills the actor's own message — the classic armed-a-timeout-then-moved-on bug;
     * <li>one that STASHES a REPEAT is an unbounded stash with CERTAINTY rather than possibility (Phase 293's
     *     version needs the protocol to keep delivering; here the actor does it to itself — measured at 40 messages
     *     in 600ms for a 20ms period).</ul>
     *
     * <p>A phase that merely IGNORES the message is not reported: dropping a timeout that no longer applies is how
     * the idiom is written when there is no Cancellable to hand. Nothing is claimed when the become-graph is not
     * readable, when the message is not a literal, when an {@code onError} arms a timer (it can fire from any
     * phase at all), or when the method cancels anything — the repeat may then be stopped.
     */
    private static List<Finding> timerFindings(String where, BlockStatement body, Map<String, ActorDecl> actors) {
        List<Finding> out = new ArrayList<Finding>()
        for (String name : actors.keySet()) {
            List<Phase> g = becomeGraph(body, name)
            if (g == null || g.isEmpty() || g.get(0).timersUnreadable) continue
            for (int i = 0; i < g.size(); i++) {
                List<Timer> ts = new ArrayList<Timer>()
                for (Arm a : g.get(i).on.values()) if (a.timers != null) ts.addAll(a.timers)
                if (g.get(i).otherwiseTimers != null) ts.addAll(g.get(i).otherwiseTimers)
                for (Timer t : ts) {
                    if (t.msg == null || !t.discarded) continue      // kept the Cancellable: it may yet be stopped
                    for (int q : reachableFrom(g, i)) {
                        Phase r = g.get(q)
                        Arm arm = armFor(r, t.msg)
                        boolean rejects = arm != null ? arm.rejects : r.otherwise == 'rejects'
                        boolean stashes = arm != null ? arm.stash : r.otherwise == 'stash'
                        if (rejects) {
                            out.add(new Finding(Reporter.formatTimerRejected(where, name, t.msg, t.repeats, t.line, r.name), t.anchor)); break
                        }
                        if (stashes && t.repeats) {
                            out.add(new Finding(Reporter.formatTimerStashUnbounded(where, name, t.msg, t.line, r.name), t.anchor)); break
                        }
                    }
                }
            }
        }
        out
    }

    // ── Phase 298 — the actor held in a FIELD ─────────────────────────────────────────────

    /**
     * Phase 298 — the class's field initialisers, presented as the declarations they are. Every actor check so
     * far reads a METHOD body, which meant the whole gallery was silent on the shape real code is written in:
     * the actor is a field of a service class, not a local of the method that sends to it. A field
     * {@code static Actor<String> gate = Actor.reactor(h)} is exactly the declaration
     * {@code Actor<String> gate = Actor.reactor(h)}, so synthesising it lets {@code actorsIn},
     * {@code behaviourLocals} and {@code becomeGraph} read a class with no change at all.
     *
     * <p>Phase 299 — the fields ASSIGNED in the class's constructor, its initialiser block and its {@code static}
     * block are read the same way, which is what makes a CYCLIC phase graph reachable: a field initialiser cannot
     * name a field declared after it, so mutual {@code become} has to be written declare-then-assign. An
     * assignment carries no such restriction, and since the behaviours are resolved by NAME the order they appear
     * in does not matter. Only whole-statement assignments to this class's own fields are taken (an unqualified
     * name or {@code this.x}).
     *
     * <p>Phase 301 — and it is every constructor and every method, not one constructor: a class whose secondary
     * constructors chain to the one that builds the actor, or that builds it in a lifecycle {@code init()}, has a
     * single definition just as much as a class that builds it inline. Counting is what decides, in
     * {@link #dropContested}: two definitions are a disjunction (only one constructor runs per instance) or a
     * replacement (a method swapping the actor out), and no analysis of a single one of them would be sound.
     */
    static BlockStatement fieldDeclarations(ClassNode owner) {
        List<Statement> ss = new ArrayList<Statement>()
        for (FieldNode f : owner.fields) {
            Expression init = f.initialValueExpression
            if (init == null) continue
            ss.add(fieldDecl(f, init, f))
        }
        // Phase 301 — EVERY place the class gives the field a value: any constructor (however many there are), any
        // method (a lifecycle `init()`, a `static` block's `<clinit>`), and the instance initialiser. Which of them
        // is the definition is not decided here — dropContested decides, by counting: one is the definition, two
        // are a disjunction no analysis of a single one would be sound about.
        List<Statement> assigned = new ArrayList<Statement>()
        for (ConstructorNode c : (owner.declaredConstructors ?: Collections.<ConstructorNode> emptyList())) {
            if (c.code != null) assigned.addAll(bodyOf(c.code))
        }
        for (MethodNode mn : (owner.methods ?: Collections.<MethodNode> emptyList())) {
            if (mn.code != null) assigned.addAll(bodyOf(mn.code))
        }
        if (owner.objectInitializerStatements != null) for (Statement st : owner.objectInitializerStatements) assigned.addAll(bodyOf(st))
        for (Statement st : assigned) {
            if (!(st instanceof ExpressionStatement)) continue
            Expression e = ((ExpressionStatement) st).expression
            if (!(e instanceof BinaryExpression) || e instanceof DeclarationExpression) continue
            BinaryExpression be = (BinaryExpression) e
            if (be.operation.type != Types.ASSIGN) continue
            FieldNode f = assignedField(be.leftExpression, owner)
            if (f == null) continue
            ss.add(fieldDecl(f, be.rightExpression, st))
        }
        BlockStatement b = new BlockStatement(dropContested(ss), null)
        b.sourcePosition = owner
        b
    }

    /**
     * Phase 299/301 — a field given a modelled value more than once (an actor factory or a behaviour closure,
     * from an initialiser and a constructor, twice in one, from two constructors of which only one ever runs, or
     * from a method that REPLACES it later) has two definitions competing, and which of them the field ends up
     * holding is not something to decide by the order they were collected in. Both are dropped, so the field is
     * simply not found. A field initialised to something we do not model (a {@code null} placeholder, say) and
     * then assigned properly is one definition, and is kept.
     */
    private static List<Statement> dropContested(List<Statement> ss) {
        Map<String, Integer> modelled = new LinkedHashMap<String, Integer>()
        for (Statement st : ss) {
            DeclarationExpression de = (DeclarationExpression) ((ExpressionStatement) st).expression
            String n = ((VariableExpression) de.leftExpression).name
            Expression r = strip(de.rightExpression)
            if (r instanceof ClosureExpression || actorFactoryArgs(r) != null) modelled.put(n, (modelled.get(n) ?: 0) + 1)
        }
        Set<String> contested = modelled.findAll { String k, Integer v -> v > 1 }.keySet()
        if (contested.isEmpty()) return ss
        ss.findAll { Statement st ->
            !contested.contains(((VariableExpression) ((DeclarationExpression) ((ExpressionStatement) st).expression).leftExpression).name)
        }
    }

    /** The statements of a block, flattened (a static block arrives wrapped in one), else the statement itself. */
    private static List<Statement> bodyOf(Statement code) {
        if (!(code instanceof BlockStatement)) return [code]
        List<Statement> out = new ArrayList<Statement>()
        for (Statement st : ((BlockStatement) code).statements) out.addAll(bodyOf(st))
        out
    }

    /** The field of {@code owner} an assignment's left side names — {@code x} or {@code this.x} — else null. */
    private static FieldNode assignedField(Expression lhs, ClassNode owner) {
        Expression l = strip(lhs)
        if (l instanceof VariableExpression) {
            Variable av = ((VariableExpression) l).accessedVariable
            if (av instanceof FieldNode && ((FieldNode) av).owner?.name == owner.name) return (FieldNode) av
            if (av instanceof PropertyNode && ((PropertyNode) av).field?.owner?.name == owner.name) return ((PropertyNode) av).field
            return owner.getField(((VariableExpression) l).name)
        }
        if (l instanceof PropertyExpression) {
            Expression o = strip(((PropertyExpression) l).objectExpression)
            boolean own = (o instanceof VariableExpression && ((VariableExpression) o).isThisExpression()) ||
                          (o instanceof ClassExpression && o.type?.name == owner.name)
            if (own) return owner.getField(((PropertyExpression) l).propertyAsString)
        }
        null
    }

    /** One synthesised declaration: the field's name and type, bound to the expression that gives it its value. */
    private static ExpressionStatement fieldDecl(FieldNode f, Expression value, ASTNode at) {
        VariableExpression lhs = new VariableExpression(f.name, f.type)
        lhs.sourcePosition = at
        DeclarationExpression de = new DeclarationExpression(lhs, Token.newSymbol(Types.ASSIGN, at.lineNumber, at.columnNumber), value)
        de.sourcePosition = at
        ExpressionStatement es = new ExpressionStatement(de)
        es.sourcePosition = at
        es
    }

    /**
     * Phase 298 — the findings that are about the actor's BEHAVIOUR GRAPH alone, for an actor declared as a
     * field. They say nothing about any one method, so they are reported once for the class rather than once per
     * method that happens to mention it. The send-dependent checks (the bounded mailbox, the stash bound) still
     * read a method body and do not see a field-held actor yet.
     */
    static List<Finding> checkClass(ClassNode owner) {
        List<Finding> out = new ArrayList<Finding>()
        if (owner == null || owner.fields == null) return out
        BlockStatement decls = fieldDeclarations(owner)
        Map<String, ActorDecl> actors = actorsIn(decls)
        if (actors.isEmpty()) return out
        String where = "the class ${owner.nameWithoutPackage}".toString()
        out.addAll(stashFindings(where, decls, actors))
        out.addAll(timerFindings(where, decls, actors))
        out
    }

    /**
     * The check. Returns the findings; the caller reports them (so this file stays free of the STC API).
     */
    static List<Finding> check(String methodName, BlockStatement body, ClassNode owner = null) {
        List<Finding> out = new ArrayList<Finding>()
        Map<String, ActorDecl> local = actorsIn(body)
        // Phase 300 — the send-dependent checks read this METHOD's sends, but the actor they are about may be
        // declared on the class. Declarations and behaviours come from both; the program-order pass below still
        // reads the method's own statements and nothing else.
        BlockStatement scope = body
        if (owner != null) {
            List<Statement> fs = fieldDeclarations(owner).statements
            if (!fs.isEmpty()) {
                List<Statement> ss = new ArrayList<Statement>(fs); ss.addAll(body.statements)
                scope = new BlockStatement(ss, null); scope.sourcePosition = body
            }
        }
        Map<String, ActorDecl> actors = scope.is(body) ? local : actorsIn(scope)
        if (actors.isEmpty()) return out
        // the behaviour-graph findings are about the ACTOR, so a field-held one has them raised once for the
        // class (checkClass) rather than again in every method that sends to it
        out.addAll(stashFindings(methodName + '()', body, local))    // Phase 292 — needs no sends, so it comes first
        out.addAll(timerFindings(methodName + '()', body, local))    // Phase 297 — likewise
        Map<String, List<ClosureExpression>> behaviours = behaviourLocals(scope)

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
            // Phase 300 — a field-held actor OUTLIVES the call, so this method's burst is only the whole story
            // when nothing else can add to it or drain it. A count that is merely a LOWER bound would still be
            // sound for the mailbox (other senders only fill it further), but not for the stash: a sibling method
            // sending the trigger drains it, and a burst that overflows here would not there. So both are claimed
            // only for a PRIVATE field that exactly one method sends to — said out loud when a bound was asked for.
            if (!local.containsKey(d.name)) {
                String why = exclusiveSenderReason(owner, d.name, methodName)
                if (why != null) {
                    if (d.capacity >= 0 || d.stashCapacity >= 0) {
                        out.add(new Finding(Reporter.formatActorSendsNotWhole(methodName, d.name, why), mine.get(0).anchor))
                    }
                    continue
                }
            }

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
