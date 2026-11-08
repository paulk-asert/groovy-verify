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
import org.codehaus.groovy.ast.ClassHelper
import org.codehaus.groovy.ast.ClassNode
import org.codehaus.groovy.ast.ConstructorNode
import org.codehaus.groovy.ast.CodeVisitorSupport
import org.codehaus.groovy.ast.FieldNode
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.Parameter
import org.codehaus.groovy.ast.expr.ClassExpression
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.expr.ConstructorCallExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.MethodPointerExpression
import org.codehaus.groovy.ast.expr.StaticMethodCallExpression
import org.codehaus.groovy.ast.expr.TupleExpression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.transform.stc.StaticTypesMarker

/**
 * Phase 538 — the Apache Pekko typed-actor pack, slice 1: what a typed handler's own body needs to stay inside the
 * fragment. Every fact here was measured on Pekko 2.0.0 ({@code PekkoSemanticsTest}) before it was modelled; Pekko is
 * matched by name, never compiled against, so the pack costs a non-Pekko build nothing.
 *
 * <ul>
 *   <li>A returned behaviour — {@code Behaviors.same()}, {@code stopped()}, {@code empty()}, {@code unhandled()},
 *       {@code ignore()}, or a receive built by {@code newReceiveBuilder()…build()} — is a value the pack claims: the
 *       method's {@code result} is an opaque non-null handle, so a postcondition about the actor's state is checked
 *       and one about the behaviour itself can't be proved. Building a receive runs no handler: its arguments are a
 *       message class and a method reference or closure, captured, not called.</li>
 *   <li>{@code ActorRef.tell} changes nothing the sender reads: it queues the message (a tell to self is handled after
 *       the current handler returns, never inside it), and a null message throws {@code InvalidMessageException} at
 *       the call. That is a pack-shipped skeleton ({@code specFqns}), trusted and ledgered.</li>
 *   <li>{@code super(context)} in an {@code AbstractBehavior} subclass's constructor runs no subclass code (the receive
 *       is built on the first message, measured) and writes none of the subclass's fields: a statement with no
 *       effect.</li>
 *   <li>Phase 539 — a handler's message is never {@code null}: {@code tell(null)} throws at the sender and an
 *       {@code ask} whose message is null fails before delivery, so the runtime never hands a handler null. The pack
 *       answers only for a method nothing else can call — private, one reference parameter, one method of that name,
 *       and named in this source only as {@code this::name} inside an {@code onMessage}/{@code onAnyMessage}/
 *       {@code onSignal} step of a receive builder in its own class (a direct call, or any other reference, and the
 *       message is possibly null again, a caller's {@code @Requires} to state).</li>
 *   <li>Phase 540 — after a handler returns {@code Behaviors.stopped()} no message is delivered to the behaviour
 *       again, so the class invariant is not owed on that exit (the invariant is the property of the actor's live
 *       states). Measured too: an {@code onSignal(PostStop)} handler still runs once, after, on that state — so a
 *       class with any {@code onSignal} step gets no release. Nor does a class whose state anything else could
 *       observe: a Groovy property (a public getter), an instance method other than the private ones and
 *       {@code createReceive()}, or a parameter or field of its type anywhere in the source (a parameter's class
 *       invariant is assumed).</li>
 *   <li>Phase 541 — a registered handler whose message carries an {@code ActorRef} named {@code replyTo} owes a reply
 *       on every normal exit: an {@code ask} nobody answers fails at its timeout (measured). Telling it, or a local
 *       holding it, meets it; so does handing it on (an argument of a call or constructor, a field it is kept in),
 *       measured to complete the ask when whoever gets it replies. A second reply is dropped harmlessly (measured).
 *       A closure is never looked into: it may not run.</li>
 *   <li>Phase 545 — the functional style: a closure literal handed to {@code Behaviors.setup}, {@code receiveMessage},
 *       {@code receive}, {@code receiveSignal}, or to an {@code onMessage} (its predicate too) / {@code onAnyMessage} /
 *       {@code onSignal} step of a {@code BehaviorBuilder} or {@code ReceiveBuilder}, is called only by the runtime,
 *       and measured never to be handed {@code null}: its reference parameters (or its implicit {@code it}) are
 *       non-null where it runs ({@code nonNullClosureParams}), unless it assigns one.</li>
 *   <li>Phase 546 — the guardian side: in a constructor of a direct {@code AbstractBehavior} subclass that begins
 *       {@code super(context)}, {@code context} is non-null after it, since {@code AbstractBehavior} throws
 *       {@code IllegalArgumentException} on null (measured); and {@code ActorSystem.create(guardian, name)} returns a
 *       system, never null (a shipped skeleton, held against the runtime by {@code SpecAuditTest}).</li>
 * </ul>
 */
@CompileStatic
class PekkoPack implements EncodingPack {

    static final String JAVADSL = 'org.apache.pekko.actor.typed.javadsl.'
    static final String ABSTRACT_BEHAVIOR = JAVADSL + 'AbstractBehavior'
    static final String BEHAVIORS = JAVADSL + 'Behaviors'
    static final String RECEIVE_BUILDER = JAVADSL + 'ReceiveBuilder'

    /** The argument-free {@code Behaviors} factories: each returns a fixed behaviour marker. */
    static final Set<String> BEHAVIOR_MARKERS = ['same', 'stopped', 'empty', 'unhandled', 'ignore'] as Set<String>

    /** The receive-builder steps that register a handler: a message class (or value) and a handler, captured. */
    static final Set<String> BUILDER_STEPS = ['onMessage', 'onMessageEquals', 'onAnyMessage', 'onSignal',
        'onSignalEquals'] as Set<String>

    /** The builder steps whose method-reference arguments the runtime calls with a delivered message or signal. */
    static final Set<String> DELIVERING_STEPS = ['onMessage', 'onAnyMessage', 'onSignal'] as Set<String>

    static final String ACTOR_REF = 'org.apache.pekko.actor.typed.ActorRef'
    static final String REPLY_TO = 'replyTo'
    static final String POST_STOP = 'org.apache.pekko.actor.typed.PostStop'

    private static final String HANDLER_KEY = 'verification.PekkoPack.handler'
    private static final String UNOBSERVED_KEY = 'verification.PekkoPack.unobservedAfterStop'

    @Override
    String name() { 'pekko' }

    @Override
    List<String> corpusGroups() { ['P538 Pekko pack', 'P539 Pekko handler message', 'P540 Pekko stopped', 'P541 Pekko reply', 'P542 Pekko PostStop', 'P545 Pekko functional', 'P546 Pekko guardian'] }

    @Override
    List<String> specFqns() { ['org.apache.pekko.actor.typed.ActorRef', 'org.apache.pekko.actor.typed.ActorSystem'] }

    @Override
    Object translateCall(TheoryApi api, MethodCallExpression mce, String m, Expression recv, List<Expression> args) {
        TheoryApi.NO_MATCH
    }

    @Override
    boolean claimsValueSource(TheoryApi api, Expression e) { isBehaviorValue(e) }

    @Override
    boolean claimsNoEffect(Expression e) { isAbstractBehaviorSuperCall(e) }

    @Override
    List<String> nonNullOnEntry(MethodNode m) {
        if (isRegisteredHandler(m)) return [m.parameters[0].name]
        String c = contextPassedToSuper(m)
        c != null ? [c] : Collections.<String> emptyList()
    }

    @Override
    String nonNullOnEntryReason(MethodNode m, String n) {
        n == contextPassedToSuper(m) ? "${n} is non-null past super(${n}): AbstractBehavior's constructor throws on null".toString() : null
    }

    /** Phase 546 — the parameter a constructor of a direct AbstractBehavior subclass passes as its first statement,
     *  {@code super(context)}: AbstractBehavior throws IllegalArgumentException on a null context (measured), so no
     *  statement after it runs with the parameter null. Null when the constructor doesn't begin so. */
    static String contextPassedToSuper(MethodNode m) {
        if (!(m instanceof ConstructorNode)) return null
        org.codehaus.groovy.ast.stmt.Statement code = m.code
        if (code instanceof org.codehaus.groovy.ast.stmt.BlockStatement) {
            List<org.codehaus.groovy.ast.stmt.Statement> ss = ((org.codehaus.groovy.ast.stmt.BlockStatement) code).statements
            code = ss.isEmpty() ? null : ss.get(0)
        }
        if (!(code instanceof org.codehaus.groovy.ast.stmt.ExpressionStatement)) return null
        Expression e = ((org.codehaus.groovy.ast.stmt.ExpressionStatement) code).expression
        if (!isAbstractBehaviorSuperCall(e)) return null
        Expression a = ((ConstructorCallExpression) e).arguments
        String name = ((VariableExpression) (a instanceof TupleExpression ? ((TupleExpression) a).expressions.get(0) : a)).name
        m.parameters.any { it.name == name } ? name : null
    }

    /** Phase 545 — the functional style: {@code Behaviors.setup}'s context, {@code receiveMessage}'s message,
     *  {@code receive}'s and {@code receiveSignal}'s context and message or signal, and the message or signal of a
     *  {@code BehaviorBuilder} / {@code ReceiveBuilder} step's handler and predicate. Measured: never null. */
    @Override
    List<String> nonNullClosureParams(Expression call, int at, ClosureExpression ce) {
        if (!isFunctionalHandlerCall(call)) return Collections.<String> emptyList()
        Parameter[] ps = ce.parameters
        if (ps == null || ps.length == 0) return ce.isParameterSpecified() ? Collections.<String> emptyList() : ['it']
        List<String> out = new ArrayList<String>()
        for (Parameter p : ps) if (!ClassHelper.isPrimitiveType(p.type)) out.add(p.name)
        out
    }

    static final Set<String> FUNCTIONAL_FACTORIES = ['setup', 'receiveMessage', 'receive', 'receiveSignal'] as Set<String>
    static final String BEHAVIOR_BUILDER = JAVADSL + 'BehaviorBuilder'

    /** A call of one of {@link #FUNCTIONAL_FACTORIES} on {@code Behaviors}, or a delivering step of a behaviour or
     *  receive builder: every closure it is handed runs only as the runtime calls it. */
    static boolean isFunctionalHandlerCall(Expression call) {
        if (call instanceof StaticMethodCallExpression) {
            StaticMethodCallExpression s = (StaticMethodCallExpression) call
            return s.ownerType?.name == BEHAVIORS && s.method in FUNCTIONAL_FACTORIES
        }
        if (!(call instanceof MethodCallExpression)) return false
        MethodCallExpression c = (MethodCallExpression) call
        String m = c.methodAsString
        (m in FUNCTIONAL_FACTORIES && declaredBy(c, BEHAVIORS)) ||
            (m in DELIVERING_STEPS && (declaredBy(c, BEHAVIOR_BUILDER) || declaredBy(c, RECEIVE_BUILDER)))
    }

    @Override
    boolean releasesInvariantAt(MethodNode m, Expression returned) {
        isStoppedMarker(returned) && isRegisteredHandler(m) && unobservedAfterStop(m.declaringClass)
    }

    @Override
    boolean runsOutsideInvariant(MethodNode m) { isPostStopHandler(m) && unobservedAfterStop(m.declaringClass) }

    /** A registered handler whose parameter is {@code PostStop}: only the runtime calls it, with that signal. */
    static boolean isPostStopHandler(MethodNode m) {
        m != null && m.parameters.length == 1 && m.parameters[0].type?.name == POST_STOP && isRegisteredHandler(m)
    }

    @Override
    String exitObligation(MethodNode m) {
        if (m == null || m.parameters.length != 1 || !hasReplyTo(m.parameters[0].type) || !isRegisteredHandler(m)) return null
        "a reply on ${m.parameters[0].name}.${REPLY_TO}".toString()
    }

    @Override
    boolean meetsExitObligation(MethodNode m, List<Object> steps, Expression returned) {
        Set<String> aliases = new HashSet<String>()
        String msg = m.parameters[0].name
        for (Object step : steps) {
            if (step instanceof Assign) {
                Assign a = (Assign) step
                boolean ref = isReplyRef(a.rhs, msg, aliases)
                if (ref && m.declaringClass.getField(a.name) != null) return true   // kept in a field: handed on
                if (!ref && repliesOrHandsOn(a.rhs, msg, aliases)) return true
                if (ref) aliases.add(a.name) else aliases.remove(a.name)
            } else if (step instanceof LemmaCall) {
                if (repliesOrHandsOn(((LemmaCall) step).call, msg, aliases)) return true
            }   // a store of a reference through another object is outside the fragment (the method skips)
        }
        returned != null && repliesOrHandsOn(returned, msg, aliases)
    }

    /** The message type declares an {@code ActorRef} named {@code replyTo} (field, property or record component). */
    static boolean hasReplyTo(ClassNode t) {
        if (t == null) return false
        FieldNode f = t.getField(REPLY_TO)
        if (f != null) return f.type?.name == ACTOR_REF
        org.codehaus.groovy.ast.PropertyNode pn = t.getProperty(REPLY_TO)
        pn != null && pn.type?.name == ACTOR_REF
    }

    /** {@code msg.replyTo}, {@code msg.getReplyTo()}, {@code msg.replyTo()} (a record), or a local holding it. */
    static boolean isReplyRef(Expression e, String msg, Set<String> aliases) {
        if (e instanceof VariableExpression) return ((VariableExpression) e).name in aliases
        if (e instanceof org.codehaus.groovy.ast.expr.PropertyExpression) {
            org.codehaus.groovy.ast.expr.PropertyExpression pe = (org.codehaus.groovy.ast.expr.PropertyExpression) e
            return isNamed(pe.objectExpression, msg) && pe.propertyAsString == REPLY_TO
        }
        if (e instanceof MethodCallExpression) {
            MethodCallExpression c = (MethodCallExpression) e
            return isNamed(c.objectExpression, msg) && c.methodAsString in [REPLY_TO, 'getReplyTo'] && noArgs(c.arguments)
        }
        false
    }

    private static boolean isNamed(Expression e, String name) {
        e instanceof VariableExpression && ((VariableExpression) e).name == name
    }

    /** {@code e} tells the reply ref, or passes it on as an argument of a call or a constructor. A closure is not
     *  looked into: it may never run ({@code xs.each { … }} over an empty list). */
    static boolean repliesOrHandsOn(Expression e, String msg, Set<String> aliases) {
        ReplySeen v = new ReplySeen(msg, aliases)
        e.visit(v)
        v.seen
    }

    private static class ReplySeen extends CodeVisitorSupport {
        final String msg
        final Set<String> aliases
        boolean seen

        ReplySeen(String msg, Set<String> aliases) { this.msg = msg; this.aliases = aliases }

        private void args(Expression a) {
            List<Expression> as = a instanceof TupleExpression ? ((TupleExpression) a).expressions : [a]
            for (Expression x : as) if (isReplyRef(x, msg, aliases)) seen = true
        }

        @Override
        void visitMethodCallExpression(MethodCallExpression c) {
            if (c.methodAsString == 'tell' && isReplyRef(c.objectExpression, msg, aliases)) seen = true
            args(c.arguments)
            super.visitMethodCallExpression(c)
        }

        @Override
        void visitStaticMethodCallExpression(StaticMethodCallExpression c) {
            args(c.arguments)
            super.visitStaticMethodCallExpression(c)
        }

        @Override
        void visitConstructorCallExpression(ConstructorCallExpression c) {
            args(c.arguments)
            super.visitConstructorCallExpression(c)
        }

        @Override
        void visitClosureExpression(ClosureExpression c) { }   // not run here
    }

    /** {@code Behaviors.stopped()}, argument-free (the overload taking a post-stop callback runs code after). */
    static boolean isStoppedMarker(Expression e) {
        if (e instanceof StaticMethodCallExpression) {
            StaticMethodCallExpression s = (StaticMethodCallExpression) e
            return s.ownerType?.name == BEHAVIORS && s.method == 'stopped' && noArgs(s.arguments)
        }
        if (!(e instanceof MethodCallExpression)) return false
        MethodCallExpression c = (MethodCallExpression) e
        c.objectExpression instanceof ClassExpression && ((ClassExpression) c.objectExpression).type?.name == BEHAVIORS &&
            c.methodAsString == 'stopped' && noArgs(c.arguments)
    }

    /** Nothing but the runtime reaches a stopped behaviour's state: no property, no non-private instance method but
     *  {@code createReceive()}, no {@code onSignal} step (PostStop runs after), no parameter or field of its type. */
    static boolean unobservedAfterStop(ClassNode dc) {
        Object cached = dc.getNodeMetaData(UNOBSERVED_KEY)
        if (cached instanceof Boolean) return (Boolean) cached
        boolean r = computeUnobserved(dc)
        dc.putNodeMetaData(UNOBSERVED_KEY, r)
        r
    }

    private static boolean computeUnobserved(ClassNode dc) {
        if (!dc.properties.isEmpty()) return false
        for (MethodNode mn : dc.methods) {
            if (mn.isSynthetic() || mn.isPrivate() || mn.isStatic()) continue
            if (mn.name == 'createReceive' && mn.parameters.length == 0) continue
            return false
        }
        SignalSteps signals = new SignalSteps(dc)
        for (MethodNode mn : dc.methods) mn.code?.visit(signals)
        for (MethodNode mn : dc.declaredConstructors) mn.code?.visit(signals)
        if (signals.found) return false
        List<ClassNode> classes = dc.module != null ? dc.module.classes : [dc]
        for (ClassNode c : classes) {
            for (FieldNode f : c.fields) if (f.type?.name == dc.name) return false
            List<MethodNode> all = new ArrayList<MethodNode>(c.methods)
            all.addAll(c.declaredConstructors)
            for (MethodNode mn : all) {
                for (org.codehaus.groovy.ast.Parameter p : mn.parameters) if (p.type?.name == dc.name) return false
            }
        }
        true
    }

    /** A signal step, but {@code onSignal(PostStop, this::h)} for a PostStop handler (Phase 542: it runs outside the
     *  invariant, so the state it sees after {@code stopped()} owes nothing). */
    private static class SignalSteps extends CodeVisitorSupport {
        final ClassNode dc
        boolean found
        SignalSteps(ClassNode dc) { this.dc = dc }
        @Override
        void visitMethodCallExpression(MethodCallExpression c) {
            if (c.methodAsString in ['onSignal', 'onSignalEquals'] && !postStopStep(c)) found = true
            super.visitMethodCallExpression(c)
        }
        private boolean postStopStep(MethodCallExpression c) {
            if (c.methodAsString != 'onSignal' || !declaredBy(c, RECEIVE_BUILDER)) return false
            List<Expression> as = ((TupleExpression) c.arguments).expressions
            if (as.size() != 2 || !(as[0] instanceof ClassExpression) || ((ClassExpression) as[0]).type?.name != POST_STOP) return false
            if (!(as[1] instanceof MethodPointerExpression)) return false
            MethodPointerExpression p = (MethodPointerExpression) as[1]
            String name = p.methodName?.text
            List<MethodNode> ms = name != null ? dc.getMethods(name) : Collections.<MethodNode> emptyList()
            isThisPointerTo(p, name) && ms.size() == 1 && isPostStopHandler(ms[0])
        }
    }

    /** A private one-parameter method of an AbstractBehavior subclass, referenced only as a receive-builder handler. */
    static boolean isRegisteredHandler(MethodNode m) {
        if (m == null || !m.isPrivate() || m.isStatic() || m.parameters.length != 1) return false
        if (ClassHelper.isPrimitiveType(m.parameters[0].type)) return false
        ClassNode dc = m.declaringClass
        if (dc == null || !extendsAbstractBehavior(dc) || dc.getMethods(m.name).size() != 1) return false
        Object cached = m.getNodeMetaData(HANDLER_KEY)
        if (cached instanceof Boolean) return (Boolean) cached
        boolean r = onlyRegistered(m.name, dc)
        m.putNodeMetaData(HANDLER_KEY, r)
        r
    }

    private static boolean extendsAbstractBehavior(ClassNode c) {
        for (ClassNode k = c.superClass; k != null; k = k.superClass) if (k.name == ABSTRACT_BEHAVIOR) return true
        false
    }

    /** Every reference to {@code name} in the module is {@code this::name} in a delivering step in {@code owner}, and
     *  there is at least one; a call by that name, a dynamic method name, or any other pointer to it and the answer is no. */
    private static boolean onlyRegistered(String name, ClassNode owner) {
        List<ClassNode> classes = owner.module != null ? owner.module.classes : [owner]
        HandlerRefs refs = new HandlerRefs(name)
        for (ClassNode c : classes) {
            refs.inOwner = c.is(owner)
            for (MethodNode mn : c.methods) mn.code?.visit(refs)
            for (MethodNode mn : c.declaredConstructors) mn.code?.visit(refs)
            for (FieldNode f : c.fields) f.initialExpression?.visit(refs)
            for (org.codehaus.groovy.ast.stmt.Statement st : c.objectInitializerStatements) st.visit(refs)
        }
        !refs.other && refs.registered > 0
    }

    private static class HandlerRefs extends CodeVisitorSupport {
        final String name
        boolean inOwner
        boolean other
        int registered
        private final Set<MethodPointerExpression> sanctioned = Collections.newSetFromMap(new IdentityHashMap<MethodPointerExpression, Boolean>())

        HandlerRefs(String name) { this.name = name }

        @Override
        void visitMethodCallExpression(MethodCallExpression c) {
            String m = c.methodAsString
            if (m == null || m == name || m == 'invokeMethod') other = true
            if (inOwner && m in DELIVERING_STEPS && declaredBy(c, RECEIVE_BUILDER)) {
                for (Expression a : ((TupleExpression) c.arguments).expressions) {
                    if (a instanceof MethodPointerExpression && isThisPointerTo((MethodPointerExpression) a, name)) {
                        sanctioned.add((MethodPointerExpression) a)
                    }
                }
            }
            super.visitMethodCallExpression(c)
        }

        @Override
        void visitStaticMethodCallExpression(StaticMethodCallExpression c) {
            if (c.method == name) other = true
            super.visitStaticMethodCallExpression(c)
        }

        @Override
        void visitMethodPointerExpression(MethodPointerExpression p) {
            if (!(p.methodName instanceof org.codehaus.groovy.ast.expr.ConstantExpression) || p.methodName.text == name) {
                if (sanctioned.contains(p)) registered++ else other = true
            }
            super.visitMethodPointerExpression(p)
        }
    }

    private static boolean isThisPointerTo(MethodPointerExpression p, String name) {
        p.methodName?.text == name && p.expression instanceof VariableExpression &&
            ((VariableExpression) p.expression).isThisExpression()
    }

    /** A behaviour marker ({@code Behaviors.same()}) or a built receive. */
    static boolean isBehaviorValue(Expression e) {
        if (e instanceof StaticMethodCallExpression) {
            StaticMethodCallExpression s = (StaticMethodCallExpression) e
            return s.ownerType?.name == BEHAVIORS && s.method in BEHAVIOR_MARKERS && noArgs(s.arguments)
        }
        if (!(e instanceof MethodCallExpression)) return false
        MethodCallExpression c = (MethodCallExpression) e
        if (c.objectExpression instanceof ClassExpression) {
            return ((ClassExpression) c.objectExpression).type?.name == BEHAVIORS &&
                c.methodAsString in BEHAVIOR_MARKERS && noArgs(c.arguments)
        }
        c.methodAsString == 'build' && noArgs(c.arguments) && isBuilderChain(c.objectExpression)
    }

    /** {@code newReceiveBuilder()} of an AbstractBehavior, then registration steps whose arguments are captured. */
    private static boolean isBuilderChain(Expression e) {
        if (!(e instanceof MethodCallExpression)) return false
        MethodCallExpression c = (MethodCallExpression) e
        if (c.methodAsString == 'newReceiveBuilder' && noArgs(c.arguments)) {
            return declaredBy(c, ABSTRACT_BEHAVIOR)
        }
        if (!(c.methodAsString in BUILDER_STEPS) || !declaredBy(c, RECEIVE_BUILDER)) return false
        for (Expression a : ((TupleExpression) c.arguments).expressions) {
            if (!(a instanceof ClassExpression || a instanceof MethodPointerExpression || a instanceof ClosureExpression)) {
                return false
            }
        }
        isBuilderChain(c.objectExpression)
    }

    /** {@code super(context)} in a direct subclass of AbstractBehavior, its argument a name. */
    static boolean isAbstractBehaviorSuperCall(Expression e) {
        if (!(e instanceof ConstructorCallExpression) || !((ConstructorCallExpression) e).isSuperCall()) return false
        ConstructorCallExpression cc = (ConstructorCallExpression) e
        Object target = cc.getNodeMetaData(StaticTypesMarker.DIRECT_METHOD_CALL_TARGET)
        ClassNode owner = target instanceof MethodNode ? ((MethodNode) target).declaringClass : null
        if (owner?.name != ABSTRACT_BEHAVIOR) return false
        Expression a = cc.arguments
        List<Expression> args = a instanceof TupleExpression ? ((TupleExpression) a).expressions : [a]
        args.size() == 1 && args.get(0) instanceof org.codehaus.groovy.ast.expr.VariableExpression
    }

    private static boolean declaredBy(MethodCallExpression c, String fqn) {
        Object t = c.getNodeMetaData(StaticTypesMarker.DIRECT_METHOD_CALL_TARGET)
        t instanceof MethodNode && ((MethodNode) t).declaringClass?.name == fqn
    }

    private static boolean noArgs(Expression a) {
        a instanceof TupleExpression && ((TupleExpression) a).expressions.isEmpty()
    }
}
