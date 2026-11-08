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
import org.codehaus.groovy.ast.ClassNode
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.expr.ClassExpression
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.expr.ConstructorCallExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.MethodPointerExpression
import org.codehaus.groovy.ast.expr.StaticMethodCallExpression
import org.codehaus.groovy.ast.expr.TupleExpression
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

    @Override
    String name() { 'pekko' }

    @Override
    List<String> corpusGroups() { ['P538 Pekko pack'] }

    @Override
    List<String> specFqns() { ['org.apache.pekko.actor.typed.ActorRef'] }

    @Override
    Object translateCall(TheoryApi api, MethodCallExpression mce, String m, Expression recv, List<Expression> args) {
        TheoryApi.NO_MATCH
    }

    @Override
    boolean claimsValueSource(TheoryApi api, Expression e) { isBehaviorValue(e) }

    @Override
    boolean claimsNoEffect(Expression e) { isAbstractBehaviorSuperCall(e) }

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
