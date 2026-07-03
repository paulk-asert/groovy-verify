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
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.Parameter
import org.codehaus.groovy.ast.expr.BinaryExpression
import org.codehaus.groovy.ast.expr.ClassExpression
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.ExpressionTransformer
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.PropertyExpression
import org.codehaus.groovy.ast.expr.TernaryExpression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.ReturnStatement
import org.codehaus.groovy.ast.stmt.Statement
import org.codehaus.groovy.syntax.Types

/**
 * Phase 209 — <b>runtime metaprogramming, statically modelled</b> (experimental). Groovy's
 * {@code ExpandoMetaClass} can add a property or an operator method to a type at runtime
 * ({@code Integer.metaClass.getFizzBuzz = { … }}, {@code Integer.metaClass.multiply = { String s -> … }});
 * such code is ordinarily <i>outside</i> the verifier's world twice over — {@code @TypeChecked} rejects the
 * unresolved references before the encoder ever sees them. This pack restores a slim, principled slice:
 *
 * <ul>
 *   <li><b>Visibility rule</b> — only registrations that are <i>statically visible in the same class</i>
 *       (a {@code <Type>.metaClass.<name> = { closure }} assignment in an initializer block or method
 *       body) are recognised. Runtime-conditional, cross-class, or category-based metaprogramming stays
 *       out (and stays a compile error under {@code @TypeChecked} — loud, not silent).</li>
 *   <li><b>The STC companion half</b> ({@link #resolveDynamicProperty}/{@link #resolveDynamicMethod}) types
 *       the registration write itself, {@code delegate}-dispatched arithmetic inside the registration
 *       closure, and the use sites ({@code n.fizzBuzz}, {@code (n % 3) * '🥤'}) — from the registered
 *       closure's own signature and body.</li>
 *   <li><b>The encoding half</b> inlines the registered closure at each use site ({@code delegate} ↦ the
 *       receiver, the closure parameter ↦ the argument) and translates the body in the String sort.
 *       A branch outside that sort (the getter's bare {@code delegate} arm) becomes a fresh
 *       <i>uninterpreted</i> value {@code meta$other$<name>(recv)} — sound over-approximation: claims
 *       about the String branches prove under branch-pruning guards; claims about the opaque branch
 *       refuse to prove.</li>
 * </ul>
 *
 * v1 scope, loud where it ends: {@code Integer} receivers; single-expression pure closure bodies
 * (nested ternaries over {@code delegate}/the parameter, String literals); one parameter at most.
 */
@CompileStatic
class MetaProgrammingPack implements EncodingPack {

    @Override
    String name() { 'metaprogramming' }

    @Override
    List<String> corpusGroups() { ['P209 metaprogramming'] }

    // ── registration scanning ─────────────────────────────────────────────────────────────────────

    /** A statically-visible registration: {@code Integer.metaClass.<name> = { closure }}. */
    @CompileStatic
    private static class Registration {
        String name              // the metaClass property assigned (e.g. 'getFizzBuzz', 'multiply')
        ClosureExpression closure
    }

    /** Scan a class for metaClass registrations on {@code Integer} (initializer blocks + method bodies). */
    private static Map<String, Registration> scan(ClassNode cn) {
        Map<String, Registration> out = new LinkedHashMap<String, Registration>()
        if (cn == null) return out
        List<Statement> roots = new ArrayList<Statement>()
        roots.addAll(cn.objectInitializerStatements ?: Collections.<Statement> emptyList())
        for (MethodNode mn : cn.methods) { if (mn.code != null) roots.add(mn.code) }
        for (Statement st : roots) collectRegs(st, out)
        out
    }

    private static void collectRegs(Statement st, Map<String, Registration> out) {
        if (st instanceof BlockStatement) {
            for (Statement s : ((BlockStatement) st).statements) collectRegs(s, out)
            return
        }
        if (!(st instanceof ExpressionStatement)) return
        Expression e = ((ExpressionStatement) st).expression
        if (!(e instanceof BinaryExpression)) return
        BinaryExpression be = (BinaryExpression) e
        if (be.operation.type != Types.ASSIGN) return
        if (!(be.rightExpression instanceof ClosureExpression)) return
        if (!(be.leftExpression instanceof PropertyExpression)) return
        PropertyExpression outer = (PropertyExpression) be.leftExpression
        if (!(outer.objectExpression instanceof PropertyExpression)) return
        PropertyExpression inner = (PropertyExpression) outer.objectExpression
        if (inner.propertyAsString != 'metaClass') return
        if (!(inner.objectExpression instanceof ClassExpression)) return
        String target = ((ClassExpression) inner.objectExpression).type.nameWithoutPackage
        if (target != 'Integer') return              // v1 scope: Integer receivers only
        Registration r = new Registration(name: outer.propertyAsString,
                                          closure: (ClosureExpression) be.rightExpression)
        out.put(r.name, r)
    }

    /** The registered closure's single result expression, or null if the body isn't that shape. */
    private static Expression closureResult(ClosureExpression ce) {
        Statement code = ce.code
        List<Statement> stmts = code instanceof BlockStatement ?
            ((BlockStatement) code).statements : Collections.<Statement> singletonList(code)
        if (stmts.size() != 1) return null
        Statement only = stmts.get(0)
        if (only instanceof ExpressionStatement) return ((ExpressionStatement) only).expression
        if (only instanceof ReturnStatement) return ((ReturnStatement) only).expression
        null
    }

    /** All value leaves of a nested-ternary expression (the non-condition positions). */
    private static void valueLeaves(Expression e, List<Expression> out) {
        if (e instanceof TernaryExpression) {
            valueLeaves(((TernaryExpression) e).trueExpression, out)
            valueLeaves(((TernaryExpression) e).falseExpression, out)
        } else {
            out.add(e)
        }
    }

    /** Substitute variable references by name ({@code delegate}, the closure param) in a copied tree. */
    private static Expression subst(Expression e, Map<String, Expression> sub) {
        ExpressionTransformer tr = null
        tr = { Expression x ->
            if (x instanceof VariableExpression) {
                Expression rep = sub.get(((VariableExpression) x).name)
                if (rep != null) return rep
            }
            return x.transformExpression(tr)
        } as ExpressionTransformer
        tr.transform(e)
    }

    private static boolean isIntegerish(ClassNode cn) {
        cn != null && (cn == ClassHelper.int_TYPE || cn.nameWithoutPackage == 'Integer')
    }

    // ── the STC companion half ────────────────────────────────────────────────────────────────────

    @Override
    ClassNode resolveDynamicProperty(ClassNode receiverType, PropertyExpression pexp, ClassNode enclosingClass) {
        if (receiverType == null) return null
        // 1. The registration write itself: `<lhs> = closure` on a groovy.lang.MetaClass receiver whose
        //    matching registration the scan found — typed as Closure.
        if (receiverType.name == 'groovy.lang.MetaClass' &&
            scan(enclosingClass).containsKey(pexp.propertyAsString)) {
            return ClassHelper.CLOSURE_TYPE
        }
        // 2. A use site: `n.fizzBuzz` with a visible `getFizzBuzz` registration. Typed honestly from the
        //    closure's value leaves: all-String → String; anything else (the bare-delegate arm) → Object.
        if (isIntegerish(receiverType)) {
            String getter = 'get' + pexp.propertyAsString.capitalize()
            Registration r = scan(enclosingClass).get(getter)
            if (r != null) {
                Expression body = closureResult(r.closure)
                if (body != null) {
                    List<Expression> leaves = new ArrayList<Expression>()
                    valueLeaves(body, leaves)
                    boolean allString = leaves.every { Expression l ->
                        l instanceof ConstantExpression && ((ConstantExpression) l).value instanceof String
                    }
                    return allString ? ClassHelper.STRING_TYPE : ClassHelper.OBJECT_TYPE
                }
            }
        }
        null
    }

    @Override
    MethodNode resolveDynamicMethod(ClassNode receiverType, String name, ClassNode[] argTypes,
                                    ClassNode enclosingClass, ClosureExpression enclosingClosure) {
        Map<String, Registration> regs = scan(enclosingClass)
        // 1. `delegate`-dispatched arithmetic INSIDE a registration closure: STC sees the delegate as
        //    java.lang.Class and fails e.g. `delegate % 15` (Class#remainder). When the enclosing closure
        //    IS a registered body, arithmetic op-methods resolve against the registration target (Integer).
        if (enclosingClosure != null && regs.values().any { Registration r -> r.closure.is(enclosingClosure) } &&
            name in ['remainder', 'mod', 'plus', 'minus', 'multiply', 'div', 'intdiv'] &&
            argTypes != null && argTypes.length == 1) {
            return new MethodNode(name, 1, ClassHelper.int_TYPE,
                [new Parameter(ClassHelper.int_TYPE, 'x')] as Parameter[], null, null)
        }
        // 2. A use site: `(n % 3) * '🥤'` — an operator method registered on Integer with a matching
        //    single parameter type. Return type from the closure's value leaves (all-String → String).
        if (isIntegerish(receiverType) && argTypes != null && argTypes.length == 1) {
            Registration r = regs.get(name)
            if (r != null && r.closure.parameters != null && r.closure.parameters.length == 1 &&
                r.closure.parameters[0].type.nameWithoutPackage == argTypes[0].nameWithoutPackage) {
                Expression body = closureResult(r.closure)
                if (body != null) {
                    List<Expression> leaves = new ArrayList<Expression>()
                    valueLeaves(body, leaves)
                    boolean allString = leaves.every { Expression l ->
                        (l instanceof ConstantExpression && ((ConstantExpression) l).value instanceof String) ||
                        (l instanceof VariableExpression && ((VariableExpression) l).name == r.closure.parameters[0].name)
                    }
                    ClassNode ret = allString ? ClassHelper.STRING_TYPE : ClassHelper.OBJECT_TYPE
                    return new MethodNode(name, 1, ret,
                        [new Parameter(argTypes[0], 'x')] as Parameter[], null, null)
                }
            }
        }
        null
    }

    // ── the encoding half ─────────────────────────────────────────────────────────────────────────

    /** Inline a registered closure body in the String sort; unencodable value leaves become the opaque
     *  {@code meta$other$<name>(recv)} — a sound uninterpreted stand-in. */
    private static Object encodeBody(TheoryApi api, String regName, Expression body, Object recvH) {
        Object strSort = api.session.declareSort('String')
        encodeInSort(api, regName, body, recvH, strSort)
    }

    private static Object encodeInSort(TheoryApi api, String regName, Expression e, Object recvH, Object strSort) {
        if (e instanceof TernaryExpression) {
            TernaryExpression te = (TernaryExpression) e
            Object c = api.translate(te.booleanExpression)
            if (c == null) return null
            Object tv = encodeInSort(api, regName, te.trueExpression, recvH, strSort)
            Object fv = encodeInSort(api, regName, te.falseExpression, recvH, strSort)
            if (tv == null || fv == null) return null
            return api.session.ite(c, tv, fv)
        }
        // In-sort leaves are whitelisted: only expressions that are String-VALUED belong in the String
        // sort. (translateInSort on an Int-bound variable returns its existing Int handle, not null —
        // the getter's bare `delegate` arm would otherwise poison the ite with a sort clash.)
        boolean stringish = (e instanceof ConstantExpression && ((ConstantExpression) e).value instanceof String)
        if (stringish) {
            Object h = api.translateInSort(e, strSort)
            if (h != null) return h
        }
        // The out-of-sort arm (the getter's bare `delegate`): a per-receiver opaque String value.
        api.session.applyUF('meta$other$' + regName, [recvH], strSort)
    }

    @Override
    Object translateCall(TheoryApi api, MethodCallExpression mce,
                         String m, Expression recv, List<Expression> args) {
        TheoryApi.NO_MATCH   // this pack recognises properties and operators, not named calls
    }

    @Override
    Object translateProperty(TheoryApi api, PropertyExpression pexp, Expression obj, String prop) {
        MethodNode m = api.currentMethod()
        if (m == null) return TheoryApi.NO_MATCH
        String getter = 'get' + prop.capitalize()
        Registration r = scan(m.declaringClass).get(getter)
        if (r == null) return TheoryApi.NO_MATCH
        Object recvH = api.translate(obj)
        if (recvH == null) return null
        Expression body = closureResult(r.closure)
        if (body == null) return null
        Expression inlined = subst(body, ['delegate': obj] as Map<String, Expression>)
        encodeBody(api, r.name, inlined, recvH)
    }

    @Override
    Object translateBinary(TheoryApi api, BinaryExpression be, int op) {
        if (op != Types.MULTIPLY) return TheoryApi.NO_MATCH
        MethodNode m = api.currentMethod()
        if (m == null) return TheoryApi.NO_MATCH
        Registration r = scan(m.declaringClass).get('multiply')
        if (r == null || r.closure.parameters == null || r.closure.parameters.length != 1) return TheoryApi.NO_MATCH
        // Only when the right operand is String-shaped (the registered signature) — ordinary int*int
        // multiplication must fall through to the core untouched.
        if (!(be.rightExpression instanceof ConstantExpression &&
              ((ConstantExpression) be.rightExpression).value instanceof String)) return TheoryApi.NO_MATCH
        Object recvH = api.translate(be.leftExpression)
        if (recvH == null) return null
        Expression body = closureResult(r.closure)
        if (body == null) return null
        Expression inlined = subst(body, ['delegate'                    : be.leftExpression,
                                          (r.closure.parameters[0].name): be.rightExpression] as Map<String, Expression>)
        encodeBody(api, r.name, inlined, recvH)
    }
}
