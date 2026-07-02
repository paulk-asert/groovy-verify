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
import org.codehaus.groovy.ast.GenericsType
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.Parameter
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.ExpressionTransformer
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.PropertyExpression
import org.codehaus.groovy.ast.expr.TupleExpression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.ReturnStatement
import org.codehaus.groovy.ast.stmt.Statement

/**
 * Canonicalises a freshly <b>re-parsed</b> contract expression against the owning method's signature,
 * before the encoder ever sees it.
 *
 * <p>Contract text is re-parsed at {@code CompilePhase.CONVERSION} (see {@code ContractExpansionTransform}
 * / {@code VerifyChecker.parseContract}), which is <i>pre-resolution</i> — so spellings that Groovy's later
 * resolution phases would rewrite arrive in their raw parse shape. Historically each such shape grew its
 * own special case at the point it was discovered (unresolved enum constants, {@code new Res(a)} carrier
 * recovery, {@code values().length} folding, the Phase-177 SAM shorthand — each found by a user-visible
 * failure). This pass is the <b>one home</b> for the rewrites among them: shapes that have a canonical
 * equivalent are normalised here, so the encoder deals in one spelling. (Pure <i>resolution</i> concerns —
 * enum-constant and carrier-type recovery, which need translate-time scope rather than a rewrite — stay
 * with the encoder.)
 *
 * <p>Current rewrites:
 * <ul>
 *   <li><b>SAM call-operator shorthand</b> (Phase 177/181): {@code f(x)} where {@code f} is a
 *   {@code java.util.function.Function}-typed formal parses as an implicit-{@code this} call
 *   {@code this.f(x)}; resolution would have made it {@code f.call(x)} → the SAM {@code apply}. Rewritten
 *   to {@code f.apply(x)}, the encoder's canonical higher-order shape — including inside closure bodies
 *   ({@code (n..<u).every { csF(i + 1) == csF(i) }}), which a plain {@link ExpressionTransformer} does not
 *   descend into.</li>
 *   <li><b>{@code <EnumClass>.values().length} / {@code .size()} fold</b> (Phase 28/183): in a re-parsed
 *   contract the receiver is an unresolved {@code VariableExpression("Color")}; when the name resolves to
 *   an enum visible from the context class's module, the whole count expression folds to the literal
 *   constant count. (<i>Body</i> expressions keep the encoder's translate-time fold — both receiver
 *   shapes, since the clean-body snapshot is captured at CONVERSION and can carry the unresolved
 *   spelling too; bodies are not contracts, so they are outside this pass's charter.)</li>
 * </ul>
 *
 * <p>Safe to rewrite in place / by copy: the input is a per-call fresh parse (never the shared clean-body
 * snapshot, which is shallow-shared across consumers and must not be restructured — bodies are resolved
 * ASTs anyway, where the shorthand arrives as {@code f.call(x)} and is recognised by the encoder directly).
 */
@CompileStatic
class ContractNormalizer {

    /** Normalise a freshly re-parsed contract expression of method {@code m}; returns {@code e} (possibly
     *  rebuilt). Null-safe on both arguments. */
    static Expression normalize(Expression e, MethodNode m) {
        if (e == null || m == null) return e
        normalize(e, functionFormalNames(m), enumDomainSizes(m.declaringClass))
    }

    /** Normalise a freshly re-parsed <b>class-level</b> contract (a class {@code @Invariant}) of
     *  {@code context}: no method scope, so only the class-scope rewrites (the enum-count fold) apply. */
    static Expression normalize(Expression e, ClassNode context) {
        if (e == null || context == null) return e
        normalize(e, Collections.<String> emptySet(), enumDomainSizes(context))
    }

    private static Expression normalize(Expression e, Set<String> fns, Map<String, Integer> enums) {
        if (fns.isEmpty() && enums.isEmpty()) return e
        new SamRewriter(fns, enums).transform(e)
    }

    /** Enum classes visible from {@code context}'s module, mapped from simple name (and
     *  inner-class-stripped name) to constant count — the scope of the {@code values().length} fold.
     *  Also feeds the checker's {@code enumDomainSizes} scope collection (domain-closure axioms). */
    static Map<String, Integer> enumDomainSizes(ClassNode context) {
        Map<String, Integer> out = new LinkedHashMap<String, Integer>()
        if (context == null || context.module == null) return out
        for (ClassNode cn : context.module.classes) {
            if (!cn.isEnum()) continue
            int count = countEnumConstants(cn)
            if (count <= 0) continue
            out.put(cn.nameWithoutPackage, count)
            String simple = simpleEnumName(cn)   // strips C$ from C$Color → Color (nested-class case)
            if (simple != cn.nameWithoutPackage) out.put(simple, count)
        }
        out
    }

    /** Count actual enum constants — fields with the JVM {@code ACC_ENUM} modifier bit — filtering the
     *  synthetic same-type fields Groovy adds ({@code MIN_VALUE}/{@code MAX_VALUE}) and {@code $VALUES}. */
    static int countEnumConstants(ClassNode t) {
        int count = 0
        for (org.codehaus.groovy.ast.FieldNode f : t.fields) {
            if ((f.modifiers & 0x4000) != 0) count++   // 0x4000 = ACC_ENUM
        }
        count
    }

    /** The user-facing simple name of an enum type: the last {@code $}-segment of a nested name
     *  ({@code C$Color} → {@code Color}), else the plain name without package. */
    static String simpleEnumName(ClassNode t) {
        String n = t.nameWithoutPackage
        int dollar = n.lastIndexOf('$')
        dollar >= 0 ? n.substring(dollar + 1) : n
    }

    /** Names of {@code java.util.function.Function}-typed formals (raw or generic) — the rewrite scope.
     *  Accepts the plain {@code Function} spelling too: the loop-contract capture normalises at
     *  {@code CompilePhase.CONVERSION} (inside {@code ContractExpansionTransform}), where the parameter's
     *  {@code ClassNode} is still <i>unresolved</i> and carries only the source name. (A same-named user
     *  type would match too — but the rewrite additionally requires an implicit-{@code this} call spelled
     *  with the parameter's own name, so a false positive needs a method and a parameter sharing one name,
     *  and merely lands on the ordinary uninterpreted {@code apply$f} modelling.) */
    static Set<String> functionFormalNames(MethodNode m) {
        Set<String> out = new HashSet<String>()
        Parameter[] ps = m.parameters
        if (ps != null) for (Parameter p : ps) {
            String tn = p.type?.name
            if (tn == 'java.util.function.Function' || tn == 'Function') out.add(p.name)
        }
        out
    }

    /** {@code Function}-typed formals → declared return type (the 2nd generic of {@code Function<A, R>}),
     *  so the encoder can sort {@code f.apply(x)}'s result; raw {@code Function} is omitted (default value
     *  sort). Pure function of the signature — shared by {@code VerifyChecker}'s scope collection. */
    static Map<String, ClassNode> functionReturnTypes(MethodNode m) {
        Map<String, ClassNode> out = new HashMap<String, ClassNode>()
        Parameter[] ps = m.parameters
        if (ps != null) for (Parameter p : ps) {
            ClassNode t = p.type
            if (t == null || t.name != 'java.util.function.Function') continue
            GenericsType[] g = t.genericsTypes
            if (g != null && g.length == 2 && g[1]?.type != null) out.put(p.name, g[1].type)
        }
        out
    }

    /** The rewriting walk. Contract closure bodies (quantifier predicates) are descended into by mutating
     *  their statements' expressions in place — sound because the whole tree is a fresh, unshared parse. */
    private static class SamRewriter implements ExpressionTransformer {
        private final Set<String> fnNames
        private final Map<String, Integer> enumSizes
        SamRewriter(Set<String> fnNames, Map<String, Integer> enumSizes) {
            this.fnNames = fnNames
            this.enumSizes = enumSizes
        }

        @Override
        Expression transform(Expression expr) {
            if (expr == null) return null
            // <EnumClass>.values().length — the property form of the enum-count fold
            if (expr instanceof PropertyExpression) {
                PropertyExpression pe = (PropertyExpression) expr
                if (pe.propertyAsString == 'length') {
                    Integer cnt = enumValuesCount(pe.objectExpression)
                    if (cnt != null) return constant(cnt, expr)
                }
            }
            if (expr instanceof MethodCallExpression) {
                MethodCallExpression mce = (MethodCallExpression) expr
                Expression recv = mce.objectExpression
                List<Expression> args = (mce.arguments instanceof TupleExpression)
                    ? ((TupleExpression) mce.arguments).expressions : null
                // <EnumClass>.values().size() — the method form of the enum-count fold
                if (mce.methodAsString == 'size' && args != null && args.isEmpty()) {
                    Integer cnt = enumValuesCount(recv)
                    if (cnt != null) return constant(cnt, expr)
                }
                boolean implicitThis = mce.isImplicitThis() ||
                    (recv instanceof VariableExpression && ((VariableExpression) recv).name == 'this')
                String name = mce.methodAsString
                if (implicitThis && name != null && fnNames.contains(name) && args != null && args.size() == 1) {
                    MethodCallExpression apply = new MethodCallExpression(
                        new VariableExpression(name), 'apply', transform(mce.arguments))
                    apply.implicitThis = false
                    apply.setSourcePosition(mce)
                    return apply
                }
            }
            if (expr instanceof ClosureExpression) {
                rewriteStatements(((ClosureExpression) expr).code)
                return expr
            }
            return expr.transformExpression(this)
        }

        /** {@code <name>.values()} (argless, unresolved VariableExpression receiver) for a known enum
         *  {@code name} → its constant count; null otherwise. */
        private Integer enumValuesCount(Expression e) {
            if (!(e instanceof MethodCallExpression)) return null
            MethodCallExpression mce = (MethodCallExpression) e
            if (mce.methodAsString != 'values') return null
            if (!(mce.arguments instanceof TupleExpression) ||
                !((TupleExpression) mce.arguments).expressions.isEmpty()) return null
            if (!(mce.objectExpression instanceof VariableExpression)) return null
            enumSizes.get(((VariableExpression) mce.objectExpression).name)
        }

        private static Expression constant(Integer cnt, Expression original) {
            ConstantExpression c = new ConstantExpression(cnt)
            c.setSourcePosition(original)
            c
        }

        /** Descend into a closure body's statements (a plain ExpressionTransformer stops at the closure).
         *  Only the statement kinds a contract closure can carry in-fragment; anything else is left alone. */
        private void rewriteStatements(Statement s) {
            if (s instanceof BlockStatement) {
                for (Statement inner : ((BlockStatement) s).statements) rewriteStatements(inner)
            } else if (s instanceof ExpressionStatement) {
                ExpressionStatement es = (ExpressionStatement) s
                es.expression = transform(es.expression)
            } else if (s instanceof ReturnStatement) {
                ReturnStatement rs = (ReturnStatement) s
                rs.expression = transform(rs.expression)
            }
        }
    }
}
