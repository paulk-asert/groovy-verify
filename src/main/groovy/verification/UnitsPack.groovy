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
import org.codehaus.groovy.ast.CodeVisitorSupport
import org.codehaus.groovy.ast.GenericsType
import org.codehaus.groovy.ast.ConstructorNode
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.Parameter
import org.codehaus.groovy.ast.expr.CastExpression
import org.codehaus.groovy.ast.stmt.Statement
import org.codehaus.groovy.ast.expr.ArgumentListExpression
import org.codehaus.groovy.ast.expr.BinaryExpression
import org.codehaus.groovy.ast.expr.ClassExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.PropertyExpression
import org.codehaus.groovy.ast.expr.StaticMethodCallExpression
import org.codehaus.groovy.ast.expr.TupleExpression
import org.codehaus.groovy.ast.expr.UnaryMinusExpression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.syntax.Types

/**
 * The JSR 385 / units-of-measurement domain as an {@link EncodingPack} — the migration that grew the SPI
 * demand-driven from call recognisers to the full set of surfaces the assessment predicted: a
 * <b>property</b> recogniser ({@code X.value}), a <b>binary-operator</b> recogniser (quantity-to-quantity
 * {@code ==}/{@code !=}), an <b>expression-claim</b> predicate (a {@code quantity * quantity} is not a
 * BigDecimal scalar — it must not be classified into the Real path), and a <b>value-source claim</b>
 * (a Quantity-typed local/{@code result} has no scalar handle, so the checker aliases the name to its
 * construction expression, which this pack's readers resolve).
 *
 * <p>The domain model (Phases 131–160): a quantity is a <b>dimension vector</b> over {@code [L, M, T]}
 * (compile-time, catches {@code length + mass}) times an <b>SI magnitude</b> (an exact Z3 Real, catches
 * the Mars-orbiter scale bug), recovered <i>structurally</i> from the construction —
 * {@code Quantities.getQuantity(v, KILO(METRE))}, {@code .to(U)}, {@code add/subtract/multiply/divide},
 * and the experimental {@code 1.km} DSL suffixes. Only quantities built in scope from curated units are
 * modelled; a parameter quantity skips loudly. All state is per-call ({@link Reader} wraps the
 * {@link TheoryApi}); the tables are static.
 *
 * <p>Corpus: groups {@code P131 dimensions}, {@code P132 unit-scale}, {@code P191 domain-typed names},
 * and the {@code examples-dsl} subproject's suite (the {@code 1.km + 1.mile} DSL) — verify and refute
 * twins throughout.
 */
@CompileStatic
class UnitsPack implements EncodingPack {

    @Override
    String name() { 'jsr385-units' }

    /** Phase 227 — the pack's thin contract rim (nullity facts); the dimension/scale semantics stay
     *  pack theory. Declaring them here gates them on the pack's enablement and puts them under the
     *  trusted-inventory lint. */
    @Override
    List<String> specFqns() { ['javax.measure.Quantity', 'tech.units.indriya.quantity.Quantities'] }

    /** The CASES groups; the DSL surface is additionally pinned by UnitScaleTest and the examples-dsl suite. */
    @Override
    List<String> corpusGroups() { ['P131 dimensions', 'P132 unit scale', 'P191 domain-typed names', 'P227 pack specs'] }

    /** {@code X.getValue()} — the SI magnitude read back in X's current unit (Phase 132). A non-quantity
     *  or unmodellable receiver falls through (the old inline handler fell through identically). */
    @Override
    Object translateCall(TheoryApi api, MethodCallExpression mce, String m, Expression recv, List<Expression> args) {
        if (m == 'getValue' && args.isEmpty()) {
            Object v = new Reader(api).valueTerm(recv, false)
            if (v != null) return v
        }
        TheoryApi.NO_MATCH
    }

    /** {@code X.value} — the property form of {@code getValue()} (Phase 148, experimental DSL). The core
     *  dispatches this hook after the carrier branches (a bespoke record's own `.value` field wins). */
    @Override
    Object translateProperty(TheoryApi api, PropertyExpression pe, Expression obj, String prop) {
        if (prop == 'value' && Reader.isQuantityTyped(obj)) {
            Object v = new Reader(api).valueTerm(obj, false)
            if (v != null) return v
        }
        TheoryApi.NO_MATCH
    }

    /** Phase 533 — {@code X.getValue() as BigDecimal} (or {@code X.value as BigDecimal}): Groovy converts a RationalNumber
     *  to its 34-digit {@code bigDecimalValue()}, where a bare read-out meets {@code ==} as {@code equals}. */
    @Override
    Object translateCast(TheoryApi api, CastExpression ce) {
        if (ce.type?.name != 'java.math.BigDecimal') return TheoryApi.NO_MATCH
        Expression inner = ce.expression
        Expression recv = null
        if (inner instanceof MethodCallExpression && ((MethodCallExpression) inner).methodAsString == 'getValue' &&
                Reader.argList((MethodCallExpression) inner).isEmpty()) recv = ((MethodCallExpression) inner).objectExpression
        if (inner instanceof PropertyExpression && ((PropertyExpression) inner).propertyAsString == 'value' &&
                Reader.isQuantityTyped(((PropertyExpression) inner).objectExpression)) recv = ((PropertyExpression) inner).objectExpression
        if (recv == null) return TheoryApi.NO_MATCH
        Reader r = new Reader(api)
        if (r.kind(recv) == null) return TheoryApi.NO_MATCH          // not a modelled quantity: the bare read-out decides
        r.valueTerm(recv, true)
    }

    /** Quantity-to-quantity {@code ==} / {@code !=} (Phase 151/159). Sound only by consulting BOTH layers:
     *  different dimensions THROW at runtime (UnconvertibleException, empirically pinned) — so {@code ==}
     *  is `false` (refutable, never provable-true) and {@code !=} must skip loudly (null); equal dimensions
     *  fall to SI-magnitude equality. A quantity-typed side the readers can't resolve is claimed as
     *  untranslatable (loud skip — Phase 191); only a comparison with no quantity-typed side at all
     *  falls through (NO_MATCH). */
    @Override
    Object translateBinary(TheoryApi api, BinaryExpression be, int opType) {
        if (opType != Types.COMPARE_EQUAL && opType != Types.COMPARE_NOT_EQUAL) return TheoryApi.NO_MATCH
        Reader r = new Reader(api)
        int[] dL = r.dimensionOf(be.leftExpression)
        int[] dR = r.dimensionOf(be.rightExpression)
        if (dL == null || dR == null) {
            // Phase 191 — a side is quantity-TYPED but its dimension is unresolvable (a Quantity
            // parameter, or a local bound from one). NO_MATCH here would let the generic scalar path
            // model the operands as int shadows and refute/prove a comparison whose runtime meaning
            // (compareTo value-equality; UnconvertibleException across kinds) that model does not
            // carry — the P900 probe caught exactly that refutation. Claim it: matched but
            // untranslatable → the loud skip (the Phase 151 posture for unknown quantities).
            if (Reader.isQuantityTyped(be.leftExpression) || Reader.isQuantityTyped(be.rightExpression)) return null
            return TheoryApi.NO_MATCH
        }
        if (!java.util.Arrays.equals(dL, dR)) {
            return opType == Types.COMPARE_EQUAL ? api.session.boolLit(false) : null
        }
        Object mL = r.siMagnitude(be.leftExpression)
        Object mR = r.siMagnitude(be.rightExpression)
        if (mL == null || mR == null) return null
        if (!r.comparesExactly(be.leftExpression, be.rightExpression)) return null      // Phase 533 — a 34-digit compare
        Object eq = api.session.eq(mL, mR)
        opType == Types.COMPARE_EQUAL ? eq : api.session.not(eq)
    }

    /** A quantity expression is a pack-domain value, not a BigDecimal scalar: `1.m / 1.s` dispatches to
     *  Quantity.divide, so the Real-division classifier (and the checker's divide-by-zero obligation
     *  collector) must not claim it (Phase 152). */
    @Override
    boolean claimsExpression(Expression e) { Reader.isQuantityExpr(e) }

    /** A Quantity construction the readers can model (dimension AND magnitude): the checker's gate for
     *  aliasing a Quantity-typed local / `result` to its construction expression (Phases 151/152). */
    @Override
    boolean claimsValueSource(TheoryApi api, Expression e) {
        Reader r = new Reader(api)
        r.dimensionOf(e) != null && r.siMagnitude(e) != null
    }

    // ==================== Phase 131 — JSR 385 dimensional analysis (C₀: dimension-only) ====================

    /** The base dimensions tracked, in vector order. Start with the Dafny base {@code [Length, Mass, Time]}. */
    private static final String[] DIM_BASE = ['L', 'M', 'T'] as String[]

    /**
     * {@code javax.measure.quantity.*} kind → its exponent vector over {@link #DIM_BASE}. A curated subset
     * (matched by fully-qualified name, so the engine never compiles against the unit-api jar); a
     * {@code Quantity<K>} whose {@code K} isn't here is treated as an unknown dimension and skips.
     */
    private static final Map<String, int[]> QUANTITY_KIND = [
        'javax.measure.quantity.Length'       : [1, 0, 0] as int[],
        'javax.measure.quantity.Mass'         : [0, 1, 0] as int[],
        'javax.measure.quantity.Time'         : [0, 0, 1] as int[],
        'javax.measure.quantity.Speed'        : [1, 0, -1] as int[],
        'javax.measure.quantity.Acceleration' : [1, 0, -2] as int[],
        'javax.measure.quantity.Area'         : [2, 0, 0] as int[],
        'javax.measure.quantity.Volume'       : [3, 0, 0] as int[],
        'javax.measure.quantity.Frequency'    : [0, 0, -1] as int[],
        'javax.measure.quantity.Force'        : [1, 1, -2] as int[],
        'javax.measure.quantity.Energy'       : [2, 1, -2] as int[],
        'javax.measure.quantity.Power'        : [2, 1, -3] as int[],
        'javax.measure.quantity.Dimensionless': [0, 0, 0] as int[],
    ]

    /**
     * Phase 131 — dimensional correctness for JSR 385 code. JSR 385 carries a quantity's kind in the generic
     * type ({@code Quantity<Length>}), and the static checker already rejects {@code mass.add(length)}. But
     * {@code multiply}/{@code divide} return {@code Quantity<?>} — the kind the type system *can't* infer — so
     * real code casts the result ({@code q.divide(t) as Quantity<Speed>}) or relies on the declared return type.
     * Those assertions are unchecked. This pass computes the result's exponent vector from the operands'
     * dimensions and refutes a cast/return whose declared kind disagrees. Pure compile-time vector arithmetic
     * (the dimensions are static), so no SMT is involved; it's the second face of the {@code @Label} lattice —
     * a free abelian group (×=add, /=subtract) rather than a join-semilattice.
     */
    @Override
    void checkMethod(CheckerApi api, MethodNode node) {
        if (node instanceof ConstructorNode) return
        if (!mentionsQuantity(node)) return                // not JSR 385 code → nothing to check
        Statement body = api.cleanBody(node)
        if (body == null) return
        // Only the `as Quantity<K>` cast is checkable: `multiply`/`divide` return `Quantity<? extends Quantity>`,
        // which STC won't assign to a `Quantity<K>` return *without* a cast — so real code always casts (the blog
        // does), and an un-cast return is rejected by the static checker before this pass, not modelled here.
        body.visit(new CodeVisitorSupport() {
            @Override void visitCastExpression(CastExpression ce) {
                int[] want = quantityKindVector(ce.type)
                if (want != null) checkDim(api, ce.expression, want, 'Quantity<' + kindSimpleName(ce.type) + '>', ce)
                super.visitCastExpression(ce)
            }
        })
    }

    /** Emit a refutation if {@code e}'s computed dimension is known and disagrees with {@code want}. */
    private static void checkDim(CheckerApi api, Expression e, int[] want, String targetText, org.codehaus.groovy.ast.ASTNode at) {
        int[] got = dimOf(api, e)
        if (got == null) return                            // couldn't determine the dimension → silently out of scope
        if (!java.util.Arrays.equals(got, want)) {
            api.reportError(formatDimensionMismatch(exprText(e), dimLabel(got), targetText, dimLabel(want)), at)
        }
    }

    /** True if the method's signature mentions {@code javax.measure.Quantity} (param or return) — the cheap gate. */
    private static boolean mentionsQuantity(MethodNode node) {
        if (isQuantityType(node.returnType)) return true
        for (Parameter p : node.parameters) if (isQuantityType(p.type)) return true
        false
    }

    private static boolean isQuantityType(ClassNode t) { t != null && t.name == 'javax.measure.Quantity' }

    /** The exponent vector of a {@code Quantity<K>} type (via its generic argument), or null. */
    private static int[] quantityKindVector(ClassNode t) {
        if (!isQuantityType(t)) return null
        GenericsType[] g = t.genericsTypes
        if (g == null || g.length < 1 || g[0].type == null) return null
        QUANTITY_KIND.get(g[0].type.name)
    }

    private static String kindSimpleName(ClassNode quantityType) {
        GenericsType[] g = quantityType?.genericsTypes
        (g != null && g.length >= 1 && g[0].type != null) ? g[0].type.nameWithoutPackage : '?'
    }

    /**
     * The exponent vector of a Quantity-typed expression, computed structurally: a declared {@code Quantity<K>}
     * variable/parameter is its kind; {@code ×} adds exponents, {@code /} subtracts, scalar {@code ×}/{@code /}
     * and {@code add}/{@code subtract}/{@code to} leave them unchanged; an inner cast contributes its declared
     * kind. Anything else (or an unknown kind) → null, i.e. out of scope.
     */
    private static int[] dimOf(CheckerApi api, Expression e) {
        if (e instanceof CastExpression) {
            int[] c = quantityKindVector(((CastExpression) e).type)
            return c != null ? c : dimOf(api, ((CastExpression) e).expression)
        }
        if (e instanceof VariableExpression) {
            return quantityKindVector(declaredTypeOf((VariableExpression) e))
        }
        if (e instanceof MethodCallExpression) {
            MethodCallExpression mce = (MethodCallExpression) e
            String m = mce.methodAsString
            if (m in ['multiply', 'divide', 'add', 'subtract', 'to']) {
                int[] dRecv = dimOf(api, mce.objectExpression)
                if (dRecv == null) return null
                List<Expression> args = (mce.arguments instanceof org.codehaus.groovy.ast.expr.ArgumentListExpression) ?
                    ((org.codehaus.groovy.ast.expr.ArgumentListExpression) mce.arguments).expressions : []
                Expression arg = args.isEmpty() ? null : args.get(0)
                boolean quantityArg = arg != null && isQuantityType(api.inferredTypeOf(arg))
                if (m == 'multiply') return quantityArg ? vadd(dRecv, dimOf(api, arg)) : dRecv      // scalar × keeps dimension
                if (m == 'divide')   return quantityArg ? vsub(dRecv, dimOf(api, arg)) : dRecv      // scalar / keeps dimension
                return dRecv                                                                    // add/subtract/to: unchanged
            }
        }
        null
    }

    /** Declared type (with generics) of a variable use — the parameter list is the reliable source of kind args. */
    private static ClassNode declaredTypeOf(VariableExpression ve) {
        org.codehaus.groovy.ast.Variable v = ve.accessedVariable
        (v != null) ? v.type : ve.type
    }

    private static int[] vadd(int[] a, int[] b) {
        if (a == null || b == null) return null
        int[] r = new int[a.length]; for (int i = 0; i < a.length; i++) r[i] = a[i] + b[i]; r
    }
    private static int[] vsub(int[] a, int[] b) {
        if (a == null || b == null) return null
        int[] r = new int[a.length]; for (int i = 0; i < a.length; i++) r[i] = a[i] - b[i]; r
    }

    /** A compact source-ish rendering of the expressions this pass walks (for the diagnostic). */
    private static String exprText(Expression e) {
        if (e instanceof VariableExpression) return ((VariableExpression) e).name
        if (e instanceof CastExpression) return exprText(((CastExpression) e).expression) + ' as ' + ((CastExpression) e).type.nameWithoutPackage
        if (e instanceof MethodCallExpression) {
            MethodCallExpression m = (MethodCallExpression) e
            List<Expression> args = (m.arguments instanceof org.codehaus.groovy.ast.expr.ArgumentListExpression) ?
                ((org.codehaus.groovy.ast.expr.ArgumentListExpression) m.arguments).expressions : []
            return exprText(m.objectExpression) + '.' + m.methodAsString + '(' + args.collect { exprText(it) }.join(', ') + ')'
        }
        if (e instanceof ConstantExpression) return String.valueOf(((ConstantExpression) e).value)
        try { return e?.text ?: '<expr>' } catch (ignored) { return '<expr>' }
    }

    /** A readable dimension, e.g. {@code [1,0,-1] → "L·T⁻¹"}, {@code [0,0,0] → "dimensionless"}. */
    private static String dimLabel(int[] d) {
        if (d == null) return '?'
        StringBuilder sb = new StringBuilder()
        for (int i = 0; i < d.length; i++) {
            if (d[i] == 0) continue
            if (sb.length() > 0) sb.append('·')
            sb.append(DIM_BASE[i])
            if (d[i] != 1) sb.append(superscript(d[i]))
        }
        sb.length() == 0 ? 'dimensionless' : sb.toString()
    }
    private static String superscript(int n) {
        String s = String.valueOf(Math.abs(n))
        StringBuilder b = new StringBuilder(n < 0 ? '⁻' : '')   // superscript minus
        for (char c : s.toCharArray()) b.append('⁰¹²³⁴⁵⁶⁷⁸⁹'.charAt((int) (c - (char) '0')))
        b.toString()
    }

    /** The C₀ mismatch diagnostic (moved from Reporter with the pass — it is units vocabulary). */
    private static String formatDimensionMismatch(String exprText, String gotDim, String targetText, String wantDim) {
        "Dimensional mismatch: '${exprText}' has dimension ${gotDim}, but is used as ${targetText} (${wantDim}). " +
        "A unit's dimension is the exponent vector over [Length, Mass, Time]; '*' adds exponents and '/' subtracts them."
    }

    /**
     * The migrated dimension/magnitude readers, verbatim from the encoder (Phases 131–160), bound to one
     * {@link TheoryApi} per hook call. Static members (the curated tables, the AST-shape tests) are
     * per-class; everything touching the session or the source-alias map rides {@code api}.
     */
    private static class Reader {
        private final TheoryApi api
        Reader(TheoryApi api) { this.api = api }

        private static List<Expression> argList(MethodCallExpression mce) {
            Expression a = mce.arguments
            if (a instanceof ArgumentListExpression) return ((ArgumentListExpression) a).expressions
            if (a instanceof TupleExpression) return ((TupleExpression) a).expressions
            return Collections.<Expression> emptyList()
        }
        private static List<Expression> callArgs(Expression e) {
            Expression a = (e instanceof StaticMethodCallExpression) ? ((StaticMethodCallExpression) e).arguments :
                           (e instanceof MethodCallExpression) ? ((MethodCallExpression) e).arguments : null
            (a instanceof ArgumentListExpression) ? ((ArgumentListExpression) a).expressions : Collections.<Expression>emptyList()
        }

        // ==================== Phase 132 — JSR 385 value/scale (C₁: SI-normalized magnitudes) ====================

        /** SI base units → their scale (always 1 for a base unit; a non-coherent base like GRAM carries its factor). */
        private static final Map<String, BigDecimal> BASE_UNIT_SCALE = [
            'METRE': 1.0G, 'METER': 1.0G, 'SECOND': 1.0G, 'KILOGRAM': 1.0G, 'GRAM': 0.001G,
            'KELVIN': 1.0G, 'AMPERE': 1.0G, 'MOLE': 1.0G, 'CANDELA': 1.0G,
            // Non-SI length units (scale to metres). The international mile is exactly 1609.344 m — pinned against
            // the JSR 385 RI by UnitScaleTest, since these scales are trusted constants, not computed.
            'MILE': 1609.344G, 'YARD': 0.9144G, 'FOOT': 0.3048G, 'INCH': 0.0254G,
            // Phase 532 — the coherent derived unit metre-per-second: SI magnitude is its value (pinned by UnitScaleTest).
            'METRE_PER_SECOND': 1.0G,
        ]

        /** Metric prefixes → their multiplier, so {@code KILO(METRE)} resolves to scale 1000. */
        private static final Map<String, BigDecimal> PREFIX_SCALE = [
            'GIGA': 1000000000.0G, 'MEGA': 1000000.0G, 'KILO': 1000.0G, 'HECTO': 100.0G, 'DECA': 10.0G, 'DEKA': 10.0G,
            'DECI': 0.1G, 'CENTI': 0.01G, 'MILLI': 0.001G, 'MICRO': 0.000001G, 'NANO': 0.000000001G,
        ]

        /**
         * Phase 148 — EXPERIMENTAL units DSL: a curated unit-suffix property (`1.km`, `1.mile`) → its scale-to-SI,
         * the same trusted-constant posture as {@link #BASE_UNIT_SCALE} but for the Groovy extension-method sugar a
         * consumer registers (`getKm(Number)` etc.). The verifier never compiles against the extension module — it
         * recognises the sugar *by property name* and gated on a {@code javax.measure.Quantity}-typed receiver. A
         * deliberately tiny, fixed vocabulary; anything outside it skips. See {@code examples-dsl}.
         */
        private static final Map<String, BigDecimal> DSL_SUFFIX_SCALE = [
            'm': 1.0G, 'km': 1000.0G, 'mile': 1609.344G, 'kg': 1.0G, 's': 1.0G,
            // `mps` is the *coherent SI derived unit* metre-per-second — a Speed literal whose SI magnitude IS its value.
            'mps': 1.0G,
        ]

        /**
         * Phase 151 — the *dimension* twin of {@link #BASE_UNIT_SCALE}: a base unit's exponent vector over the
         * {@code [Length, Mass, Time]} base (the same base as the Phase 131 cast-checker's {@code QUANTITY_KIND}).
         * The scale layer alone can't compare quantities (`1.m` and `1.kg` both have SI magnitude 1), so a
         * quantity-to-quantity {@code ==} consults this vector first: differing dimensions are never equal. Units
         * outside {@code [L,M,T]} (KELVIN/AMPERE/MOLE/CANDELA) are intentionally absent → unknown dimension → skip.
         */
        private static final Map<String, int[]> BASE_UNIT_DIM = [
            'METRE': [1, 0, 0] as int[], 'METER': [1, 0, 0] as int[],
            'MILE': [1, 0, 0] as int[], 'YARD': [1, 0, 0] as int[], 'FOOT': [1, 0, 0] as int[], 'INCH': [1, 0, 0] as int[],
            'KILOGRAM': [0, 1, 0] as int[], 'GRAM': [0, 1, 0] as int[],
            'SECOND': [0, 0, 1] as int[],
            'METRE_PER_SECOND': [1, 0, -1] as int[],     // Phase 532 — Speed = Length·Time⁻¹
        ]

        /** Phase 151 — the dimension twin of {@link #DSL_SUFFIX_SCALE} for the experimental unit-suffix sugar. */
        private static final Map<String, int[]> DSL_SUFFIX_DIM = [
            'm': [1, 0, 0] as int[], 'km': [1, 0, 0] as int[], 'mile': [1, 0, 0] as int[], 'kg': [0, 1, 0] as int[],
            's': [0, 0, 1] as int[], 'mps': [1, 0, -1] as int[],     // Speed = Length·Time⁻¹
        ]

        /** True when {@code e} is a JSR 385 Quantity expression the readers can model both the dimension AND the
         *  magnitude of — the gate {@code checkPath} uses before aliasing a Quantity-typed {@code result}. */
        boolean isModellableQuantity(Expression e) { dimensionOf(e) != null && siMagnitude(e) != null }

        /** The Quantity source expression a variable aliases (see the encoder source-alias map), else null. Guards against
         *  a self-alias so the readers' recursion terminates. */
        private Expression quantitySourceOf(Expression e) {
            if (!(e instanceof VariableExpression)) return null
            Expression src = api.sourceAlias(((VariableExpression) e).name)
            return (src != null && !src.is(e)) ? src : null
        }

        private static int[] vadd(int[] a, int[] b) {
            if (a == null || b == null) return null
            int[] r = new int[a.length]; for (int i = 0; i < a.length; i++) r[i] = a[i] + b[i]; r
        }
        private static int[] vsub(int[] a, int[] b) {
            if (a == null || b == null) return null
            int[] r = new int[a.length]; for (int i = 0; i < a.length; i++) r[i] = a[i] - b[i]; r
        }

        /** The dimension vector of a unit expression — a base-unit constant or a (nested) prefix application (a
         *  metric prefix is dimension-neutral). Mirrors {@code scaleOf}; null = outside the curated base → skip. */
        private int[] dimVecOf(Expression u) {
            if (u instanceof PropertyExpression) return BASE_UNIT_DIM.get(((PropertyExpression) u).propertyAsString)
            if (u instanceof VariableExpression) return BASE_UNIT_DIM.get(((VariableExpression) u).name)
            if (u instanceof MethodCallExpression) {
                MethodCallExpression mc = (MethodCallExpression) u
                List<Expression> a = argList(mc)
                if (PREFIX_SCALE.containsKey(mc.methodAsString) && a.size() == 1) return dimVecOf(a.get(0))
            }
            if (u instanceof StaticMethodCallExpression) {
                StaticMethodCallExpression mc = (StaticMethodCallExpression) u
                List<Expression> a = (mc.arguments instanceof org.codehaus.groovy.ast.expr.ArgumentListExpression) ?
                    ((org.codehaus.groovy.ast.expr.ArgumentListExpression) mc.arguments).expressions : []
                if (PREFIX_SCALE.containsKey(mc.method) && a.size() == 1) return dimVecOf(a.get(0))
            }
            null
        }

        /**
         * Phase 151 — the SI *dimension* (exponent vector over {@code [L,M,T]}) of a Quantity-valued expression,
         * recovered structurally exactly as {@link #siMagnitude} recovers the magnitude: {@code getQuantity(v,U)} is
         * {@code dim(U)}; {@code to}/{@code add}/{@code subtract} keep it; {@code multiply} adds vectors and
         * {@code divide} subtracts; the DSL suffix/`+`/`-`/`*` mirror those. A scalar factor is dimension-neutral.
         * null = unknown (a parameter quantity, an uncurated unit) → the {@code ==} caller skips, never guesses.
         */
        private int[] dimensionOf(Expression e) {
            Expression src = quantitySourceOf(e)
            if (src != null) return dimensionOf(src)
            if (isGetQuantityCall(e)) {
                List<Expression> a = callArgs(e)
                return a.size() == 2 ? dimVecOf(a.get(1)) : null
            }
            if (e instanceof MethodCallExpression) {
                MethodCallExpression mc = (MethodCallExpression) e
                String m = mc.methodAsString
                List<Expression> a = argList(mc)
                if (m == 'to' && a.size() == 1) return dimensionOf(mc.objectExpression)        // unit relabel: dimension invariant
                if (m == 'asType' && a.size() == 1) {                                             // Phase 532 — a kind check
                    int[] d = dimensionOf(mc.objectExpression)
                    int[] k = asTypeKind(a.get(0))
                    return (d != null && k != null && Arrays.equals(d, k)) ? d : null             // a mismatch throws: skip
                }
                if (m in ['add', 'subtract'] && a.size() == 1) return dimensionOf(mc.objectExpression)
                if (m in ['multiply', 'divide'] && a.size() == 1) {
                    int[] dRecv = dimensionOf(mc.objectExpression)
                    if (dRecv == null) return null
                    Expression arg = a.get(0)
                    if (isNumericScalar(arg)) return dRecv                                       // scalar ×/÷ keeps dimension
                    int[] dArg = dimensionOf(arg)
                    return m == 'multiply' ? vadd(dRecv, dArg) : vsub(dRecv, dArg)
                }
            }
            if (e instanceof PropertyExpression) {
                PropertyExpression pe = (PropertyExpression) e
                int[] d = DSL_SUFFIX_DIM.get(pe.propertyAsString)
                if (d != null && isQuantityExpr(pe)) return d
            }
            if (e instanceof BinaryExpression) {
                BinaryExpression be = (BinaryExpression) e
                String op = be.operation.text
                if (!isQuantityExpr(e)) return null
                if (op == '+' || op == '-') return dimensionOf(be.leftExpression)               // same-dimension (STC-enforced)
                if (op == '*' || op == '/') {
                    int[] l = isNumericScalar(be.leftExpression) ? ([0, 0, 0] as int[]) : dimensionOf(be.leftExpression)
                    int[] r = isNumericScalar(be.rightExpression) ? ([0, 0, 0] as int[]) : dimensionOf(be.rightExpression)
                    return op == '*' ? vadd(l, r) : vsub(l, r)                                   // Length/Time = Speed [1,0,-1]
                }
            }
            null
        }

        /** The scale-to-SI of a unit expression — a base-unit constant or a (nested) prefix application — or null. */
        private BigDecimal scaleOf(Expression u) {
            if (u instanceof PropertyExpression) return BASE_UNIT_SCALE.get(((PropertyExpression) u).propertyAsString)
            if (u instanceof VariableExpression) return BASE_UNIT_SCALE.get(((VariableExpression) u).name)
            if (u instanceof MethodCallExpression) {
                MethodCallExpression mc = (MethodCallExpression) u
                BigDecimal p = PREFIX_SCALE.get(mc.methodAsString)
                List<Expression> a = argList(mc)
                if (p != null && a.size() == 1) { BigDecimal inner = scaleOf(a.get(0)); return inner == null ? null : p * inner }
            }
            if (u instanceof StaticMethodCallExpression) {
                StaticMethodCallExpression mc = (StaticMethodCallExpression) u
                BigDecimal p = PREFIX_SCALE.get(mc.method)
                List<Expression> a = (mc.arguments instanceof org.codehaus.groovy.ast.expr.ArgumentListExpression) ?
                    ((org.codehaus.groovy.ast.expr.ArgumentListExpression) mc.arguments).expressions : []
                if (p != null && a.size() == 1) { BigDecimal inner = scaleOf(a.get(0)); return inner == null ? null : p * inner }
            }
            null
        }

        /** True for a {@code tech.units.indriya.quantity.Quantities.getQuantity(value, unit)} construction. */
        private static boolean isGetQuantityCall(Expression e) {
            if (e instanceof MethodCallExpression) {
                MethodCallExpression mc = (MethodCallExpression) e
                return mc.methodAsString == 'getQuantity' && String.valueOf(mc.objectExpression?.text).endsWith('Quantities')
            }
            if (e instanceof StaticMethodCallExpression) {
                StaticMethodCallExpression mc = (StaticMethodCallExpression) e
                return mc.method == 'getQuantity' && String.valueOf(mc.ownerType?.name).endsWith('Quantities')
            }
            false
        }

        /** A scalar (dimensionless number) factor for {@code multiply}/{@code divide} — a numeric literal or a
         *  numeric-typed expression, never a Quantity. */
        private static boolean isNumericScalar(Expression e) {
            if (e instanceof ConstantExpression) return ((ConstantExpression) e).value instanceof Number
            ClassNode t = null
            try { t = e?.getType() } catch (ignored) {}
            if (t == null || t.name == null) return false
            String n = t.name
            n in ['int', 'long', 'short', 'byte', 'double', 'float',
                  'java.lang.Integer', 'java.lang.Long', 'java.lang.Short', 'java.lang.Byte',
                  'java.lang.Double', 'java.lang.Float', 'java.math.BigDecimal', 'java.math.BigInteger', 'java.lang.Number']
        }

        /** Phase 532 — the exponent vector of {@code q.asType(K)}'s kind class {@code K}, or null when {@code K} isn't
         *  a curated {@code javax.measure.quantity} kind. indriya's {@code asType} checks the unit's dimension against
         *  {@code K} (throwing on a mismatch) and returns the quantity itself, so magnitude and unit carry through. */
        private static int[] asTypeKind(Expression k) {
            k instanceof ClassExpression ? QUANTITY_KIND.get(((ClassExpression) k).type.name) : null
        }

        /**
         * The SI magnitude (a Real term) of a Quantity-valued expression, recovered from its construction, gated on
         * {@link #kind}: the Real is indriya's exact value only where the kind analysis says no rounding occurs on the
         * way (Phase 533). Null = out of scope, a loud skip.
         */
        Object siMagnitude(Expression e) { kind(e) == null ? null : siMagnitudeRaw(e) }

        /**
         * The exact SI magnitude: {@code getQuantity(v, U)} is {@code v·scale(U)}, {@code to(U)} keeps it, {@code add}/
         * {@code subtract} combine same-dimension magnitudes (STC enforces the match), and {@code multiply}/{@code divide}
         * take a Quantity or a scalar. Exact rational arithmetic throughout: whether that is what indriya computes is
         * {@link #kind}'s question, so callers reach this only through {@link #siMagnitude}.
         */
        private Object siMagnitudeRaw(Expression e) {
            Expression src = quantitySourceOf(e)
            if (src != null) return siMagnitudeRaw(src)
            if (isGetQuantityCall(e)) {
                List<Expression> a = callArgs(e)
                if (a.size() != 2) return null
                BigDecimal s = scaleOf(a.get(1))
                Object vR = api.asRealValue(a.get(0))
                if (s == null || vR == null) return null
                return (s.compareTo(BigDecimal.ONE) == 0) ? vR : api.session.times(vR, api.session.realLit(TheoryApi.rationalOf(s)))
            }
            if (e instanceof MethodCallExpression) {
                MethodCallExpression mc = (MethodCallExpression) e
                String m = mc.methodAsString
                List<Expression> a = argList(mc)
                if (m == 'to' && a.size() == 1) return siMagnitudeRaw(mc.objectExpression)      // unit relabel: magnitude invariant
                if (m == 'asType' && a.size() == 1)                                               // Phase 532 — returns itself
                    return asTypeKind(a.get(0)) != null && dimensionOf(e) != null ? siMagnitudeRaw(mc.objectExpression) : null
                if (m in ['add', 'subtract', 'multiply', 'divide'] && a.size() == 1) {
                    return combineRaw(m, siMagnitudeRaw(mc.objectExpression), a.get(0))
                }
            }
            // Phase 148 (experimental DSL) — a curated unit-suffix property `v.km` is `v · scale`, and the DSL `+`/`-`
            // (the registered `plus`/`minus` extension operators) combine same-dimension magnitudes. Gated on a
            // javax.measure.Quantity-typed expression so a stray `.m` on a non-quantity can't be misread as a unit.
            if (e instanceof PropertyExpression) {
                PropertyExpression pe = (PropertyExpression) e
                BigDecimal sc = DSL_SUFFIX_SCALE.get(pe.propertyAsString)
                if (sc != null && isQuantityExpr(pe)) {
                    Object vR = api.asRealValue(pe.objectExpression)
                    if (vR == null) return null
                    return (sc.compareTo(BigDecimal.ONE) == 0) ? vR : api.session.times(vR, api.session.realLit(TheoryApi.rationalOf(sc)))
                }
            }
            // Phase 150/152 — the DSL `+`/`-` (add/subtract), `*` (Quantity.multiply) and `/` (the `div` extension, i.e.
            // Quantity.divide): the method forms' magnitudes. `1.km * 1.km` is an area of SI magnitude 1e6 (m²).
            if (e instanceof BinaryExpression && isQuantityExpr(e)) {
                BinaryExpression be = (BinaryExpression) e
                String m = DSL_OP.get(be.operation.text)
                if (m != null) return combineRaw(m, siMagnitudeRaw(be.leftExpression), be.rightExpression)
            }
            null
        }

        /** The DSL operators' method forms (the extension module's plus/minus/div, and Quantity's own multiply). */
        private static final Map<String, String> DSL_OP = ['+': 'add', '-': 'subtract', '*': 'multiply', '/': 'divide']

        /** {@code recv.m(arg)}'s exact SI magnitude from the receiver's: the argument is a Quantity if it reads as one,
         *  else (multiply/divide only) a numeric scalar. */
        private Object combineRaw(String m, Object recvM, Expression arg) {
            if (recvM == null) return null
            Object other = siMagnitudeRaw(arg)
            if (other == null && (m == 'multiply' || m == 'divide') && isNumericScalar(arg)) other = api.asRealValue(arg)
            if (other == null) return null
            if (m == 'add')      return api.session.plus(recvM, other)
            if (m == 'subtract') return api.session.minus(recvM, other)
            if (m == 'multiply') return api.session.times(recvM, other)
            return api.session.realDiv(recvM, other)                       // a closed non-zero divisor: kind's guard
        }

        // ==================== Phase 533 — indriya's number system ====================

        /**
         * What indriya 2.2.4 holds a quantity's value as, and so whether the exact Real is what it computes (measured).
         * Its number system keeps Integer, Long, BigInteger and RationalNumber exact (overflow widens, a division
         * multiplies by the divisor's exact reciprocal, a unit conversion by an exact rational factor), and narrows an
         * integral result to an integer type. A BigDecimal is exact too, until a RationalNumber meets it: the rational
         * is then read as {@code bigDecimalValue()}, rounded to 34 significant digits. And a BigDecimal's arithmetic in
         * a non-SI unit goes to the SI unit and back, so a factor whose reciprocal doesn't terminate (mile, foot) rounds
         * it: {@code 1.5 mile + 0 mile} is 1.4999…948. Fields: {@code dec}, the value may be a BigDecimal; {@code rat},
         * it may be a non-integral RationalNumber; {@code cur}/{@code si}, its exact value in its unit and in SI when
         * closed over literals; {@code scale}, its unit's scale to SI when known.
         */
        @CompileStatic
        static final class Kind {
            boolean dec
            boolean rat
            Rat cur
            Rat si
            Rat scale
        }

        /** The value's kind, or null where indriya may round (or the expression isn't a modelled quantity). */
        Kind kind(Expression e) {
            Expression src = quantitySourceOf(e)
            if (src != null) return kind(src)
            if (isGetQuantityCall(e)) {
                List<Expression> a = callArgs(e)
                if (a.size() != 2) return null
                BigDecimal s = scaleOf(a.get(1))
                return s == null ? null : leaf(a.get(0), Rat.of(s))
            }
            if (e instanceof PropertyExpression) {
                PropertyExpression pe = (PropertyExpression) e
                BigDecimal sc = DSL_SUFFIX_SCALE.get(pe.propertyAsString)
                if (sc != null && isQuantityExpr(pe)) return leaf(pe.objectExpression, Rat.of(sc))
                return null
            }
            if (e instanceof MethodCallExpression) {
                MethodCallExpression mc = (MethodCallExpression) e
                String m = mc.methodAsString
                List<Expression> a = argList(mc)
                if (a.size() != 1) return null
                if (m == 'to') {
                    BigDecimal t = scaleOf(a.get(0))
                    return t == null ? null : converted(kind(mc.objectExpression), Rat.of(t))
                }
                if (m == 'asType') return asTypeKind(a.get(0)) != null && dimensionOf(e) != null ? kind(mc.objectExpression) : null
                if (m in ['add', 'subtract', 'multiply', 'divide']) return combined(m, kind(mc.objectExpression), a.get(0))
                return null
            }
            if (e instanceof BinaryExpression && isQuantityExpr(e)) {
                BinaryExpression be = (BinaryExpression) e
                String m = DSL_OP.get(be.operation.text)
                if (m != null) return combined(m, kind(be.leftExpression), be.rightExpression)
            }
            null
        }

        /** {@code getQuantity(v, U)}: an integer-typed value is held exactly, a BigDecimal as itself (an integral one is
         *  narrowed, which the {@code dec} flag over-approximates); a double or an unknown number type is out of scope. */
        private Kind leaf(Expression v, Rat scale) {
            Boolean dec = isDecValue(v)
            if (dec == null || api.asRealValue(v) == null) return null
            Rat c = closedValue(v)
            new Kind(dec: dec, rat: false, cur: c, si: c?.times(scale), scale: scale)
        }

        /** {@code q.to(U)}: the value times the direct factor scale(q)/scale(U), an exact rational; a BigDecimal meets it
         *  as 34 digits ({@code 1.5 m} to miles is 0.000932…7730, measured), so it must convert exactly. */
        private Kind converted(Kind k, Rat target) {
            if (k == null || k.scale == null) return null
            Rat f = k.scale.div(target)
            if (k.dec && !f.bdExact()) return null
            new Kind(dec: k.dec, rat: k.rat || (!f.isInteger() && !surelyBigDecimal(k)), cur: k.cur?.times(f), si: k.si, scale: target)
        }

        /** {@code recv.m(arg)} for add/subtract (a Quantity argument) and multiply/divide (a Quantity or a scalar). */
        private Kind combined(String m, Kind r, Expression arg) {
            if (r == null) return null
            Kind q = kind(arg)
            if (m == 'add' || m == 'subtract') return q == null ? null : sum(r, q, m == 'add')
            if (q != null) return m == 'multiply' ? product(r, q) : quotient(r, q)
            if (siMagnitudeRaw(arg) != null || !isNumericScalar(arg)) return null      // an unmodelled quantity argument
            scaled(r, arg, m == 'multiply')
        }

        /** add/subtract: both to SI, combined, and back to the receiver's unit (measured: {@code 1.5 mile + 0 m} and
         *  {@code + 0 mile} alike are 1.4999…948). A BigDecimal needs every factor on that route to convert exactly,
         *  and a RationalNumber meeting it must read exactly at 34 digits. */
        private Kind sum(Kind a, Kind b, boolean plus) {
            boolean dec = a.dec || b.dec
            if (dec && !(decimalScale(a.scale) && decimalScale(b.scale) && meetsExactly(a) && meetsExactly(b))) return null
            boolean rat = a.rat || b.rat || a.scale == null || b.scale == null || !(a.scale.isOne() && b.scale.isOne())
            Rat si = (a.si != null && b.si != null) ? (plus ? a.si.plus(b.si) : a.si.minus(b.si)) : null
            Rat cur = (si != null && a.scale != null) ? si.div(a.scale) : null
            new Kind(dec: dec, rat: rat, cur: cur, si: si, scale: a.scale)
        }

        /** multiply/divide by a scalar: to SI, scaled, and back (measured: {@code 1.5 mile · 2} is 2.9999…). A divisor is
         *  closed and non-zero (a zero throws), and its reciprocal is a RationalNumber even of a BigDecimal. */
        private Kind scaled(Kind a, Expression c, boolean mul) {
            Boolean cdec = isDecValue(c)
            if (cdec == null) return null
            Rat cv = closedValue(c)
            if (!mul && (cv == null || cv.isZero())) return null
            Rat factor = mul ? cv : cv.inverse()
            boolean dec = a.dec || (mul && cdec)
            if (dec) {
                if (!decimalScale(a.scale) || !meetsExactly(a)) return null
                if (!mul && !factor.bdExact()) return null      // the reciprocal meets the BigDecimal as 34 digits
            }
            boolean rat = a.rat || a.scale == null || !a.scale.isOne() || (!mul && !factor.isInteger() && !surelyBigDecimal(a))
            new Kind(dec: dec, rat: rat, cur: (a.cur != null && factor != null) ? a.cur.times(factor) : null,
                     si: (a.si != null && factor != null) ? a.si.times(factor) : null, scale: a.scale)
        }

        /** multiply by a Quantity: the values multiply, no conversion (measured: {@code 1.5 mile · 1 s} is 1.5). */
        private Kind product(Kind a, Kind b) {
            boolean dec = a.dec || b.dec
            if (dec && !(meetsExactly(a) && meetsExactly(b))) return null
            new Kind(dec: dec, rat: a.rat || b.rat,
                     cur: (a.cur != null && b.cur != null) ? a.cur.times(b.cur) : null,
                     si: (a.si != null && b.si != null) ? a.si.times(b.si) : null,
                     scale: (a.scale != null && b.scale != null) ? a.scale.times(b.scale) : null)
        }

        /** divide by a Quantity: times the reciprocal of its value, a RationalNumber even of a BigDecimal (measured:
         *  {@code 1 m / 1.5 s} is 2/3), so the divisor's value is closed and non-zero. */
        private Kind quotient(Kind a, Kind b) {
            if (b.cur == null || b.cur.isZero() || b.si == null || b.scale == null) return null
            Rat inv = b.cur.inverse()
            if (a.dec && !(inv.bdExact() && meetsExactly(a))) return null
            new Kind(dec: a.dec, rat: a.rat || (!inv.isInteger() && !surelyBigDecimal(a)), cur: a.cur?.times(inv), si: a.si?.div(b.si),
                     scale: a.scale?.div(b.scale))
        }

        /** A value that may be a RationalNumber meets a BigDecimal exactly only when it reads exactly at 34 digits —
         *  known only when closed (a symbolic one may be any rational). */
        private static boolean meetsExactly(Kind k) {
            !k.rat || (k.cur != null && k.si != null && k.cur.bdExact() && k.si.bdExact())
        }

        /** A closed non-integral BigDecimal: one a RationalNumber factor meets as 34 digits, leaving a BigDecimal (or,
         *  integral, an integer), never a RationalNumber (measured: {@code 1.5 m / 2^48} is a BigDecimal). An integral
         *  one was narrowed to an integer, which the factor turns into a RationalNumber ({@code 3.0 m / 4} is 3/4). */
        private static boolean surelyBigDecimal(Kind k) { k.dec && !k.rat && k.cur != null && !k.cur.isInteger() }

        /** A unit scale a BigDecimal can go to SI and back through exactly: it and its reciprocal read exactly as 34
         *  digits (the metric prefixes and coherent units; not the mile, yard, foot or inch). */
        private static boolean decimalScale(Rat s) { s != null && !s.isZero() && s.bdExact() && s.inverse().bdExact() }

        /** True for an integer-typed value, false for a BigDecimal, null for anything else (a double, an unknown type). */
        private static Boolean isDecValue(Expression v) {
            if (v instanceof UnaryMinusExpression) return isDecValue(((UnaryMinusExpression) v).expression)
            if (v instanceof ConstantExpression) {
                Object c = ((ConstantExpression) v).value
                if (c instanceof Integer || c instanceof Long || c instanceof BigInteger || c instanceof Short || c instanceof Byte) return false
                return c instanceof BigDecimal ? Boolean.TRUE : null
            }
            ClassNode t = (ClassNode) v?.getNodeMetaData(org.codehaus.groovy.transform.stc.StaticTypesMarker.INFERRED_TYPE)
            if (t == null) { try { t = v?.getType() } catch (ignored) {} }
            String n = t?.name
            if (n in ['int', 'long', 'short', 'byte', 'java.lang.Integer', 'java.lang.Long', 'java.lang.Short',
                      'java.lang.Byte', 'java.math.BigInteger']) return false
            n == 'java.math.BigDecimal' ? Boolean.TRUE : null
        }

        /** A numeric literal (or its negation) as an exact rational; null when symbolic. */
        private static Rat closedValue(Expression v) {
            if (v instanceof UnaryMinusExpression) { Rat r = closedValue(((UnaryMinusExpression) v).expression); return r?.negate() }
            if (!(v instanceof ConstantExpression)) return null
            Object c = ((ConstantExpression) v).value
            if (!(c instanceof Number) || c instanceof Double || c instanceof Float) return null
            Rat.of(new BigDecimal(c.toString()))
        }

        /** Phase 148 — true when {@code e}'s (STC-inferred) type is {@code javax.measure.Quantity} — the gate that
         *  keeps the experimental DSL recognisers off non-quantity property reads / operators. The kind comes from
         *  STC's {@code INFERRED_TYPE} node metadata (a `+`/property's syntactic {@code getType()} is just Object). */
        private static boolean isQuantityTyped(Expression e) {
            if (e == null) return false
            ClassNode t = (ClassNode) e.getNodeMetaData(org.codehaus.groovy.transform.stc.StaticTypesMarker.INFERRED_TYPE)
            if (t == null) { try { t = e.getType() } catch (ignored) {} }
            t != null && t.name == 'javax.measure.Quantity'
        }

        /**
         * Phase 151 — is {@code e} a JSR 385 Quantity expression, for the DSL readers' gate? Prefers STC's
         * {@code INFERRED_TYPE} ({@link #isQuantityTyped}), but falls back to a *structural* recognition of the
         * curated DSL shapes when that metadata is absent. The metadata IS absent inside an {@code @Ensures}
         * closure — captured at CONVERSION, before type-checking — so `result == 1.km` needs this to see the `1.km`.
         * The fallback is tight: a curated unit suffix on a numeric receiver ({@code 1.km}), or a {@code +}/{@code -}/
         * {@code *} of such — never a bare `.m` on an arbitrary object.
         */
        static boolean isQuantityExpr(Expression e) {
            if (e == null) return false
            if (isQuantityTyped(e)) return true
            if (e instanceof PropertyExpression) {
                PropertyExpression pe = (PropertyExpression) e
                return DSL_SUFFIX_SCALE.containsKey(pe.propertyAsString) && isNumericReceiver(pe.objectExpression)
            }
            if (e instanceof BinaryExpression) {
                String op = ((BinaryExpression) e).operation.text
                if (op == '+' || op == '-' || op == '*' || op == '/') {
                    return isQuantityExpr(((BinaryExpression) e).leftExpression) ||
                           isQuantityExpr(((BinaryExpression) e).rightExpression)
                }
            }
            false
        }

        /** A numeric receiver for a DSL unit suffix — a numeric literal ({@code 1.km}) or numeric-typed expression. */
        private static boolean isNumericReceiver(Expression r) {
            if (r instanceof ConstantExpression) return ((ConstantExpression) r).value instanceof Number
            return isNumericScalar(r)
        }

        /**
         * {@code X.getValue()} (or the property {@code X.value}) as a Real: the value in X's unit. Phase 533 — what the
         * read-out is depends on indriya's number type. A bare read-out ({@code asBigDecimal} false) meets Groovy's
         * {@code ==}, which on a RationalNumber (not Comparable) is {@code equals}: {@code 1 m / 4}'s value {@code == 0.25}
         * is false (measured), so a value that may be a non-integral RationalNumber skips. Under {@code as BigDecimal} a
         * RationalNumber reads as its 34 significant digits ({@code 10 km / 3} in metres is 3333.333…3), exactly
         * computed when closed.
         */
        Object valueTerm(Expression recv, boolean asBigDecimal) {
            Kind k = kind(recv)
            if (k == null || k.scale == null || k.scale.isZero()) return null
            Object mag = siMagnitudeRaw(recv)
            if (mag == null) return null
            Object term = k.scale.isOne() ? mag : api.session.realDiv(mag, api.session.realLit(k.scale.smt()))
            if (k.cur != null && k.cur.isInteger()) return term                 // narrowed to an integer type
            if (!asBigDecimal) return k.rat ? null : term                       // a RationalNumber's == is equals
            if (k.cur != null) {
                if (k.cur.bdExact()) return term
                if (!k.dec) return api.session.realLit(Rat.of(k.cur.round34()).smt())
            }
            k.rat ? null : term
        }

        /** Phase 533 — whether quantity {@code ==} between {@code l} and {@code r} compares exactly. Two values that are
         *  never BigDecimals are exact rationals, compared exactly (measured: {@code 1 m / 3} isn't 0.333…3 / 1). With a
         *  BigDecimal side, indriya converts the argument into the receiver's unit and reads a RationalNumber at 34
         *  digits ({@code 1 m / 3 == 0.333…3 m}, 34 threes, is true, and {@code 1.5 mile == 2414.016 m} false while the
         *  reverse is true), so the conversion and both values must read exactly. */
        boolean comparesExactly(Expression l, Expression r) {
            Kind a = kind(l), b = kind(r)
            if (a == null || b == null) return false
            if (!a.dec && !b.dec) return true
            if (a.scale == null || b.scale == null || a.scale.isZero()) return false
            Rat f = b.scale.div(a.scale)
            if (b.dec && !f.bdExact()) return false
            Rat argInRecv = b.cur?.times(f)
            boolean argMayRat = b.rat || !f.isInteger()
            if (argMayRat && !(argInRecv != null && argInRecv.bdExact())) return false
            meetsExactly(a)
        }
    }

    /** Phase 533 — an exact rational (reduced, positive denominator), for indriya's closed values. */
    @CompileStatic
    static final class Rat {
        final BigInteger n
        final BigInteger d

        Rat(BigInteger num, BigInteger den) {
            if (den.signum() == 0) throw new ArithmeticException('a rational with a zero denominator')
            if (den.signum() < 0) { num = num.negate(); den = den.negate() }
            BigInteger g = num.gcd(den)
            if (g.signum() == 0) g = BigInteger.ONE
            n = num.divide(g)
            d = den.divide(g)
        }

        static Rat of(BigDecimal b) {
            b.scale() <= 0 ? new Rat(b.toBigIntegerExact(), BigInteger.ONE) : new Rat(b.unscaledValue(), BigInteger.TEN.pow(b.scale()))
        }

        Rat plus(Rat o)  { new Rat(n * o.d + o.n * d, d * o.d) }
        Rat minus(Rat o) { new Rat(n * o.d - o.n * d, d * o.d) }
        Rat times(Rat o) { new Rat(n * o.n, d * o.d) }
        Rat div(Rat o)   { new Rat(n * o.d, d * o.n) }
        Rat inverse()    { new Rat(d, n) }
        Rat negate()     { new Rat(n.negate(), d) }
        boolean isZero()    { n.signum() == 0 }
        boolean isOne()     { n == BigInteger.ONE && d == BigInteger.ONE }
        boolean isInteger() { d == BigInteger.ONE }

        /** A denominator of only 2s and 5s: a terminating decimal. */
        boolean terminates() {
            BigInteger u = d
            BigInteger two = BigInteger.valueOf(2), five = BigInteger.valueOf(5)
            while (u.mod(two).signum() == 0) u = u.divide(two)
            while (u.mod(five).signum() == 0) u = u.divide(five)
            u == BigInteger.ONE
        }

        /** Reads exactly as indriya's {@code bigDecimalValue()}: an integer, or a terminating decimal of at most 34
         *  significant digits (DECIMAL128). */
        boolean bdExact() {
            isInteger() || (terminates() && new BigDecimal(n).divide(new BigDecimal(d)).precision() <= 34)
        }

        /** indriya's {@code bigDecimalValue()}: 34 significant digits, half-even (measured: 1/2^49 reads …312, not …313). */
        BigDecimal round34() { new BigDecimal(n).divide(new BigDecimal(d), java.math.MathContext.DECIMAL128) }

        /** The SMT rational literal. */
        String smt() { d == BigInteger.ONE ? n.toString() : n.toString() + '/' + d.toString() }
    }
}
