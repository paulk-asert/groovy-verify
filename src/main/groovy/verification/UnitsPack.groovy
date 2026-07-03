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
 * <p>Corpus: groups {@code P131 dimensions}, {@code P132 unit-scale}, and the {@code examples-dsl}
 * subproject's suite (the {@code 1.km + 1.mile} DSL) — verify and refute twins throughout.
 */
@CompileStatic
class UnitsPack implements EncodingPack {

    @Override
    String name() { 'jsr385-units' }

    /** The CASES groups; the DSL surface is additionally pinned by UnitScaleTest and the examples-dsl suite. */
    @Override
    List<String> corpusGroups() { ['P131 dimensions', 'P132 unit scale'] }

    /** {@code X.getValue()} — the SI magnitude read back in X's current unit (Phase 132). A non-quantity
     *  or unmodellable receiver falls through (the old inline handler fell through identically). */
    @Override
    Object translateCall(TheoryApi api, MethodCallExpression mce, String m, Expression recv, List<Expression> args) {
        if (m == 'getValue' && args.isEmpty()) {
            Object v = new Reader(api).quantityValueTerm(recv)
            if (v != null) return v
        }
        TheoryApi.NO_MATCH
    }

    /** {@code X.value} — the property form of {@code getValue()} (Phase 148, experimental DSL). The core
     *  dispatches this hook after the carrier branches (a bespoke record's own `.value` field wins). */
    @Override
    Object translateProperty(TheoryApi api, PropertyExpression pe, Expression obj, String prop) {
        if (prop == 'value' && Reader.isQuantityTyped(obj)) {
            Object v = new Reader(api).quantityValueTerm(obj)
            if (v != null) return v
        }
        TheoryApi.NO_MATCH
    }

    /** Quantity-to-quantity {@code ==} / {@code !=} (Phase 151/159). Sound only by consulting BOTH layers:
     *  different dimensions THROW at runtime (UnconvertibleException, empirically pinned) — so {@code ==}
     *  is `false` (refutable, never provable-true) and {@code !=} must skip loudly (null); equal dimensions
     *  fall to SI-magnitude equality. Either side unmodellable → NO_MATCH (the core's fall-through). */
    @Override
    Object translateBinary(TheoryApi api, BinaryExpression be, int opType) {
        if (opType != Types.COMPARE_EQUAL && opType != Types.COMPARE_NOT_EQUAL) return TheoryApi.NO_MATCH
        Reader r = new Reader(api)
        int[] dL = r.dimensionOf(be.leftExpression)
        int[] dR = r.dimensionOf(be.rightExpression)
        if (dL == null || dR == null) return TheoryApi.NO_MATCH
        if (!java.util.Arrays.equals(dL, dR)) {
            return opType == Types.COMPARE_EQUAL ? api.session.boolLit(false) : null
        }
        Object mL = r.siMagnitude(be.leftExpression)
        Object mR = r.siMagnitude(be.rightExpression)
        if (mL == null || mR == null) return null
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

        /**
         * The SI magnitude (a Real term) of a Quantity-valued expression, recovered from its construction:
         * {@code getQuantity(v, U)} is {@code v·scale(U)}, {@code to(U)} is magnitude-invariant, {@code add}/{@code
         * subtract} combine same-dimension magnitudes (the dimension match is what STC already enforces on these),
         * and {@code multiply}/{@code divide} take a Quantity or a scalar. A Quantity whose construction isn't
         * visible (a parameter) → null, i.e. out of scope.
         */
        private Object siMagnitude(Expression e) {
            Expression src = quantitySourceOf(e)
            if (src != null) return siMagnitude(src)
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
                if (m == 'to' && a.size() == 1) return siMagnitude(mc.objectExpression)         // unit relabel: magnitude invariant
                if (m in ['add', 'subtract', 'multiply', 'divide'] && a.size() == 1) {
                    Object recvM = siMagnitude(mc.objectExpression)
                    if (recvM == null) return null
                    Expression arg = a.get(0)
                    Object other
                    if (m == 'add' || m == 'subtract') {
                        other = siMagnitude(arg)                  // add/subtract take a same-dimension Quantity (STC-enforced)
                    } else {
                        Object q = siMagnitude(arg)               // multiply/divide: a Quantity if we can model it,
                        other = q != null ? q : (isNumericScalar(arg) ? api.asRealValue(arg) : null)   // else a numeric scalar
                    }
                    if (other == null) return null
                    if (m == 'add')      return api.session.plus(recvM, other)
                    if (m == 'subtract') return api.session.minus(recvM, other)
                    if (m == 'multiply') return api.session.times(recvM, other)
                    return api.session.realDiv(recvM, other)                                          // divide
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
            if (e instanceof BinaryExpression) {
                BinaryExpression be = (BinaryExpression) e
                String op = be.operation.text
                if ((op == '+' || op == '-') && isQuantityExpr(e)) {
                    Object l = siMagnitude(be.leftExpression)
                    Object r = siMagnitude(be.rightExpression)
                    if (l == null || r == null) return null
                    return op == '+' ? api.session.plus(l, r) : api.session.minus(l, r)
                }
                // Phase 150/152 — the DSL `*` (Quantity.multiply) and `/` (Quantity.divide): magnitudes multiply/divide.
                // `1.km * 1.km` is an *area* whose SI magnitude is 1000·1000 = 1e6 (m²); `1.m / 1.s` is a *speed* whose SI
                // magnitude is 1 (m/s). A scalar factor multiplies/divides the magnitude. (The dimension the operator
                // produces is invisible to the magnitude alone — the dimension reader / the .value read-out make it
                // observable to the verifier.)
                if ((op == '*' || op == '/') && isQuantityExpr(e)) {
                    Object l = siMagnitude(be.leftExpression)
                    if (l == null && isNumericScalar(be.leftExpression)) l = api.asRealValue(be.leftExpression)
                    Object r = siMagnitude(be.rightExpression)
                    if (r == null && isNumericScalar(be.rightExpression)) r = api.asRealValue(be.rightExpression)
                    if (l == null || r == null) return null
                    if (op == '*') return api.session.times(l, r)
                    // Phase 143 posture: exact Real division is sound only for a terminating divisor (Groovy rounds the
                    // rest, e.g. `/3`). The divisor here is a *quantity's magnitude*, not a syntactic literal, so guard on
                    // the right operand's scale being a terminating decimal — a unit scale (1, 1000, 1609.344) always is.
                    if (!isTerminatingQuantityDivisor(be.rightExpression)) return null
                    return api.session.realDiv(l, r)
                }
            }
            null
        }

        /** Phase 152 — true when the divisor {@code e}'s SI magnitude is a *closed terminating decimal*, so exact Real
         *  division is sound (Groovy/indriya round a non-terminating quotient, which the exact Real model would not — and
         *  a later multiply-back could then "verify" a runtime-false contract, the Phase 143 hazard). We compute the full
         *  magnitude (value·scale, including the unit scale — so {@code 1.mile} = 1609.344, which has a factor of 3, is
         *  correctly rejected) and test it has only the prime factors 2 and 5; a symbolic divisor (a parameter) → false. */
        private boolean isTerminatingQuantityDivisor(Expression e) {
            BigDecimal m = closedQuantityMagnitude(e)
            return m != null && isTerminatingDecimal(m)
        }

        /** The SI magnitude of a Quantity (or scalar) expression as a literal {@link BigDecimal}, when it's fully closed
         *  over numeric literals and curated units; null if anything is symbolic (a name, a parameter). The BigDecimal
         *  twin of {@link #siMagnitude}, used only by the division soundness guard. */
        private BigDecimal closedQuantityMagnitude(Expression e) {
            if (e == null) return null
            Expression src = quantitySourceOf(e)
            if (src != null) return closedQuantityMagnitude(src)        // a quantity local resolves to its RHS
            if (e instanceof UnaryMinusExpression) {
                BigDecimal inner = closedQuantityMagnitude(((UnaryMinusExpression) e).expression)
                return inner == null ? null : inner.negate()
            }
            if (e instanceof ConstantExpression) {
                Object v = ((ConstantExpression) e).value
                if (!(v instanceof Number) || v instanceof Double || v instanceof Float) return null
                try { return new BigDecimal(v.toString()) } catch (Exception ignored) { return null }
            }
            if (e instanceof PropertyExpression) {
                PropertyExpression pe = (PropertyExpression) e
                BigDecimal sc = DSL_SUFFIX_SCALE.get(pe.propertyAsString)
                if (sc == null) return null
                BigDecimal v = closedQuantityMagnitude(pe.objectExpression)
                return v == null ? null : v.multiply(sc)
            }
            if (e instanceof BinaryExpression) {
                BinaryExpression be = (BinaryExpression) e
                String op = be.operation.text
                BigDecimal l = closedQuantityMagnitude(be.leftExpression)
                BigDecimal r = closedQuantityMagnitude(be.rightExpression)
                if (l == null || r == null) return null
                switch (op) {
                    case '+': return l.add(r)
                    case '-': return l.subtract(r)
                    case '*': return l.multiply(r)
                    case '/': return (r.signum() == 0 || !isTerminatingDecimal(r)) ? null : l.divide(r)
                }
            }
            null
        }

        /** A BigDecimal whose unscaled integer has only the prime factors 2 and 5 — i.e. a *terminating* decimal, safe
         *  as an exact Real divisor (the value-level twin of {@link #isTerminatingDivisor}'s expression test). */
        private static boolean isTerminatingDecimal(BigDecimal bd) {
            if (bd == null || bd.signum() == 0) return false
            BigInteger u = bd.unscaledValue().abs()
            BigInteger two = BigInteger.valueOf(2), five = BigInteger.valueOf(5)
            while (u.mod(two).signum() == 0) u = u.divide(two)
            while (u.mod(five).signum() == 0) u = u.divide(five)
            u.equals(BigInteger.ONE)
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

        /** Phase 148 — the scale of an expression's *current* unit, for a getValue read-out: a unit-suffix property's
         *  scale, a {@code to(U)} / {@code getQuantity(_, U)}'s unit, or (for the DSL `+`/`-` and `add`/`subtract`) the
         *  receiver's unit, which those keep. {@code value-in-unit = siMagnitude / currentUnitScale}. */
        private BigDecimal currentUnitScale(Expression e) {
            Expression src = quantitySourceOf(e)
            if (src != null) return currentUnitScale(src)
            if (e instanceof PropertyExpression) {
                BigDecimal sc = DSL_SUFFIX_SCALE.get(((PropertyExpression) e).propertyAsString)
                if (sc != null) return sc
            }
            if (e instanceof BinaryExpression) {
                BinaryExpression be = (BinaryExpression) e
                String op = be.operation.text
                if (op == '+' || op == '-') return currentUnitScale(be.leftExpression)
                // Phase 150/152 — a product/quotient's current unit is the product/quotient of the operands' units
                // (km · km = km², scale 1e6; m / s = m·s⁻¹, scale 1), so `(1.km * 1.km).value` reads back 1e6/1e6 = 1 and
                // `(1.m / 1.s).value` reads back 1. A scalar factor carries unit-scale 1.
                if (op == '*' || op == '/') {
                    BigDecimal l = currentUnitScale(be.leftExpression)
                    if (l == null && isNumericScalar(be.leftExpression)) l = 1.0G
                    BigDecimal r = currentUnitScale(be.rightExpression)
                    if (r == null && isNumericScalar(be.rightExpression)) r = 1.0G
                    if (l == null || r == null) return null
                    if (op == '*') return l * r
                    return (r.signum() == 0 || !isTerminatingDecimal(r)) ? null : l.divide(r)
                }
            }
            if (e instanceof MethodCallExpression) {
                MethodCallExpression mc = (MethodCallExpression) e
                List<Expression> a = argList(mc)
                if (mc.methodAsString == 'to' && a.size() == 1) return scaleOf(a.get(0))
                if (mc.methodAsString in ['add', 'subtract'] && a.size() == 1) return currentUnitScale(mc.objectExpression)
            }
            if (isGetQuantityCall(e)) {
                List<Expression> a = callArgs(e)
                if (a.size() == 2) return scaleOf(a.get(1))
            }
            null
        }

        /** {@code X.getValue()} (or the property `X.value`) as a Real — the SI magnitude read back in X's *current*
         *  unit, i.e. {@code siMagnitude(X) / currentUnitScale(X)}. Modelled only when both are syntactically known
         *  (a {@code to(U)} / {@code getQuantity(_, U)} top, or the experimental DSL forms); else null (skips). */
        private Object quantityValueTerm(Expression recv) {
            Object mag = siMagnitude(recv)
            BigDecimal s = currentUnitScale(recv)
            if (mag == null || s == null) return null
            return (s.compareTo(BigDecimal.ONE) == 0) ? mag : api.session.realDiv(mag, api.session.realLit(TheoryApi.rationalOf(s)))
        }    }
}
