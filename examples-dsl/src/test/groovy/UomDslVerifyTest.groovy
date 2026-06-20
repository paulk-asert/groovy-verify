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
import org.codehaus.groovy.control.MultipleCompilationErrorsException
import org.codehaus.groovy.control.messages.SyntaxErrorMessage
import org.junit.jupiter.api.Test

import static org.junit.jupiter.api.Assertions.assertNull
import static org.junit.jupiter.api.Assertions.assertTrue

/**
 * The literal blog-DSL units sentence, verified by groovy-verify at compile time. The registered
 * {@code UomExtensions} module (on this test's classpath) makes `1.km` resolve to a JSR 385 quantity; the C₁
 * reader, extended to recognise the DSL sugar, proves the resulting expression. Each case compiles a snippet
 * under {@code @TypeChecked(extensions = 'verification.VerifyChecker')} and inspects the diagnostics.
 */
class UomDslVerifyTest {

    private static String snippet(String ensures, String retType, String body) {
        """
        import groovy.transform.TypeChecked
        import groovy.contracts.Ensures

        @TypeChecked(extensions = 'verification.VerifyChecker')
        class DslCase {
            @Ensures({ $ensures })
            static $retType total() { $body }
        }
        """
    }

    /** Diagnostics from compiling {@code src} (null means a clean compile = verified). */
    private static String diagnostics(String src) {
        def gcl = new GroovyClassLoader(UomDslVerifyTest.class.classLoader)
        try {
            gcl.parseClass(src, 'DslCase.groovy')
            return null
        } catch (MultipleCompilationErrorsException e) {
            return e.errorCollector.errors.collect { err ->
                err instanceof SyntaxErrorMessage ? err.cause.message : err.toString()
            }.join('\n')
        } finally {
            try { gcl.close() } catch (ignored) {}
        }
    }

    @Test
    void metreTotalVerifies() {
        // 1 km + 1 mile, worked in metres, reads back exactly 2609.344 m.
        assertNull(diagnostics(snippet('result == 2609.344', 'BigDecimal', '(1000.m + 1.mile).value as BigDecimal')))
    }

    @Test
    void kilometreReadingVerifies() {
        // The same sum built in kilometres reads back 2.609344 km — the verifier tracks the unit.
        assertNull(diagnostics(snippet('result == 2.609344', 'BigDecimal', '(1.km + 1.mile).value as BigDecimal')))
    }

    @Test
    void unitConfusionRefutes() {
        // The Mars bug, in the pretty syntax: `(1.km + 1.mile)` is in *kilometres*, so claiming the metre number
        // (2609.344) is false — its `.value` is 2.609344 — and the verifier refutes it.
        String d = diagnostics(snippet('result == 2609.344', 'BigDecimal', '(1.km + 1.mile).value as BigDecimal'))
        assertTrue(d?.contains('Cannot prove postcondition'), "expected refutation, got: $d")
    }

    @Test
    void wrongTotalRefutes() {
        String d = diagnostics(snippet('result == 2600.0', 'BigDecimal', '(1000.m + 1.mile).value as BigDecimal'))
        assertTrue(d?.contains('Cannot prove postcondition'), "expected refutation, got: $d")
    }

    @Test
    void squareKilometreVerifies() {
        // `1.km * 1.km` is an *area* — one square kilometre — so its `.value` reads back 1, not 1000 or 1e6.
        assertNull(diagnostics(snippet('result == 1.0', 'BigDecimal', '(1.km * 1.km).value as BigDecimal')))
    }

    @Test
    void squareKilometreUnitConfusionRefutes() {
        // The dimension trap a `Quantity<?>` can't catch (erasure leaves only one `multiply`): `1.km * 1.km` is
        // 1 km², value 1 — NOT the metre² magnitude 1e6. There's no static error (it's a perfectly typed area);
        // the verifier refutes it on the scale layer. A *value* refutation — unlike `1.kg`, a dimension the JSR 385
        // generics reject outright before the verifier ever runs.
        String d = diagnostics(snippet('result == 1000000.0', 'BigDecimal', '(1.km * 1.km).value as BigDecimal'))
        assertTrue(d?.contains('Cannot prove postcondition'), "expected refutation, got: $d")
    }

    @Test
    void dimensionMismatchRejectedByTheTypeSystem() {
        // A length plus a mass: the JSR 385 generics reject `plus(Quantity<Length>, Quantity<Mass>)` outright —
        // the dimension is caught by the type system before the verifier (the scale layer) ever runs.
        String d = diagnostics(snippet('result == 0', 'BigDecimal', '(1.km + 1.kg).value as BigDecimal'))
        assertTrue(d != null, 'expected a compile error for length + mass, but it compiled')
    }

    // ── Phase 151 — quantity-to-quantity `==` (the literal `result == 1.km` form, no `.value`) ──
    // Sound now because the comparison consults BOTH the dimension (a compile-time exponent vector) and the SI
    // magnitude: equal dimensions ⇒ magnitudes settle it; differing dimensions ⇒ never equal (`1.m == 1.kg`
    // throws at runtime — never true). Empirically pinned: `1.km == 1000.m` is true, `1.km == 1.m` is false.

    @Test
    void quantityEqualsAcrossUnitsVerifies() {
        // The literal blog form the user asked for: a Quantity-returning method whose `result` IS a quantity.
        // `1000.m` and `1.km` are the same Length (both 1000 m), so `result == 1.km` holds — no `.value` needed.
        assertNull(diagnostics(snippet('result == 1.km', 'javax.measure.Quantity', '1000.m')))
    }

    @Test
    void quantityEqualsWrongMagnitudeRefutes() {
        // Same dimension (Length), different magnitude: 2000 m is not 1 km, so the postcondition refutes.
        String d = diagnostics(snippet('result == 1.km', 'javax.measure.Quantity', '2000.m'))
        assertTrue(d?.contains('Cannot prove postcondition'), "expected refutation, got: $d")
    }

    @Test
    void quantityEqualsDimensionMismatchRefutes() {
        // The user's `@Ensures({ result == 1.km }) Quantity squareKm() { 1.km * 1.km }`. `result` is an *area*
        // (km², dimension [2,0,0]); `1.km` is a length ([1,0,0]). Different dimensions are never equal — so the
        // contract refutes *on the dimension*, with no `.value` and no help from the (erased) generics. (At runtime
        // the comparison throws `UnconvertibleException`; either way it can never be true, so the contract can't hold.)
        String d = diagnostics(snippet('result == 1.km', 'javax.measure.Quantity', '1.km * 1.km'))
        assertTrue(d?.contains('Cannot prove postcondition'), "expected refutation, got: $d")
    }

    @Test
    void quantityNotEqualsDimensionMismatchSkips() {
        // Soundness guard for the `!=` direction: across different dimensions the runtime comparison THROWS, so it
        // is neither true nor false. We must NOT *prove* `result != 1.km` (the method would throw at its own
        // contract check) — so this skips loudly rather than verifying. (The `==` mirror above refutes; only `!=`
        // would be the unsound "verified", so it's the one that must skip.)
        String d = diagnostics(snippet('result != 1.km', 'javax.measure.Quantity', '1.km * 1.km'))
        assertTrue(d?.contains('Skipped verification') || d?.contains('outside fragment'),
            "expected a loud skip for a cross-dimension !=, got: $d")
    }

    // ── Phase 152 — DSL division (Speed = Length/Time), and quantity-typed locals (`def d = 1.m; d / s`) ──

    @Test
    void speedFromDivisionVerifies() {
        // The motivating example: `def s = 1.s; def d = 1.m; d / s` is 1 m/s. `result == 1.m / 1.s` holds — the
        // locals are aliased to their RHS, the `/` operator subtracts the dimension exponents (Length−Time = Speed
        // [1,0,-1]) and divides the magnitudes (1/1 = 1). No `.value`, no explicit `divide` call.
        assertNull(diagnostics(snippet('result == 1.m / 1.s', 'javax.measure.Quantity', 'def s = 1.s; def d = 1.m; d / s')))
    }

    @Test
    void speedFromDivisionWrongMagnitudeRefutes() {
        // Same dimension (Speed), different magnitude: 2 m / 1 s is 2 m/s, not 1 m/s — refutes on magnitude.
        String d = diagnostics(snippet('result == 1.m / 1.s', 'javax.measure.Quantity', 'def s = 1.s; def d = 2.m; d / s'))
        assertTrue(d?.contains('Cannot prove postcondition'), "expected refutation, got: $d")
    }

    @Test
    void speedAsLengthDimensionRefutes() {
        // A speed claimed as a length: `1.m / 1.s` is [1,0,-1], `1.m` is [1,0,0] — different dimensions, never equal,
        // so the contract refutes *on the dimension*. The dual of the area case, via division.
        String d = diagnostics(snippet('result == 1.m', 'javax.measure.Quantity', '1.m / 1.s'))
        assertTrue(d?.contains('Cannot prove postcondition'), "expected refutation, got: $d")
    }

    @Test
    void nonTerminatingDivisorSkips() {
        // Soundness boundary (Phase 143 posture): `1.m / 3.s` has SI magnitude 1/3, which Groovy/indriya *round* —
        // the exact Real model would disagree (and a multiply-back could then "verify" a runtime-false fact). The
        // dimension is fine (Speed), but the magnitude is non-terminating, so the comparison skips loudly.
        String d = diagnostics(snippet('result == 1.m / 3.s', 'javax.measure.Quantity', '1.m / 3.s'))
        assertTrue(d?.contains('Skipped verification') || d?.contains('outside fragment'),
            "expected a loud skip for a non-terminating divisor, got: $d")
    }
}
