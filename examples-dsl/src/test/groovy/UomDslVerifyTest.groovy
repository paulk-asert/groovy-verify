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
}
