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
import org.codehaus.groovy.ast.expr.BinaryExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.PropertyExpression

/**
 * A pluggable <b>domain encoding</b>: recognisers and axioms for a library/domain vocabulary (a spec-helper
 * family, JSR 385 quantities, a time or money library, …), contributed from outside the core encoder. The
 * boundary is principled: <b>packs model library/domain vocabularies; the core models the language</b>
 * (ints, arrays, operators, closures, {@code String} theory stay in the {@code Encoder}).
 *
 * <p>Discovery is via {@link java.util.ServiceLoader} ({@code META-INF/services/verification.EncodingPack}
 * on the compile classpath — the same mechanism that registers the contract transform), applied in
 * name-sorted order at a fixed slot in the encoder's method-call dispatch registry: after the core scalar
 * and aggregation forms, before the collection oracles. Within one pack, dispatch internally.
 *
 * <p>The first pack in tree is {@link NumberTheoryPack} (the {@code Fib}/{@code Trib}/{@code Tetra}/
 * {@code Gcd}/{@code Lcm} spec helpers) — the reference for the shape: a runtime-executable helper class,
 * a recogniser per spelling, defining axioms asserted once per VC via {@link TheoryApi#axiomsOnce}, and a
 * pinned verify/refute case corpus (its groups predate the SPI and double as its regression mesh).
 *
 * <p>This SPI is <b>experimental</b> and minimal by design (call recognisers only); property/operator
 * recognisers, scope collection, normalizer rewrites, and counterexample rendering are the known growth
 * surfaces, to be added when a pack demonstrably needs them.
 */
@CompileStatic
interface EncodingPack {

    /** Stable pack name — used for deterministic (name-sorted) dispatch order and diagnostics. */
    String name()

    /**
     * Try to translate a method call. {@code m} is the method name (non-null), {@code recv} the receiver
     * with any transparent immutability wrapper stripped, {@code args} the flat argument expressions.
     * Return {@link TheoryApi#NO_MATCH} when the guard does not fire, {@code null} for matched-but-
     * untranslatable (aborts the dispatch — a loud skip), else the SMT handle.
     */
    Object translateCall(TheoryApi api, MethodCallExpression mce, String m, Expression recv, List<Expression> args)

    /** Try to translate a property read {@code obj.prop} (same tri-state as {@link #translateCall}).
     *  Dispatched after the core's carrier/record branches, before the JDK-constant folds. */
    default Object translateProperty(TheoryApi api, PropertyExpression pe, Expression obj, String prop) {
        TheoryApi.NO_MATCH
    }

    /** Try to translate a binary expression (same tri-state); {@code opType} is the
     *  {@link org.codehaus.groovy.syntax.Types} operator constant. Dispatched from the core's
     *  binary translator at the domain-comparison slot (before string/numeric handling). */
    default Object translateBinary(TheoryApi api, BinaryExpression be, int opType) {
        TheoryApi.NO_MATCH
    }

    /** True iff {@code e} is a pack-domain value that scalar classifiers must not claim — e.g. a JSR 385
     *  {@code quantity / quantity} is Quantity.divide, not BigDecimal division (so no Real classification
     *  and no divide-by-zero obligation on the divisor). Static context: no {@link TheoryApi} available. */
    default boolean claimsExpression(Expression e) { false }

    /** True iff {@code e} is a construction this pack can model as a named value's source — the checker
     *  then aliases the (scalar-handle-less) name to the expression, which the pack's readers resolve via
     *  {@link TheoryApi#sourceAlias}. */
    default boolean claimsValueSource(TheoryApi api, Expression e) { false }
}
