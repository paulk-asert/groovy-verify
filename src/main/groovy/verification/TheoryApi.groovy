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
import org.codehaus.groovy.ast.expr.ClassExpression
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.PropertyExpression
import org.codehaus.groovy.ast.expr.VariableExpression

/**
 * The curated encoder surface an {@link EncodingPack} programs against — deliberately small, grown
 * demand-driven (the same slice discipline as the engine itself), so packs get a stability contract
 * without the {@code Encoder}'s internals leaking. Implemented by the per-VC {@code Encoder}.
 *
 * <p><b>The tri-state result convention</b> (identical to the encoder's own dispatch registry): a pack's
 * recogniser returns {@link #NO_MATCH} when its guard does not fire (dispatch continues to the next pack
 * and then the built-in handlers), {@code null} when it <i>matched but is honestly untranslatable</i>
 * (the whole dispatch aborts → the obligation surfaces as a loud "outside fragment" skip), or the SMT
 * handle of the translated expression.
 *
 * <p><b>Soundness is the pack's obligation.</b> A pack's lowering and axioms are trusted exactly like the
 * engine's own: the project's definition of done applies — every pack capability needs a verifying case
 * <i>and</i> a refuting twin in the corpus (a wrong lowering that only ever verifies is unsound and
 * invisible). Namespace UF symbols (e.g. {@code fib$}, {@code units$scale}) to avoid colliding with user
 * names and other packs.
 */
@CompileStatic
interface TheoryApi {

    /** The pack-recogniser "my guard did not fire" sentinel — dispatch moves on. Never returned by
     *  {@link #translate}; compare by identity ({@code NO_MATCH.is(r)}). */
    static final Object NO_MATCH = new Object()

    /** The live SMT session: sorts, literals, arithmetic/boolean term builders, {@code assertExpr},
     *  quantifiers, and {@code applyUF(name, args, rangeSort)} — the generic named-UF creator that makes
     *  bespoke per-function backend methods unnecessary. */
    SmtSession getSession()

    /** Phase 209 — the method whose VC this encoder is building (null for bare encoders). Lets a pack
     *  scan the declaring class for statically-visible declarations (e.g. metaclass registrations). */
    MethodNode currentMethod()

    /** Translate a sub-expression in its natural sort; null if outside the fragment. */
    Object translate(Expression e)

    /** Translate a sub-expression coerced into {@code expectedSort}; null if outside the fragment. */
    Object translateInSort(Expression e, Object expectedSort)

    /** Translate a sub-expression as an exact Real (decimal literals, arithmetic, int→real coercion);
     *  null if outside the fragment. */
    Object asRealValue(Expression e)

    /**
     * Mint-once gate for a pack's defining axioms, scoped to this verification condition: returns true the
     * first time {@code key} is seen on this encoder (assert your axioms then), false afterwards. The
     * per-VC scope matches the engine's own primitives (each VC is a fresh solver context).
     */
    boolean axiomsOnce(String key)

    /**
     * The expression a (scalar-handle-less) name was aliased to by the checker — a pack-domain value's
     * construction, registered when the pack's {@code claimsValueSource} accepted it (e.g. a JSR 385
     * Quantity local's RHS, or a Quantity-returning method's return expression bound to {@code result}).
     * Null when the name carries no alias. Per-VC, like every encoder binding.
     */
    Expression sourceAlias(String name)

    /** A BigDecimal/Double/Float as an SMT rational numeral string ({@code "25/10"} for {@code 2.5G}) —
     *  the exact-Real literal format {@link SmtSession#realLit} consumes. */
    static String rationalOf(Object value) {
        BigDecimal bd = (value instanceof BigDecimal) ? (BigDecimal) value : new BigDecimal(value.toString())
        bd = bd.stripTrailingZeros()
        int scale = bd.scale()
        if (scale <= 0) {
            return bd.unscaledValue().multiply(BigInteger.TEN.pow(-scale)).toString()
        }
        return bd.unscaledValue().toString() + '/' + BigInteger.TEN.pow(scale).toString()
    }

    /**
     * True iff {@code recv} denotes the class named {@code simpleName} in any of the three spellings a
     * static-helper receiver reaches the encoder in: an unresolved bare import
     * ({@code VariableExpression}), an FQN path in a re-parsed contract ({@code PropertyExpression}), or a
     * resolved {@code ClassExpression} in body code.
     */
    static boolean receiverIsClass(Expression recv, String simpleName) {
        (recv instanceof VariableExpression && ((VariableExpression) recv).name == simpleName) ||
        (recv instanceof PropertyExpression && ((PropertyExpression) recv).propertyAsString == simpleName) ||
        (recv instanceof ClassExpression && ((ClassExpression) recv).type?.nameWithoutPackage == simpleName)
    }
}
