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

/**
 * The least-common-multiple spec helper the verifier recognises in {@code @Requires}/{@code @Ensures}/
 * {@code @Invariant} contracts — the multiplicative sibling of {@link Gcd}:
 *
 * <pre>
 *   {@literal @}Ensures({ result == Lcm.of(a, b) })
 * </pre>
 *
 * <p>{@code of(a, b)} divides by the gcd <em>first</em> (the value is exact, since {@code gcd(a, b)} divides
 * {@code a}) to avoid the intermediate overflow of {@code a * b}, so it stays executable and the
 * groovy-contracts <em>runtime</em> check still works. At compile time {@link Encoder} recognises the
 * {@code Lcm.of(a, b)} shape and lowers it to an uninterpreted {@code lcm$ : (Int, Int) -> Int} constrained by
 * the base axioms ({@code ∀a. lcm(a, 0) == 0}, {@code ∀b. lcm(0, b) == 0}) and the fundamental identity
 * {@code ∀a,b. lcm(a, b) * gcd(a, b) == a * b} — so it composes with {@link Gcd}'s Euclid axioms (e.g.
 * {@code Lcm.of(4, 6) == 12} via {@code gcd(4, 6) == 2}, and the identity proves symbolically).
 */
@CompileStatic
class Lcm {

    /** The least common multiple of {@code a} and {@code b}; {@code of(a, 0) == of(0, b) == 0}, {@code of(4, 6) == 12}. */
    static int of(int a, int b) {
        if (a == 0 || b == 0) return 0
        a.intdiv(Gcd.of(a, b)) * b   // divide by the gcd first — exact, and avoids `a * b` overflowing
    }
}
