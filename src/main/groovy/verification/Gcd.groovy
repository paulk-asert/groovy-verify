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
 * The greatest-common-divisor spec helper the verifier recognises in {@code @Requires}/{@code @Ensures}/
 * {@code @Invariant} contracts — the two-argument sibling of {@link Fib} (HumanEval task 013
 * {@code greatest_common_divisor}):
 *
 * <pre>
 *   {@literal @}Ensures({ result == Gcd.of(a, b) })
 *   {@literal @}Invariant({ Gcd.of(x, y) == Gcd.of(a, b) })
 * </pre>
 *
 * {@code of(a, b)} is Euclid's algorithm, so it stays executable and the groovy-contracts <em>runtime</em>
 * check still works. At compile time {@code Encoder} recognises the {@code Gcd.of(a, b)} shape and lowers it
 * to an uninterpreted {@code gcd$ : (Int, Int) -> Int} constrained by Euclid's defining axioms — base
 * {@code ∀x. gcd(x, 0) == x} and step {@code ∀x,y. y != 0 ⟹ gcd(x, y) == gcd(y, x % y)} — so a Euclid loop's
 * invariant {@code Gcd.of(x, y) == Gcd.of(a, b)} is preserved by {@code t = x % y; x = y; y = t} via the step
 * axiom (a congruence), and at exit ({@code y == 0}) the base axiom collapses {@code gcd(x, 0)} to {@code x}.
 */
@CompileStatic
class Gcd {

    /** The gcd of {@code a} and {@code b} by Euclid's algorithm; {@code of(a, 0) == a}, so {@code of(12, 8) == 4}. */
    static int of(int a, int b) {
        while (b != 0) {
            int t = a % b
            a = b
            b = t
        }
        a
    }
}
