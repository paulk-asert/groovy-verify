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
 * The fib4 / tetranacci spec helper the verifier recognises in {@code @Requires}/{@code @Ensures}/
 * {@code @Invariant} contracts — the four-term sibling of {@link Trib}, for HumanEval task 046
 * ({@code fib4}):
 *
 * <pre>
 *   {@literal @}Ensures({ result == Tetra.of(n) })
 *   {@literal @}Invariant({ a == Tetra.of(i) {@literal &&} b == Tetra.of(i + 1) {@literal &&}
 *                           c == Tetra.of(i + 2) {@literal &&} d == Tetra.of(i + 3) })
 * </pre>
 *
 * {@code of(i)} is the i-th fib4 number ({@code 0, 0, 2, 0, 2, 4, 8, 14, 28, 54, …}). It stays executable so
 * the groovy-contracts <em>runtime</em> check still works (iteratively, no deep recursion). At compile time
 * {@code Encoder} recognises the {@code Tetra.of(i)} shape and lowers it to an uninterpreted
 * {@code tetra$ : Int -> Int} constrained by its defining axioms — base {@code tetra(0)==0},
 * {@code tetra(1)==0}, {@code tetra(2)==2}, {@code tetra(3)==0} and step
 * {@code ∀k. k>=4 ⟹ tetra(k)==tetra(k-1)+tetra(k-2)+tetra(k-3)+tetra(k-4)} — so a generation loop's invariant
 * {@code d == Tetra.of(i+3)} is preserved by {@code e = a + b + c + d} via the step axiom (a congruence).
 */
@CompileStatic
class Tetra {

    /** The i-th fib4 number, for i &gt;= 0 ({@code of(0)==0, of(1)==0, of(2)==2, of(3)==0, of(4)==2, of(8)==28, …}). */
    static int of(int i) {
        if (i < 2 || i == 3) return 0
        if (i == 2) return 2
        int a = 0, b = 0, c = 2, d = 0   // tetra(0), tetra(1), tetra(2), tetra(3)
        for (int k = 4; k <= i; k++) {
            int t = a + b + c + d
            a = b
            b = c
            c = d
            d = t
        }
        d
    }
}
