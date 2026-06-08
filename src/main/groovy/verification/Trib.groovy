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
 * The tribonacci spec helper the verifier recognises in {@code @Requires}/{@code @Ensures}/
 * {@code @Invariant} contracts — the three-term sibling of {@link Fib}, for HumanEval task 063
 * ({@code fibfib}):
 *
 * <pre>
 *   {@literal @}Ensures({ result == Trib.of(n) })
 *   {@literal @}Invariant({ a == Trib.of(i) {@literal &&} b == Trib.of(i + 1) {@literal &&} c == Trib.of(i + 2) })
 * </pre>
 *
 * {@code of(i)} is the i-th {@code fibfib} number ({@code 0, 0, 1, 1, 2, 4, 7, 13, 24, …}). It stays
 * executable so the groovy-contracts <em>runtime</em> check still works (iteratively, no deep recursion).
 * At compile time {@code Encoder} recognises the {@code Trib.of(i)} shape and lowers it to an uninterpreted
 * {@code trib$ : Int -> Int} constrained by its defining axioms — base {@code trib(0)==0},
 * {@code trib(1)==0}, {@code trib(2)==1} and step {@code ∀k. k>=3 ⟹ trib(k)==trib(k-1)+trib(k-2)+trib(k-3)}
 * — so a generation loop's invariant {@code c == Trib.of(i+2)} is preserved by {@code c = a + b + c} via
 * the step axiom (a congruence).
 */
@CompileStatic
class Trib {

    /** The i-th fibfib number, for i &gt;= 0 ({@code of(0)==0, of(1)==0, of(2)==1, of(5)==4, of(8)==24, …}). */
    static int of(int i) {
        if (i < 2) return 0
        if (i == 2) return 1
        int a = 0, b = 0, c = 1   // trib(0), trib(1), trib(2)
        for (int k = 3; k <= i; k++) {
            int t = a + b + c
            a = b
            b = c
            c = t
        }
        c
    }
}
