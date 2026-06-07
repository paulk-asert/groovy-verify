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
 * The Fibonacci spec helper the verifier recognises in {@code @Requires}/{@code @Ensures}/
 * {@code @Invariant} contracts (roadmap Phase 55):
 *
 * <pre>
 *   {@literal @}Ensures({ result == Fib.of(n) })
 *   {@literal @}Invariant({ a == Fib.of(i) {@literal &&} b == Fib.of(i + 1) })
 * </pre>
 *
 * {@code of(i)} is the i-th Fibonacci number ({@code 0, 1, 1, 2, 3, 5, …}). It stays executable so
 * the groovy-contracts <em>runtime</em> check still works (iteratively, no deep recursion). At compile
 * time {@code Encoder} recognises the {@code Fib.of(i)} shape and lowers it to an uninterpreted
 * {@code fib$ : Int -> Int} constrained by its defining axioms — base {@code fib(0)==0}, {@code fib(1)==1}
 * and step {@code ∀k. k>=2 ⟹ fib(k)==fib(k-1)+fib(k-2)} — so a generation loop's invariant
 * {@code b == Fib.of(i+1)} is preserved by {@code b = a + b} via the step axiom (a congruence).
 *
 * This is the two-term-recurrence sibling of the {@code sum}/{@code prod} aggregations. The
 * <em>outer</em> {@code prime_fib} search is a deliberate non-target — its termination depends on the
 * (open) infinitude of Fibonacci primes — but the Fibonacci generation it rests on verifies.
 */
@CompileStatic
class Fib {

    /** The i-th Fibonacci number, for i &gt;= 0 ({@code of(0)==0, of(1)==1, of(2)==1, of(5)==5, …}). */
    static int of(int i) {
        if (i < 2) return i
        int a = 0, b = 1
        for (int k = 2; k <= i; k++) {
            int t = a + b
            a = b
            b = t
        }
        b
    }
}
