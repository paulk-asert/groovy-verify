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
 * The binomial-coefficient spec helper (Phase 203, the math-comp {@code 'C(n, m)} twin), recognised by
 * {@link CombinatoricsPack} and lowered to the <b>two-argument</b> uninterpreted {@code binom$ :
 * (Int, Int) -> Int} constrained by Pascal's rule — base {@code binom(n,0)==1}, out-of-range
 * {@code k>n ⟹ binom(n,k)==0}, step {@code ∀n,k. n>=1 ∧ k>=1 ⟹ binom(n,k)==binom(n-1,k-1)+binom(n-1,k)}
 * (triggered on {@code binom(n,k)}). The first spec primitive to ride the generic n-ary {@code applyUF}
 * at arity 2. Stays executable (Pascal recursion with the additive rule) for the runtime check.
 */
@CompileStatic
class Binom {

    /** C(n, k) for n,k &gt;= 0 ({@code of(4,2)==6}); 0 when k &gt; n. */
    static int of(int n, int k) {
        if (k < 0 || k > n) return 0
        if (k == 0 || k == n) return 1
        of(n - 1, k - 1) + of(n - 1, k)
    }
}
