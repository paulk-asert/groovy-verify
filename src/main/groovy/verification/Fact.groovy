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
 * The factorial spec helper (Phase 203, the math-comp {@code n`!} twin), recognised by
 * {@link CombinatoricsPack} in contracts and lowered to the uninterpreted {@code fact$ : Int -> Int}
 * constrained by base {@code fact(0)==1} and step {@code ∀n. n>=1 ⟹ fact(n)==n*fact(n-1)} (triggered on
 * {@code fact(n)} — the pow$-style guarded product). Stays executable (iteratively) so the
 * groovy-contracts runtime check still works.
 */
@CompileStatic
class Fact {

    /** n! for n &gt;= 0 ({@code of(0)==1, of(3)==6, …}); iterative, int-ranged. */
    static int of(int n) {
        int r = 1
        for (int k = 2; k <= n; k++) r *= k
        r
    }
}
