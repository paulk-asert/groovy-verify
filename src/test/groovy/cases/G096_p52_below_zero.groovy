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
package cases

import static cases.CaseDsl.*

/** 'P52 below_zero' — 1 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G096_p52_below_zero {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'HumanEval 003 below_zero — the full biconditional: result iff some prefix sum is negative.'

    static final List<Map> CASES = [

        // ---------- HumanEval 3 (below_zero): running balance ever negative ----------
        // The FULL biconditional spec — result ⟺ some prefix sum is negative — verifies: the early
        // return witnesses the existential (`any`), and the invariant "no prefix negative so far"
        // (`every`) carries the converse to the `return false` path. Uses `sum(0)` (runtime-safe: 0
        // for the empty prefix, vs `[].sum() == null`) and an `(int)` cast — but NOT for the
        // generics-erasure reason the others had: the seeded GDK `sum(Iterable, initialValue)` overload is
        // declared to return `Object` by signature (unlike the bare `sum()`), so the `< 0` comparison needs
        // it even with GROOVY-12071's restored closure generics. The proof logic is groovy-verify's sum
        // aggregation + bounded ∀/∃.
        [group: 'P52 below_zero', name: 'below_zero full biconditional spec', ok: true,
         src: tc('''class C {
                        @Requires({ operations != null })
                        @Ensures({ result == (0..operations.size()).any { ((int) operations[0..<it].sum(0)) < 0 } })
                        static boolean belowZero(List<Integer> operations) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= operations.size() &&
                                         s == operations[0..<i].sum(0) &&
                                         (0..i).every { ((int) operations[0..<it].sum(0)) >= 0 } })
                            @Decreases({ operations.size() - i })
                            while (i < operations.size()) {
                                s = s + operations[i]
                                if (s < 0) return true
                                i = i + 1
                            }
                            return false
                        }
                    }''')],
    ]
}
