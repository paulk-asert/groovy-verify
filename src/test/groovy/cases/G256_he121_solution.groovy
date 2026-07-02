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

/** 'HE121 solution' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G256_he121_solution {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'HumanEval 121 — conditional accumulator: summing the odd-valued elements at even indices over a non-negative list stays >= 0 (a sign invariant); a strict > 0 claim refutes since the sum can be zero.'

    static final List<Map> CASES = [

        // 121 sums the ODD-valued elements at EVEN indices — the parity of THAT sum varies (it tracks how many odds were
        // added), so the clean invariant here is a SIGN one: over a non-negative list, the conditional sum stays >= 0.
        [group: 'HE121 solution', name: 'conditional sum over a non-negative list is non-negative', ok: true,
         src: tc('''class C {
                        @Requires({ lst != null && (0..<lst.size()).every { lst[it] >= 0 } })
                        @Ensures({ result >= 0 })
                        static int solution(List<Integer> lst) {
                            int sum = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= lst.size() && sum >= 0 && (0..<lst.size()).every { lst[it] >= 0 } })
                            @Decreases({ lst.size() - i })
                            while (i < lst.size()) {
                                if (i % 2 == 0 && lst[i] % 2 != 0) {
                                    sum = sum + lst[i]
                                }
                                i = i + 1
                            }
                            return sum
                        }
                    }''')],
        // Soundness: the sum can be exactly 0 (an empty list, or no odd element at an even index), so a STRICT `> 0`
        // claim is not provable — refutes.
        [group: 'HE121 solution', name: 'strict positivity refutes (the sum can be zero)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ lst != null && (0..<lst.size()).every { lst[it] >= 0 } })
                        @Ensures({ result > 0 })
                        static int solution(List<Integer> lst) {
                            int sum = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= lst.size() && sum >= 0 && (0..<lst.size()).every { lst[it] >= 0 } })
                            @Decreases({ lst.size() - i })
                            while (i < lst.size()) {
                                if (i % 2 == 0 && lst[i] % 2 != 0) {
                                    sum = sum + lst[i]
                                }
                                i = i + 1
                            }
                            return sum
                        }
                    }''')],
    ]
}
