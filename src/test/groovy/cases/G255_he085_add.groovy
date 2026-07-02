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

/** 'HE085 add' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G255_he085_add {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'HumanEval 085 — conditional accumulator: summing the even-valued elements at odd indices keeps the running sum even (a parity invariant); claiming the sum is odd refutes.'

    static final List<Map> CASES = [

        // ---------- 085 add / 121 solution (HumanEval) — a CONDITIONAL accumulator: sum a selected subset ----------
        // 085 sums the EVEN-valued elements at ODD indices. A subset-sum has no clean `sum$` spelling, but the elements
        // summed are all even, so the running sum stays even — a parity invariant the loop carries (sum % 2 == 0).
        [group: 'HE085 add', name: 'sum of even elements is even', ok: true,
         src: tc('''class C {
                        @Requires({ lst != null })
                        @Ensures({ result % 2 == 0 })
                        static int add(List<Integer> lst) {
                            int sum = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= lst.size() && sum % 2 == 0 })
                            @Decreases({ lst.size() - i })
                            while (i < lst.size()) {
                                if (i % 2 == 1 && lst[i] % 2 == 0) {
                                    sum = sum + lst[i]
                                }
                                i = i + 1
                            }
                            return sum
                        }
                    }''')],
        // Soundness: claiming the sum is ODD contradicts the parity invariant — refutes.
        [group: 'HE085 add', name: 'claiming the sum is odd refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ lst != null })
                        @Ensures({ result % 2 == 1 })
                        static int add(List<Integer> lst) {
                            int sum = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= lst.size() && sum % 2 == 0 })
                            @Decreases({ lst.size() - i })
                            while (i < lst.size()) {
                                if (i % 2 == 1 && lst[i] % 2 == 0) {
                                    sum = sum + lst[i]
                                }
                                i = i + 1
                            }
                            return sum
                        }
                    }''')],
    ]
}
