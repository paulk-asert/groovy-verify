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

/** 'HE042 incr_list' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G250_he042_incr_list {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'HumanEval 042 — element-wise map: build a list whose every element is the input + 1, with a per-element @Ensures over the returned list; forgetting the +1 refutes.'

    static final List<Map> CASES = [

        // ---------- Element-wise list transforms (HumanEval 042 / 152 / 062) — build a list whose every element is a
        // function of the input's; the post-condition is a per-element `every` over the RETURNED list. ----------
        // 042 incr_list: each output is the input + 1.
        [group: 'HE042 incr_list', name: 'every element is the input plus one', ok: true,
         src: tc('''class C {
                        @Requires({ l != null })
                        @Ensures({ result.size() == l.size() && (0..<l.size()).every { result[it] == l[it] + 1 } })
                        static List<Integer> incrList(List<Integer> l) {
                            List<Integer> result = []
                            int index = 0
                            @Invariant({ result != null && 0 <= index && index <= l.size() && result.size() == index &&
                                         (0..<index).every { result[it] == l[it] + 1 } })
                            @Decreases({ l.size() - index })
                            while (index < l.size()) {
                                result.add(l[index] + 1)
                                index = index + 1
                            }
                            return result
                        }
                    }''')],
        // Soundness: claiming the element is the input unchanged (forgetting the +1) refutes.
        [group: 'HE042 incr_list', name: 'forgetting the +1 refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ l != null })
                        @Ensures({ result.size() == l.size() && (0..<l.size()).every { result[it] == l[it] } })
                        static List<Integer> incrList(List<Integer> l) {
                            List<Integer> result = []
                            int index = 0
                            @Invariant({ result != null && 0 <= index && index <= l.size() && result.size() == index &&
                                         (0..<index).every { result[it] == l[it] + 1 } })
                            @Decreases({ l.size() - index })
                            while (index < l.size()) {
                                result.add(l[index] + 1)
                                index = index + 1
                            }
                            return result
                        }
                    }''')],
    ]
}
