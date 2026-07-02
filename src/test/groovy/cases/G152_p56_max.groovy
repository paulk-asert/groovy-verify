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

/** 'P56 max' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G152_p56_max {

    static final List<Map> CASES = [

        // ---------- HumanEval 35 (max_element): the witnessed extremum ----------
        // The spec is BOTH universal and existential: the result is >= every element AND is *equal to*
        // one of them (the "witness"). The invariant carries both as the running max grows.
        [group: 'P56 max', name: 'max_element is a witnessed extremum', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ (0..<a.length).every { a[it] <= result } &&
                                   (0..<a.length).any { a[it] == result } })
                        static int maxElement(int[] a) {
                            int m = a[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= a.length &&
                                         (0..<i).every { a[it] <= m } &&
                                         (0..<i).any { a[it] == m } })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] > m) m = a[i]
                                i = i + 1
                            }
                            return m
                        }
                    }''')],
        // min — the symmetric witnessed extremum (result <= every element, and is one of them).
        [group: 'P56 max', name: 'min_element is a witnessed extremum', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ (0..<a.length).every { result <= a[it] } &&
                                   (0..<a.length).any { a[it] == result } })
                        static int minElement(int[] a) {
                            int m = a[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= a.length &&
                                         (0..<i).every { m <= a[it] } &&
                                         (0..<i).any { a[it] == m } })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] < m) m = a[i]
                                i = i + 1
                            }
                            return m
                        }
                    }''')],
        // Soundness anchor: returning the first element isn't the max — the universal clause refutes
        // (some later element can exceed it). The existential witness alone isn't enough.
        [group: 'P56 max', name: 'returning a[0] is not the max (refutes)',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ (0..<a.length).every { a[it] <= result } &&
                                   (0..<a.length).any { a[it] == result } })
                        static int badMax(int[] a) { a[0] }
                    }''')],
    ]
}
