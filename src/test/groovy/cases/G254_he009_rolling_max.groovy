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

/** 'HE009 rolling_max' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G254_he009_rolling_max {

    static final List<Map> CASES = [

        // ---------- 009 rolling_max (HumanEval) — the running maximum at each position, as a returned list ----------
        // The full spec (each output is the exact prefix maximum) is a nested forall/exists; here we prove the clean,
        // faithful characterisation it implies — the running max DOMINATES each element and is NON-DECREASING — which
        // the loop invariant carries directly (max_so_far is tied to the last pushed element).
        [group: 'HE009 rolling_max', name: 'running max dominates each element and is non-decreasing', ok: true,
         src: tc('''class C {
                        @Requires({ numbers != null })
                        @Ensures({ result.size() == numbers.size() &&
                                   (0..<numbers.size()).every { numbers[it] <= result[it] } &&
                                   (0..<numbers.size()).every { it == 0 || result[it - 1] <= result[it] } })
                        static List<Integer> rollingMax(List<Integer> numbers) {
                            int maxSoFar = Integer.MIN_VALUE
                            List<Integer> result = []
                            int i = 0
                            @Invariant({ result != null && 0 <= i && i <= numbers.size() && result.size() == i &&
                                         (i == 0 || maxSoFar == result[i - 1]) &&
                                         (0..<i).every { numbers[it] <= result[it] } &&
                                         (0..<i).every { it == 0 || result[it - 1] <= result[it] } })
                            @Decreases({ numbers.size() - i })
                            while (i < numbers.size()) {
                                int number = numbers[i]
                                if (number > maxSoFar) maxSoFar = number
                                result.add(maxSoFar)
                                i = i + 1
                            }
                            return result
                        }
                    }''')],
        // Soundness: returning the input unchanged is not a running max — it fails the non-decreasing clause on any
        // descending input (e.g. [2, 1]). Straight-line, so the refutation is a clean counterexample.
        [group: 'HE009 rolling_max', name: 'returning the input unchanged refutes (not monotone)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ numbers != null })
                        @Ensures({ result.size() == numbers.size() &&
                                   (0..<numbers.size()).every { numbers[it] <= result[it] } &&
                                   (0..<numbers.size()).every { it == 0 || result[it - 1] <= result[it] } })
                        static List<Integer> rollingMax(List<Integer> numbers) {
                            return numbers
                        }
                    }''')],
    ]
}
