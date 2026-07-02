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

/** 'HE062 derivative' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G252_he062_derivative {

    static final List<Map> CASES = [

        // 062 derivative: a polynomial's coefficients [c0, c1, c2, ...] → [c1*1, c2*2, ...] (size n-1). Each output is
        // the next coefficient times its power. Requires a non-empty coefficient list (a polynomial has a constant term).
        [group: 'HE062 derivative', name: 'each output is the coefficient times its power', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() >= 1 })
                        @Ensures({ result.size() == xs.size() - 1 && (0..<result.size()).every { result[it] == xs[it + 1] * (it + 1) } })
                        static List<Integer> derivative(List<Integer> xs) {
                            List<Integer> result = []
                            int i = 1
                            @Invariant({ result != null && 1 <= i && i <= xs.size() && result.size() == i - 1 &&
                                         (0..<result.size()).every { result[it] == xs[it + 1] * (it + 1) } })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                result.add(xs[i] * i)
                                i = i + 1
                            }
                            return result
                        }
                    }''')],
        // Soundness: using the index instead of the power (xs[it+1]*it rather than *(it+1)) refutes — the first term
        // would be multiplied by 0.
        [group: 'HE062 derivative', name: 'wrong power (times index) refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() >= 1 })
                        @Ensures({ result.size() == xs.size() - 1 && (0..<result.size()).every { result[it] == xs[it + 1] * it } })
                        static List<Integer> derivative(List<Integer> xs) {
                            List<Integer> result = []
                            int i = 1
                            @Invariant({ result != null && 1 <= i && i <= xs.size() && result.size() == i - 1 &&
                                         (0..<result.size()).every { result[it] == xs[it + 1] * (it + 1) } })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                result.add(xs[i] * i)
                                i = i + 1
                            }
                            return result
                        }
                    }''')],
    ]
}
