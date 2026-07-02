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

/** 'P78 list return' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G102_p78_list_return {

    static final List<Map> CASES = [

        // ---------- Phase 78: list-literal returns + constant-index result[k] ----------
        // A method may now return a list literal and have @Ensures reference its elements by constant
        // index: `result` is bound as a factory container, so result.size()/result[k] fold.
        [group: 'P78 list return', name: 'return [1,2]: result[0]==1 && result[1]==2', ok: true,
         src: tc('''class C {
                        @Ensures({ result[0] == 1 && result[1] == 2 && result.size() == 2 })
                        static List<Integer> pair() { [1, 2] }
                    }''')],
        // The faithful HumanEval 008 (sum_product): return BOTH aggregates as a list, each element proven
        // against its aggregate — what previously had to collapse to `s + p` for lack of tuple/list returns.
        [group: 'P78 list return', name: 'sum_product returns [sum, product]', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result[0] == xs.sum() && result[1] == xs.inject(1) { a, x -> a * x } })
                        static List<Integer> sumProduct(List<Integer> xs) {
                            int s = xs[0]
                            int p = xs[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= xs.size() &&
                                         s == xs[0..<i].sum() &&
                                         p == xs[0..<i].inject(1) { a, x -> a * x } })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                s = s + xs[i]
                                p = p * xs[i]
                                i = i + 1
                            }
                            return [s, p]
                        }
                    }''')],
        // A false element claim refutes (result[1] is 2, not 1).
        [group: 'P78 list return', name: 'return [1,2]: wrong element claim refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result[1] == 1 })
                        static List<Integer> pair() { [1, 2] }
                    }''')],
    ]
}
