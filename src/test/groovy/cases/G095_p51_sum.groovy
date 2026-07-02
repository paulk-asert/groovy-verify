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

/** 'P51 sum' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G095_p51_sum {

    static final List<Map> CASES = [

        // ---------- Phase 51: numeric sum aggregation over an Int list (xs[lo..<hi].sum()) ----------
        [group: 'P51 sum', name: 'range sum unfolds to elements', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() >= 2 })
                        @Ensures({ xs[0..<2].sum() == xs[0] + xs[1] })
                        static void f(List<Integer> xs) { }
                    }''')],
        [group: 'P51 sum', name: 'prefix-extension step law holds', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() >= 2 })
                        @Ensures({ xs[0..<2].sum() == xs[0..<1].sum() + xs[1] })
                        static void f(List<Integer> xs) { }
                    }''')],
        // The canonical loop-invariant proof: a running total equals the prefix sum at each step,
        // so the returned value equals the whole-list sum. Non-empty per the GDK `[].sum()==null` limit.
        [group: 'P51 sum', name: 'running total equals list sum', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result == xs.sum() })
                        static int total(List<Integer> xs) {
                            int s = xs[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= xs.size() && s == xs[0..<i].sum() })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                s += xs[i]
                                i++
                            }
                            return s
                        }
                    }''')],
        // Duck-typed String `sum()` IS concatenation (`['a','b','c'].sum() == 'abc'`): a String-element
        // list lowers to the `strConcat$` monoid analogue, and a range sum unfolds to the element concat.
        [group: 'P51 sum', name: 'string-list range sum concatenates', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() >= 2 })
                        @Ensures({ xs[0..<2].sum() == xs[0] + xs[1] })
                        static void f(List<String> xs) { }
                    }''')],
        // The canonical loop-invariant proof, String monoid: a running concatenation equals the
        // whole-list `sum()` (`s == xs[0..<i].sum()` carried across the loop with `str.++`).
        [group: 'P51 sum', name: 'running concatenation equals list sum', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result == xs.sum() })
                        static String concatAll(List<String> xs) {
                            String s = xs[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= xs.size() && s == xs[0..<i].sum() })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                s = s + xs[i]
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
    ]
}
