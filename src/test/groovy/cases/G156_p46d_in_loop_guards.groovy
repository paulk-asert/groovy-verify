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

/** 'P46d in-loop guards' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G156_p46d_in_loop_guards {

    static final List<Map> CASES = [

        // The earlier P37 "in-body if (xs[i] != null) guard verifies" test covered the
        // straight-line case. Phase 46d extends the same path-fact mechanism to the loop body:
        // dischargeRegion recurses into an in-region if-statement, asserting the cond in the
        // then-branch and !cond in the else-branch, then descends through &&/||/ternary
        // operands so the right operand is discharged under the short-circuit guard.
        [group: 'P46d in-loop guards', name: 'in-loop if (xs[i] != null) discharges deref obligation', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        static int f(List<String> xs) {
                            int n = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= xs.size() && n >= 0 })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                if (xs[i] != null) {
                                    n = n + xs[i].length()
                                }
                                i = i + 1
                            }
                            return n
                        }
                    }''')],
        // && short-circuit inside the if-cond — the natural way to write a guarded deref.
        [group: 'P46d in-loop guards', name: 'in-loop && short-circuit discharges deref obligation', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && p != null })
                        static int f(List<String> xs, String p) {
                            int n = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= xs.size() && n >= 0 })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                if (xs[i] != null && xs[i].startsWith(p)) {
                                    n = n + 1
                                }
                                i = i + 1
                            }
                            return n
                        }
                    }''')],
        // Soundness: removing the null guard refutes — the obligation is still real, the
        // path-fact mechanism only DISCHARGES the obligation when the guard establishes it.
        [group: 'P46d in-loop guards', name: 'in-loop unguarded deref refutes',
         expect: 'Possible NullPointerException',
         src: tc('''class C {
                        @Requires({ xs != null })
                        static int f(List<String> xs) {
                            int n = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= xs.size() && n >= 0 })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                n = n + xs[i].length()
                                i = i + 1
                            }
                            return n
                        }
                    }''')],
    ]
}
