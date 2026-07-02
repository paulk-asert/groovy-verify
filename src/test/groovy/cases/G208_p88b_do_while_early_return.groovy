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

/** 'P88b do-while early-return' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G208_p88b_do_while_early_return {

    static final List<Map> CASES = [

        // ---------- do-while early return on the first iteration (Phase 88b — a soundness fix) ----------
        // A do-while runs its body once before the guard/invariant, so an in-body early return can fire on
        // the FIRST iteration from the *entry* state. The exit's @Ensures is now checked from there (no
        // invariant/guard assumed) in addition to the later-iteration (invariant ∧ guard) check.
        // Valid: the guard is false at entry (n==0), yet the body runs once and returns 7 — verifies.
        [group: 'P88b do-while early-return', name: 'iter-1 return, guard false at entry, verifies', ok: true,
         src: tc('''class C {
                        @Requires({ n == 0 })
                        @Ensures({ result == 7 })
                        static int f(int n) {
                            int i = 0
                            @Invariant({ i >= 0 })
                            @Decreases({ n - i })
                            do { if (i == 0) return 7; i = i + 1 } while (i < n)
                            return 7
                        }
                    }''')],
        // Valid: a first-iteration return whose value satisfies the post on every path.
        [group: 'P88b do-while early-return', name: 'iter-1 return value satisfies post', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            do { if (i >= 0) return i; i = i + 1 } while (i < n)
                            return i
                        }
                    }''')],
        // SOUNDNESS (the bug this fixes): the invariant {i==0} is false at entry (i=5); the body returns 5
        // on iter 1, so the post result==0 is FALSE. Pre-fix this *vacuously verified* (the exit check
        // assumed the not-yet-established invariant); now the first-iteration check refutes it.
        [group: 'P88b do-while early-return', name: 'iter-1 return, invariant false at entry, false post refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() {
                            int i = 5
                            @Invariant({ i == 0 })
                            @Decreases({ i })
                            do { if (i == 5) return i; i = i - 1 } while (i > 0)
                            return 0
                        }
                    }''')],
    ]
}
