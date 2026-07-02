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

/** 'P88 do-while' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G059_p88_do_while {

    static final List<Map> CASES = [

        // ---------- Phase 88: do..while (body runs once before the first guard/invariant check) ----------
        // `do B while (G)` ≡ `B; while (G) B`. Establishment therefore checks the invariant AFTER the first
        // body, not at entry: the `1 <= i` clause here is FALSE at entry (i=0) but true after one `i++` —
        // so this verifies only with do-while-faithful establishment (Phase 88), and `result == n` follows
        // from the exit `i == n`. Termination on `n - i`.
        [group: 'P88 do-while', name: 'do-while countUp (body-first establishment)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 1 })
                        @Ensures({ result == n })
                        static int countUp(int n) {
                            int i = 0
                            @Invariant({ 1 <= i && i <= n })
                            @Decreases({ n - i })
                            do { i++ } while (i < n)
                            return i
                        }
                    }''')],
        // SOUNDNESS (the bug Phase 88 fixes): at n==0 the body runs once (result is 1), but `@Invariant({i==0})`
        // holds at entry and is vacuously preserved (guard never true), and exit `i==0` would prove the FALSE
        // `result==0`. Treating do-while as while verified this silently; now establishment runs the body once
        // (i=1) and the invariant fails there — correctly rejected, with do-while-aware wording.
        [group: 'P88 do-while', name: 'do-while false invariant rejected (was unsound)',
         expect: "after the do-while's first iteration",
         src: tc('''class C {
                        @Requires({ n == 0 })
                        @Ensures({ result == 0 })
                        static int f(int n) {
                            int i = 0
                            @Invariant({ i == 0 })
                            @Decreases({ n - i })
                            do { i++ } while (i < n)
                            return i
                        }
                    }''')],
        // A wrong postcondition still refutes at the use obligation (exit is i==n, not n+1).
        [group: 'P88 do-while', name: 'do-while wrong postcondition refuted',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ n >= 1 })
                        @Ensures({ result == n + 1 })
                        static int countUp(int n) {
                            int i = 0
                            @Invariant({ 1 <= i && i <= n })
                            @Decreases({ n - i })
                            do { i++ } while (i < n)
                            return i
                        }
                    }''')],
    ]
}
