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

/**
 * 'P344 break or continue before a nested loop' — desugarContinue and the break flag refused a rewrite that would put a
 * nested loop in a branch (nested loops were verified only at a body's top level, before Phase 335), and the walk to a
 * nested loop refused a top-level exit before it. Now the continue/break flag guards the loop with if (flag) {} else,
 * and an exit before the loop is the assumption it wasn't taken. En route: LoopEncoder.applyIf assumed what a branch
 * assumes (a nested loop's summary, an assert) on both paths; each branch now runs under its condition.
 */
class G388_p344_exit_before_nested_loop {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 344 break or continue before a nested loop: a continue or a buried break in an if that a nested loop follows goes through its flag, so the loop lands in the else of if (flag) {} else, a loop in a branch of a loop body; a top-level break or return before a nested loop is, on the way to it, the assumption that it was not taken. Fixed (unsound before): a nested loop or an assert in one branch of a loop body was assumed on the other path too. Nesting three deep still skips loudly.'

    static final List<Map> CASES = [

        // if (k == 0) continue ahead of a nested loop: the continue is a flag, and the nested loop moves into the else of if (cont) {} else, a loop in a branch of a loop body (Phase 335).
        [group: 'P344 break or continue before a nested loop', name: 'a continue before a nested loop', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 1 && m >= 0 })
                        @Ensures({ result == n - 1 })
                        static int f(int n, int m) {
                            int c = 0
                            @Invariant({ 0 <= k && k <= n && c == (k == 0 ? 0 : k - 1) })
                            @Decreases({ n - k })
                            for (int k = 0; k < n; k++) {
                                if (k == 0) continue
                                int i = 0
                                @Invariant({ 0 <= i && i <= m })
                                @Decreases({ m - i })
                                while (i < m) {
                                    i = i + 1
                                }
                                c = c + 1
                            }
                            return c
                        }
                    }''')],
        [group: 'P344 break or continue before a nested loop', name: 'a wrong count past the continue refutes', expect: ['Cannot prove postcondition', 'fails on: f(1, 0)'],
         src: tc('''class C {
                        @Requires({ n >= 1 && m >= 0 })
                        @Ensures({ result == n })
                        static int f(int n, int m) {
                            int c = 0
                            @Invariant({ 0 <= k && k <= n && c == (k == 0 ? 0 : k - 1) })
                            @Decreases({ n - k })
                            for (int k = 0; k < n; k++) {
                                if (k == 0) continue
                                int i = 0
                                @Invariant({ 0 <= i && i <= m })
                                @Decreases({ m - i })
                                while (i < m) {
                                    i = i + 1
                                }
                                c = c + 1
                            }
                            return c
                        }
                    }''')],
        [group: 'P344 break or continue before a nested loop', name: 'the continuing iteration skips the nested loop', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 1 && m >= 0 })
                        @Ensures({ result == (n - 1) * m })
                        static int f(int n, int m) {
                            int s = 0
                            @Invariant({ 0 <= k && k <= n && s == (k == 0 ? 0 : (k - 1) * m) })
                            @Decreases({ n - k })
                            for (int k = 0; k < n; k++) {
                                if (k == 0) continue
                                int i = 0
                                @Invariant({ 0 <= i && i <= m && s == (k - 1) * m + i })
                                @Decreases({ m - i })
                                while (i < m) {
                                    s = s + 1
                                    i = i + 1
                                }
                            }
                            return s
                        }
                    }''')],
        // Phase 384: any failing call (`f(2, 1)` or `f(1, 2)`, both genuine — row 0 is skipped): which one the model
        // gives varies with the solver budget, which Phase 383 scales with the machine's load.
        [group: 'P344 break or continue before a nested loop', name: 'a claim as if the skipped row ran refutes', expect: ['Cannot prove postcondition', 'fails on: f('],
         src: tc('''class C {
                        @Requires({ n >= 1 && m >= 0 })
                        @Ensures({ result == n * m })
                        static int f(int n, int m) {
                            int s = 0
                            @Invariant({ 0 <= k && k <= n && s == (k == 0 ? 0 : (k - 1) * m) })
                            @Decreases({ n - k })
                            for (int k = 0; k < n; k++) {
                                if (k == 0) continue
                                int i = 0
                                @Invariant({ 0 <= i && i <= m && s == (k - 1) * m + i })
                                @Decreases({ m - i })
                                while (i < m) {
                                    s = s + 1
                                    i = i + 1
                                }
                            }
                            return s
                        }
                    }''')],
        [group: 'P344 break or continue before a nested loop', name: 'a continue nested in an if, before a nested loop', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n, int m, int lim) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && s >= 0 })
                            @Decreases({ n - k })
                            while (k < n) {
                                k = k + 1
                                if (k > 2) {
                                    if (s > lim) continue
                                    s = s + 1
                                }
                                int i = 0
                                @Invariant({ 0 <= i && i <= m && s >= 0 })
                                @Decreases({ m - i })
                                while (i < m) {
                                    s = s + 1
                                    i = i + 1
                                }
                            }
                            return s
                        }
                    }''')],
        [group: 'P344 break or continue before a nested loop', name: 'a continue before a nested loop, then a break', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n, int m, int lim) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && s >= 0 })
                            @Decreases({ n - k })
                            while (k < n) {
                                k = k + 1
                                if (k == 2) continue
                                int i = 0
                                @Invariant({ 0 <= i && i <= m && s >= 0 })
                                @Decreases({ m - i })
                                while (i < m) {
                                    s = s + 1
                                    i = i + 1
                                }
                                if (s > lim) break
                            }
                            return s
                        }
                    }''')],
        [group: 'P344 break or continue before a nested loop', name: 'a buried break before a nested loop in its branch', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 1 && m >= 0 })
                        @Ensures({ result == m })
                        static int f(int n, int m) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= 1 && k <= n && s == k * m })
                            @Decreases({ n - k })
                            while (k < n) {
                                k = k + 1
                                if (k > 0) {
                                    if (k == 2) break
                                    int i = 0
                                    @Invariant({ 0 <= i && i <= m && k == 1 && s == i })
                                    @Decreases({ m - i })
                                    while (i < m) {
                                        s = s + 1
                                        i = i + 1
                                    }
                                }
                            }
                            return s
                        }
                    }''')],
        // Only the break leaves (n >= 2), at k == 2 with s == m: the nested loop did not run on that iteration.
        [group: 'P344 break or continue before a nested loop', name: 'a claim as if the nested loop ran on the breaking iteration refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ n >= 2 && m >= 0 })
                        @Ensures({ result == 2 * m })
                        static int f(int n, int m) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= 1 && k <= n && s == k * m })
                            @Decreases({ n - k })
                            while (k < n) {
                                k = k + 1
                                if (k > 0) {
                                    if (k == 2) break
                                    int i = 0
                                    @Invariant({ 0 <= i && i <= m && k == 1 && s == i })
                                    @Decreases({ m - i })
                                    while (i < m) {
                                        s = s + 1
                                        i = i + 1
                                    }
                                }
                            }
                            return s
                        }
                    }''')],
        // The walk to the nested loop meets if (k == 2) break: reaching the loop means it was not taken.
        [group: 'P344 break or continue before a nested loop', name: 'a top-level break before a nested loop', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 1 && m >= 0 })
                        @Ensures({ result == m })
                        static int f(int n, int m) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= 1 && k <= n && s == k * m })
                            @Decreases({ n - k })
                            while (k < n) {
                                k = k + 1
                                if (k == 2) break
                                int i = 0
                                @Invariant({ 0 <= i && i <= m && k == 1 && s == i })
                                @Decreases({ m - i })
                                while (i < m) {
                                    s = s + 1
                                    i = i + 1
                                }
                            }
                            return s
                        }
                    }''')],
        [group: 'P344 break or continue before a nested loop', name: 'a return before a nested loop', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 1 && m >= 0 })
                        @Ensures({ result == m })
                        static int f(int n, int m) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= 1 && k <= n && s == k * m })
                            @Decreases({ n - k })
                            while (k < n) {
                                k = k + 1
                                if (k == 2) return s
                                int i = 0
                                @Invariant({ 0 <= i && i <= m && k == 1 && s == i })
                                @Decreases({ m - i })
                                while (i < m) {
                                    s = s + 1
                                    i = i + 1
                                }
                            }
                            return s
                        }
                    }''')],
        [group: 'P344 break or continue before a nested loop', name: 'a wrong claim at that return refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ n >= 2 && m >= 0 })
                        @Ensures({ result == 2 * m })
                        static int f(int n, int m) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= 1 && k <= n && s == k * m })
                            @Decreases({ n - k })
                            while (k < n) {
                                k = k + 1
                                if (k == 2) return s
                                int i = 0
                                @Invariant({ 0 <= i && i <= m && k == 1 && s == i })
                                @Decreases({ m - i })
                                while (i < m) {
                                    s = s + 1
                                    i = i + 1
                                }
                            }
                            return s
                        }
                    }''')],
        // Unsound before: the nested loop's inv && !guard (k == 1) was assumed on the else path too, so s = -5 kept s >= 0.
        [group: 'P344 break or continue before a nested loop', name: 'fixed: a loop in one branch no longer makes the other vacuous', expect: ['Cannot prove loop invariant is preserved', 'fails on: f(2, 1)'],
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n, int m) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && s >= 0 })
                            @Decreases({ n - k })
                            while (k < n) {
                                k = k + 1
                                if (k == 1) {
                                    int i = 0
                                    @Invariant({ 0 <= i && i <= m && k == 1 })
                                    @Decreases({ m - i })
                                    while (i < m) {
                                        i = i + 1
                                    }
                                } else {
                                    s = -5
                                }
                            }
                            return s
                        }
                    }''')],
        [group: 'P344 break or continue before a nested loop', name: 'fixed: an assert in one branch is not assumed on the other', expect: ['Cannot prove loop invariant is preserved', 'fails on: f(2)'],
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && s >= 0 })
                            @Decreases({ n - k })
                            while (k < n) {
                                k = k + 1
                                if (k == 1) {
                                    assert k == 1
                                } else {
                                    s = -5
                                }
                            }
                            return s
                        }
                    }''')],
        [group: 'P344 break or continue before a nested loop', name: 'a continue before a loop nested three deep still skips loudly', expect: 'loops nested 3+ deep',
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n, int m) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && s >= 0 })
                            @Decreases({ n - k })
                            while (k < n) {
                                k = k + 1
                                int j = 0
                                @Invariant({ 0 <= j && j <= m && s >= 0 })
                                @Decreases({ m - j })
                                while (j < m) {
                                    j = j + 1
                                    if (j == 1) continue
                                    int i = 0
                                    @Invariant({ 0 <= i && i <= m && s >= 0 })
                                    @Decreases({ m - i })
                                    while (i < m) {
                                        s = s + 1
                                        i = i + 1
                                    }
                                }
                            }
                            return s
                        }
                    }''')],
    ]
}
