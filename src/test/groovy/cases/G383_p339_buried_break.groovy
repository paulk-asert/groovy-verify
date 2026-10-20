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
 * 'P339 break inside a non-tail if' — a break was modelled only as a top-level if (c) break / if (c) { lead; break }
 * (or a tail chain's leaf); one buried under another if, or followed by more of its branch, skipped the loop
 * ("unsupported statement BreakStatement", or for a nested loop "a `break` in a nested loop is modelled only as a
 * top-level ..."). ContractExpansionTransform.desugarBreak rewrites it to a flag: brk = false before the if, the
 * break becoming brk = true with the rest of its branch guarded, then if (brk) break. En route: a scalar first written
 * in one branch of an if, unread before it, lost that write in the branch merge (LoopEncoder.iteCombineMap).
 */
class G383_p339_buried_break {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 339 break inside a non-tail if: a break under another if, in an else, or before more statements of its branch, in a top-level or nested loop, is rewritten to a flag and a top-level if (brk) break, so the loop leaves at the same point with the same state (a for loop\'s update skipped, the rest of the branch not run). A labelled break, or one beside a return in a non-tail if, still skips loudly.'

    static final List<Map> CASES = [

        // if (i > 2) { if (s > lim) break; s = s + 1 } becomes brk = false; if (i > 2) { if (s > lim) brk = true else s = s + 1 }; if (brk) break.
        [group: 'P339 break inside a non-tail if', name: 'a break under another if, before more of the body', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n, int lim) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                if (i > 2) {
                                    if (s > lim) break
                                    s = s + 1
                                }
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P339 break inside a non-tail if', name: 'the same inside a nested loop', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n, int m, int lim) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && s >= 0 })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m && s >= 0 })
                                @Decreases({ m - i })
                                while (i < m) {
                                    if (i > 2) {
                                        if (s > lim) break
                                        s = s + 1
                                    }
                                    i = i + 1
                                }
                                k = k + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P339 break inside a non-tail if', name: 'a break in an else branch of a nested loop', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 })
                        static void f(int n, int m) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m })
                                @Decreases({ m - i })
                                while (i < m) {
                                    if (i < 2) { i = i + 1 } else { break }
                                }
                                k = k + 1
                            }
                        }
                    }''')],
        [group: 'P339 break inside a non-tail if', name: 'a break in an else, then more statements', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n, int lim) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                if (s < lim) { s = s + 1 } else { break }
                                s = s * 1
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P339 break inside a non-tail if', name: 'the postcondition holds from the break state', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result <= n })
                        static int f(int n, int lim) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) {
                                if (i > 0) {
                                    if (i == lim) break
                                    i = i + 0
                                }
                                i = i + 1
                            }
                            return i
                        }
                    }''')],
        [group: 'P339 break inside a non-tail if', name: 'a postcondition the break state misses refutes', expect: ['Cannot prove postcondition', 'fails on: f(2, 1)'],
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int f(int n, int lim) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) {
                                if (i > 0) {
                                    if (i == lim) break
                                }
                                i = i + 1
                            }
                            return i
                        }
                    }''')],
        // r = r + 1 sits after the break in its branch: on the breaking iteration r stays i - 1.
        [group: 'P339 break inside a non-tail if', name: 'the rest of the branch after the break does not run', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 3 })
                        @Ensures({ result == 0 })
                        static int f(int n) {
                            int r = -1
                            int i = 0
                            @Invariant({ 0 <= i && i <= 1 && r == i - 1 })
                            @Decreases({ n - i })
                            while (i < n) {
                                if (i >= 0) {
                                    if (i == 1) break
                                    r = r + 1
                                }
                                i = i + 1
                            }
                            return r
                        }
                    }''')],
        [group: 'P339 break inside a non-tail if', name: 'a buried break skips a for loop\'s update', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 3 })
                        @Ensures({ result == 1 })
                        static int f(int n) {
                            int r = -1
                            @Invariant({ 0 <= i && i <= n && i <= 1 })
                            @Decreases({ n - i })
                            for (int i = 0; i < n; i++) {
                                if (i >= 0) {
                                    if (i == 1) { r = i; break }
                                }
                            }
                            return r
                        }
                    }''')],
        // r = i in a nested if, unread before it: the branch merge dropped the write (r read as its free value), so r == 1 at the break did not prove.
        [group: 'P339 break inside a non-tail if', name: 'a write in an if before the exit reaches the break state', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 3 })
                        @Ensures({ result == 1 })
                        static int f(int n) {
                            int r = -1
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && i <= 1 })
                            @Decreases({ n - i })
                            while (i < n) {
                                if (i >= 0) { if (i == 1) { r = i } }
                                if (i == 1) break
                                i = i + 1
                            }
                            return r
                        }
                    }''')],
        // Each row stops at i == 2, so s is 2 per row, not m.
        [group: 'P339 break inside a non-tail if', name: 'an inner loop\'s break state reaches the outer loop', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ n >= 1 && m >= 3 })
                        @Ensures({ result == n * m })
                        static int f(int n, int m) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m })
                                @Decreases({ m - i })
                                while (i < m) {
                                    if (i >= 0) {
                                        if (i == 2) break
                                        s = s + 1
                                    }
                                    i = i + 1
                                }
                                k = k + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P339 break inside a non-tail if', name: 'a labelled break still skips loudly', expect: 'Skipped loop verification',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        static void f(int n) {
                            int i = 0
                            outer:
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) {
                                if (i > 1) { if (i == 3) break outer }
                                i = i + 1
                            }
                        }
                    }''')],
    ]
}
