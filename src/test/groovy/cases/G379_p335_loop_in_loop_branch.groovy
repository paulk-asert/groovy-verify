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
 * 'P335 loop in a branch of a loop body' — an annotated loop inside an if in a loop body was summarised by its
 * invariant while the outer loop was checked, but verifyNestedLoops saw only the body's top-level loops, so that
 * invariant was never checked (silently unsound until Phase 334 made it loud). Each such loop is now verified as a
 * nested loop entered along its path: the outer body's statements before it with each branch condition assumed
 * (VerifyChecker.branchInnerLoops). The conditions nothing writes are frame facts of the inner loop, in its
 * preservation, progress, returns and body obligations.
 */
class G379_p335_loop_in_loop_branch {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 335 loop in a branch of a loop body: an annotated loop inside an if (or else, or a nested if) in a loop body gets the nested-loop checks: establishment from the outer body along its path with the branch conditions assumed, preservation, progress, its returns against @Ensures, and its body obligations, with the conditions nothing writes held at every iteration. A writing condition (x++) and a loop in a branch of a nested loop skip loudly.'

    static final List<Map> CASES = [

        [group: 'P335 loop in a branch of a loop body', name: 'a loop in a then-branch of a loop body', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n, boolean b) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && s >= 0 })
                            @Decreases({ n - k })
                            while (k < n) {
                                if (b) {
                                    int i = 0
                                    @Invariant({ 0 <= i && i <= n && s >= 0 })
                                    @Decreases({ n - i })
                                    while (i < n) { s = s + 1; i = i + 1 }
                                }
                                k = k + 1
                            }
                            return s
                        }
                    }''')],
        // i = 1 <= a.length holds only under a.length > 0.
        [group: 'P335 loop in a branch of a loop body', name: 'its establishment assumes the branch condition', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && n >= 0 })
                        static void f(int[] a, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                if (a.length > 0) {
                                    int i = 1
                                    @Invariant({ 1 <= i && i <= a.length })
                                    @Decreases({ a.length - i })
                                    while (i < a.length) { a[i] = a[i - 1]; i = i + 1 }
                                }
                                k = k + 1
                            }
                        }
                    }''')],
        [group: 'P335 loop in a branch of a loop body', name: 'a loop in the else branch runs under the negated condition', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        static void f(int n, int m) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                if (m <= 0) {
                                    k = k + 0
                                } else {
                                    int i = 0
                                    @Invariant({ 0 <= i && i <= m })
                                    @Decreases({ m - i })
                                    while (i < m) { i = i + 1 }
                                }
                                k = k + 1
                            }
                        }
                    }''')],
        [group: 'P335 loop in a branch of a loop body', name: 'a loop in an if nested inside a branch of the body', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        static void f(int n, int m, boolean b) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                if (b) {
                                    if (m > 2) {
                                        int i = 2
                                        @Invariant({ 2 <= i && i <= m })
                                        @Decreases({ m - i })
                                        while (i < m) { i = i + 1 }
                                    }
                                }
                                k = k + 1
                            }
                        }
                    }''')],
        [group: 'P335 loop in a branch of a loop body', name: 'the outer loop keeps its invariant through the branch summary', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n, int m, boolean b) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && s >= 0 })
                            @Decreases({ n - k })
                            while (k < n) {
                                if (b) {
                                    int i = 0
                                    @Invariant({ 0 <= i && i <= m && s >= 0 })
                                    @Decreases({ m - i })
                                    while (i < m) { s = s + i; i = i + 1 }
                                } else {
                                    s = s + 1
                                }
                                k = k + 1
                            }
                            return s
                        }
                    }''')],
        // Unsound before Phase 334 (silently proved result == 0, although f(1, true) returns 1), loud in 334, checked now.
        [group: 'P335 loop in a branch of a loop body', name: 'a wrong inner invariant refutes instead of making the outer proof vacuous', expect: ['Cannot prove loop invariant is preserved', 'fails on: f(1, true)'],
         src: tc('''class C {
                        @Requires({ n >= 1 })
                        @Ensures({ result == 0 })
                        static int f(int n, boolean b) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && s == 0 })
                            @Decreases({ n - k })
                            while (k < n) {
                                if (b) {
                                    int i = 0
                                    @Invariant({ 0 <= i && i <= 0 })
                                    @Decreases({ n - i })
                                    while (i < n) { s = s + 1; i = i + 1 }
                                }
                                k = k + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P335 loop in a branch of a loop body', name: 'a broken inner invariant refutes', expect: 'Cannot prove loop invariant is preserved',
         src: tc('''class C {
                        static void f(int n, int m) {
                            int k = 0
                            @Invariant({ 0 <= k })
                            @Decreases({ n - k })
                            while (k < n) {
                                if (m > 0) {
                                    int i = 0
                                    int t = 0
                                    @Invariant({ 0 <= i && t == 0 })
                                    @Decreases({ m - i })
                                    while (i < m) { t = t + 1; i = i + 1 }
                                }
                                k = k + 1
                            }
                        }
                    }''')],
        // The body obligations are discharged under the inner invariant, guard and the branch condition b.
        [group: 'P335 loop in a branch of a loop body', name: 'an out-of-bounds write in the branch loop refutes', expect: ['Possible IndexOutOfBoundsException', 'fails on: f(new int[0], 1, true)'],
         src: tc('''class C {
                        @Requires({ a != null && n >= 0 })
                        static void f(int[] a, int n, boolean b) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                if (b) {
                                    int i = 0
                                    @Invariant({ 0 <= i && i <= a.length + 1 })
                                    @Decreases({ a.length + 1 - i })
                                    while (i <= a.length) { a[i] = 0; i = i + 1 }
                                }
                                k = k + 1
                            }
                        }
                    }''')],
        [group: 'P335 loop in a branch of a loop body', name: 'a return inside the branch loop is checked against @Ensures', expect: ['Cannot prove postcondition', 'fails on: f(3, true)'],
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n, boolean b) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                if (b) {
                                    int i = 0
                                    @Invariant({ 0 <= i && i <= n })
                                    @Decreases({ n - i })
                                    while (i < n) { if (i == 2) return i - 5; i = i + 1 }
                                }
                                k = k + 1
                            }
                            return 0
                        }
                    }''')],
        // m > 0 holds on entry but the loop counts m down, so it is no frame fact.
        [group: 'P335 loop in a branch of a loop body', name: 'a condition the loop writes is not assumed at every iteration', expect: 'Cannot prove loop invariant is preserved',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        static void f(int n, int m) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                if (m > 0) {
                                    int i = 0
                                    @Invariant({ 0 <= i && m > 0 })
                                    @Decreases({ 10 - i })
                                    while (i < 10) { m = m - 1; i = i + 1 }
                                }
                                k = k + 1
                            }
                        }
                    }''')],
        [group: 'P335 loop in a branch of a loop body', name: 'a branch condition that writes skips loudly', expect: 'a branch condition that writes',
         src: tc('''class C {
                        static void f(int n, int x) {
                            int k = 0
                            @Invariant({ 0 <= k })
                            @Decreases({ n - k })
                            while (k < n) {
                                if (x++ > 0) {
                                    int i = 0
                                    @Invariant({ 0 <= i })
                                    @Decreases({ n - i })
                                    while (i < n) { i = i + 1 }
                                }
                                k = k + 1
                            }
                        }
                    }''')],
        // Phase 397 — verified at any depth (it skipped loudly): the innermost `i <= 0` breaks once i reaches 1, f(1, true)
        [group: 'P335 loop in a branch of a loop body', name: 'a loop in a branch of a nested loop is verified',
         expect: ['Cannot prove loop invariant is preserved', 'fails on: f(1, true)'],
         src: tc('''class C {
                        static void f(int n, boolean b) {
                            int k = 0
                            @Invariant({ 0 <= k })
                            @Decreases({ n - k })
                            while (k < n) {
                                int j = 0
                                @Invariant({ 0 <= j })
                                @Decreases({ n - j })
                                while (j < n) {
                                    if (b) {
                                        int i = 0
                                        @Invariant({ 0 <= i && i <= 0 })
                                        @Decreases({ n - i })
                                        while (i < n) { i = i + 1 }
                                    }
                                    j = j + 1
                                }
                                k = k + 1
                            }
                        }
                    }''')],
    ]
}
