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
 * 'P334 loop inside a branch' — a top-level if whose branch holds an annotated loop skipped the whole method ("unsupported
 * statement WhileStatement"). The method body now splits at that if into one body per branch: the statements before
 * it, the branch condition (or its negation) as an assume-only assert, the branch's statements, then the rest. Each
 * is verified as a method body of its own (VerifyChecker.branchLoopVariants), so the loop sits at the top level of
 * one of them; together they cover every path. The condition is also a frame fact of the loop when nothing writes
 * what it reads, so in-loop refutations get repros that take the branch. A loop inside a branch of a loop body is
 * Phase 335 (G379).
 */
class G378_p334_loop_in_branch {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 334 loop inside a branch: an annotated loop inside a branch of a top-level if (or else-if chain, or an if nested in a branch) is verified. The method splits into one body per branch, with the branch condition assumed, so each loop is checked at the top level of its body, under the condition, with the other branches checked as loop-free code. Its counterexamples take the branch. A condition that writes (x++) is not split. A loop inside a branch of a loop body is Phase 335.'

    static final List<Map> CASES = [

        // The then-branch runs the loop, the missing else leaves s alone; each is verified as its own body.
        [group: 'P334 loop inside a branch', name: 'an annotated loop in a then-branch with no else', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n, boolean b) {
                            int s = 0
                            if (b) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s >= 0 })
                                @Decreases({ n - i })
                                while (i < n) { s = s + i; i = i + 1 }
                            }
                            return s
                        }
                    }''')],
        [group: 'P334 loop inside a branch', name: 'a postcondition the branch loop misses refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 1 })
                        static int f(int n, boolean b) {
                            int s = 0
                            if (b) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s >= 0 })
                                @Decreases({ n - i })
                                while (i < n) { s = s + i; i = i + 1 }
                            }
                            return s
                        }
                    }''')],
        // The else branch runs under !(n > 0), so s = -n is non-negative.
        [group: 'P334 loop inside a branch', name: 'the else branch is checked with the condition false', ok: true,
         src: tc('''class C {
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            if (n > 0) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s == i })
                                @Decreases({ n - i })
                                while (i < n) { s = s + 1; i = i + 1 }
                            } else {
                                s = -n
                            }
                            return s
                        }
                    }''')],
        [group: 'P334 loop inside a branch', name: 'a search loop in the else branch returns from inside', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= -1 && result < a.length })
                        static int f(int[] a, int x) {
                            if (a.length == 0) {
                                return -1
                            } else {
                                int i = 0
                                @Invariant({ 0 <= i && i <= a.length })
                                @Decreases({ a.length - i })
                                while (i < a.length) { if (a[i] == x) return i; i = i + 1 }
                            }
                            return -1
                        }
                    }''')],
        // i = 1 <= n holds only because the loop runs under n > 0.
        [group: 'P334 loop inside a branch', name: 'establishment assumes the branch condition', ok: true,
         src: tc('''class C {
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            if (n > 0) {
                                int i = 1
                                @Invariant({ 1 <= i && i <= n && s >= 0 })
                                @Decreases({ n - i })
                                while (i < n) { s = s + i; i = i + 1 }
                            }
                            return s
                        }
                    }''')],
        [group: 'P334 loop inside a branch', name: 'establishment fails when the branch condition is too weak', expect: 'Cannot prove loop invariant holds on entry',
         src: tc('''class C {
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            if (n > -5) {
                                int i = 1
                                @Invariant({ 1 <= i && i <= n && s >= 0 })
                                @Decreases({ n - i })
                                while (i < n) { s = s + i; i = i + 1 }
                            }
                            return s
                        }
                    }''')],
        // The condition b is a frame fact of the loop (nothing writes it), so the repro takes the branch.
        [group: 'P334 loop inside a branch', name: 'a broken invariant refutes with a repro that enters the branch', expect: ['Cannot prove loop invariant is preserved', 'fails on: f(1, true)'],
         src: tc('''class C {
                        static int f(int n, boolean b) {
                            int s = 0
                            if (b) {
                                int i = 0
                                @Invariant({ 0 <= i && s == 0 })
                                @Decreases({ n - i })
                                while (i < n) { s = s + 1; i = i + 1 }
                            }
                            return s
                        }
                    }''')],
        [group: 'P334 loop inside a branch', name: 'an out-of-bounds write in a branch loop refutes', expect: ['Possible IndexOutOfBoundsException', 'fails on: f(new int[0], true)'],
         src: tc('''class C {
                        @Requires({ a != null })
                        static void f(int[] a, boolean b) {
                            if (b) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= a.length + 1 })
                                @Decreases({ a.length + 1 - i })
                                while (i <= a.length) { a[i] = 0; i = i + 1 }
                            }
                        }
                    }''')],
        // Split again per branch: three bodies, each with at most one loop.
        [group: 'P334 loop inside a branch', name: 'an else-if chain with a loop in two branches', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n, int mode) {
                            int s = 0
                            if (mode == 1) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s == i })
                                @Decreases({ n - i })
                                while (i < n) { s = s + 1; i = i + 1 }
                            } else if (mode == 2) {
                                int j = 0
                                @Invariant({ 0 <= j && j <= n && s == 2 * j })
                                @Decreases({ n - j })
                                while (j < n) { s = s + 2; j = j + 1 }
                            } else {
                                s = 7
                            }
                            return s
                        }
                    }''')],
        [group: 'P334 loop inside a branch', name: 'the loop-free arm of a chain is checked too', expect: ['Cannot prove postcondition', 'fails on: f(0, 2)'],
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n, int mode) {
                            int s = 0
                            if (mode == 1) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s == i })
                                @Decreases({ n - i })
                                while (i < n) { s = s + 1; i = i + 1 }
                            } else if (mode == 2) {
                                s = -1
                            }
                            return s
                        }
                    }''')],
        [group: 'P334 loop inside a branch', name: 'a branch loop followed by a top-level loop', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n, boolean b) {
                            int s = 0
                            if (b) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s >= 0 })
                                @Decreases({ n - i })
                                while (i < n) { s = s + i; i = i + 1 }
                            }
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && s >= 0 })
                            @Decreases({ n - k })
                            while (k < n) { s = s + 1; k = k + 1 }
                            return s
                        }
                    }''')],
        [group: 'P334 loop inside a branch', name: 'an else that returns early and a loop with an in-body return', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 })
                        static int f(int[] a) {
                            int s = 0
                            if (a.length > 0) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= a.length && s >= 0 })
                                @Decreases({ a.length - i })
                                while (i < a.length) { if (a[i] < 0) return 0; s = s + a[i]; i = i + 1 }
                            } else {
                                return 0
                            }
                            return s
                        }
                    }''')],
        [group: 'P334 loop inside a branch', name: 'a loop in an if nested inside a branch', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n, boolean b, boolean c) {
                            int s = 0
                            if (b) {
                                s = 1
                                if (c) {
                                    int i = 0
                                    @Invariant({ 0 <= i && i <= n && s >= 1 })
                                    @Decreases({ n - i })
                                    while (i < n) { s = s + i; i = i + 1 }
                                }
                                s = s - 1
                            }
                            return s
                        }
                    }''')],
        // The earlier loop is summarised in both bodies; its exit fact s == n reaches the later loop.
        [group: 'P334 loop inside a branch', name: 'a top-level loop followed by a branch loop', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= n })
                        static int f(int n, boolean b) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && s == k })
                            @Decreases({ n - k })
                            while (k < n) { s = s + 1; k = k + 1 }
                            if (b) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s >= n })
                                @Decreases({ n - i })
                                while (i < n) { s = s + i; i = i + 1 }
                            }
                            return s
                        }
                    }''')],
        [group: 'P334 loop inside a branch', name: 'a wrong claim after a top-level loop and a branch loop refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result > n })
                        static int f(int n, boolean b) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && s == k })
                            @Decreases({ n - k })
                            while (k < n) { s = s + 1; k = k + 1 }
                            if (b) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s >= n })
                                @Decreases({ n - i })
                                while (i < n) { s = s + i; i = i + 1 }
                            }
                            return s
                        }
                    }''')],
        [group: 'P334 loop inside a branch', name: 'the branch skipped leaves its loop out of the result', expect: ['Cannot prove postcondition', 'fails on: f(1, false)'],
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int f(int n, boolean b) {
                            int s = 0
                            if (b) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s == i })
                                @Decreases({ n - i })
                                while (i < n) { s = s + 1; i = i + 1 }
                            }
                            return s
                        }
                    }''')],
        // x++ would run once at runtime, but the split evaluates the condition as a fact on each side: loud, as before.
        [group: 'P334 loop inside a branch', name: 'a branch condition that writes is not split', expect: 'Skipped verification of postcondition',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n, int x) {
                            int s = 0
                            if (x++ > 0) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s >= 0 })
                                @Decreases({ n - i })
                                while (i < n) { s = s + i; i = i + 1 }
                            }
                            return s + x - x
                        }
                    }''')],
    ]
}
