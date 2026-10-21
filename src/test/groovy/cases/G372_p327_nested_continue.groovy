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
 * 'P327 nested continue ahead of an exit' — Phase 325 kept an exit after a top-level {@code if (c) continue} where the
 * exit lifting sees it, but a {@code continue} nested deeper in an {@code if} still went through Phase 324's branch
 * rewrite, which buries the exit. Such an {@code if} now gets a flag that is false before it and set where it
 * continues; the rest of that branch, and everything after the {@code if}, is guarded by it
 * (ContractExpansionTransform.flagged).
 */
class G372_p327_nested_continue {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 327 nested continue ahead of an exit: an if whose branches continue at any depth, followed by a break or return, declares a body-local flag false before it, replaces each continue by setting the flag and guards the rest of that branch by it, then guards what follows the if as Phase 325 does, so the exits stay top-level; in an outer loop and a nested one. A guard ahead of a nested loop puts it in a branch (Phase 344).'

    static final List<Map> CASES = [

        [group: 'P327 nested continue ahead of an exit', name: 'a continue nested in an if ahead of a break', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 })
                        static int f(int[] a, int t) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                i = i + 1
                                if (t > 0) {
                                    if (a[i - 1] < 0) continue
                                    t = t - 1
                                }
                                if (a[i - 1] == t) break
                            }
                            return i
                        }
                    }''')],
        // The continue in the else skips the negatives; the then branch only sees values over 100, so every return is >= 0.
        [group: 'P327 nested continue ahead of an exit', name: 'a continue in an else keeps the return from seeing negatives', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == -1 || (0 <= result && result < a.length && a[result] >= 0) })
                        static int find(int[] a, int t) {
                            int big = 0
                            @Invariant({ 0 <= i && i <= a.length && big >= 0 })
                            @Decreases({ a.length - i })
                            for (int i = 0; i < a.length; i++) {
                                if (a[i] > 100) {
                                    big = big + 1
                                } else {
                                    if (a[i] < 0) { continue }
                                }
                                if (a[i] == t) return i
                            }
                            return -1
                        }
                    }''')],
        // s - 1 runs only when s != 0: the rest of the continuing branch is skipped, not just what follows the if.
        [group: 'P327 nested continue ahead of an exit', name: 'the rest of the continuing branch is skipped', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 })
                        static int f(int[] a, int t) {
                            int s = 0
                            @Invariant({ 0 <= i && i <= a.length && s >= 0 })
                            @Decreases({ a.length - i })
                            for (int i = 0; i < a.length; i++) {
                                if (t > 0) {
                                    if (s == 0) continue
                                    s = s - 1
                                }
                                if (a[i] == t) break
                            }
                            return s
                        }
                    }''')],
        [group: 'P327 nested continue ahead of an exit', name: 'a continue that does not cover the exit is refuted', expect: 'Cannot prove postcondition of find',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == -1 || (0 <= result && result < a.length && a[result] >= 0) })
                        static int find(int[] a, int t) {
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            for (int i = 0; i < a.length; i++) {
                                if (t > 0) {
                                    if (a[i] < 0) continue
                                }
                                if (a[i] == t) return i
                            }
                            return -1
                        }
                    }''')],
        // The continuing iteration keeps the s = s - 1 before its continue: s goes negative on f([1], 1).
        [group: 'P327 nested continue ahead of an exit', name: 'the continuing iteration preserves the invariant', expect: 'Cannot prove loop invariant is preserved',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 })
                        static int f(int[] a, int t) {
                            int s = 0
                            @Invariant({ 0 <= i && i <= a.length && s >= 0 })
                            @Decreases({ a.length - i })
                            for (int i = 0; i < a.length; i++) {
                                if (t > 0) {
                                    s = s - 1
                                    if (a[i] > 0) continue
                                    s = s + 1
                                }
                                if (a[i] == t) break
                                s = s + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P327 nested continue ahead of an exit', name: 'a nested continue ahead of a nested loop break', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                int d = 0
                                @Invariant({ 0 <= j && j <= n && d >= 0 })
                                @Decreases({ n - j })
                                while (j < n) {
                                    j = j + 1
                                    if (j > 1) {
                                        if (j % 2 == 0) continue
                                        d = d + 1
                                    }
                                    if (j > i) break
                                }
                                s = s + d
                                i = i + 1
                            }
                            return s
                        }
                    }''')],

        // ---------- still out ----------
        [group: 'P327 nested continue ahead of an exit', name: 'a nested continue ahead of a loop verifies (Phase 344)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                i = i + 1
                                if (i > 1) {
                                    if (i % 2 == 0) continue
                                }
                                int j = 0
                                @Invariant({ 0 <= j && j <= i })
                                @Decreases({ i - j })
                                while (j < i) {
                                    if (j == 3) break
                                    j = j + 1
                                }
                                s = s + j
                            }
                            return s
                        }
                    }''')],
    ]
}
