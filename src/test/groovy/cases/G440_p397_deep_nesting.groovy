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
 * 'P397 deep nesting' — loops nested three or more deep skipped loudly (`loops nested 3+ deep — not yet supported`).
 * They are verified level by level now: each nested loop against the one around it (its establishment under that
 * loop's invariant and guard), its obligations under its own invariant, its stable @Requires judged by the outermost
 * loop's writes, and its witnesses sought through every enclosing loop. And a nested loop's establishment refutation,
 * at any depth, shows a call only from an exact run to its entry (it showed the outer-iteration model's: `f(1)` for a
 * run whose inner entry is fine).
 */
class G440_p397_deep_nesting {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 397: loops nested three or more deep are verified level by level (establishment, preservation, obligations, returns), and a nested loop's establishment refutation shows a call only from an exact run to its entry."

    static final String EST = "Cannot prove loop invariant holds on entry in f"
    static final String NOTE = "no failing call: the inner loop's entry is checked in a state the outer loop's invariant allows"

    static final List<Map> CASES = [

        // Before (each): `loops nested 3+ deep — not yet supported`.
        [group: "P397 deep nesting", name: "an obligation three loops down is checked under its own loop",
         ok: true,
         src: tc('''class A {
                            @Requires({ a != null && n >= 0 && a.length >= n })
                            static void f(int[] a, int n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    int j = 0
                                    @Invariant({ 0 <= j && j <= n })
                                    @Decreases({ n - j })
                                    while (j < n) {
                                        int k = 0
                                        @Invariant({ 0 <= k && k <= n })
                                        @Decreases({ n - k })
                                        while (k < n) {
                                            a[k] = i + j
                                            k = k + 1
                                        }
                                        j = j + 1
                                    }
                                    i = i + 1
                                }
                            }
                        }''')],

        [group: "P397 deep nesting", name: "… and refutes with the run that reaches it",
         expect: ["index may be out of bounds", "fails on: f(new int[0], 1)"],
         src: tc('''class A {
                            @Requires({ a != null && n >= 0 })
                            static void f(int[] a, int n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    int j = 0
                                    @Invariant({ 0 <= j && j <= n })
                                    @Decreases({ n - j })
                                    while (j < n) {
                                        int k = 0
                                        @Invariant({ 0 <= k && k <= n })
                                        @Decreases({ n - k })
                                        while (k < n) {
                                            a[k] = i + j
                                            k = k + 1
                                        }
                                        j = j + 1
                                    }
                                    i = i + 1
                                }
                            }
                        }''')],

        // n = 4: the first middle iteration's inner loop leaves s = 4 for the second's entry.
        [group: "P397 deep nesting", name: "an innermost invariant's entry, broken by a real run",
         expect: [EST, "fails on: f(4)"],
         src: tc('''class A {
                            @Requires({ n >= 0 })
                            static int f(int n) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    int j = 0
                                    @Invariant({ 0 <= j && j <= n })
                                    @Decreases({ n - j })
                                    while (j < n) {
                                        int k = 0
                                        @Invariant({ 0 <= k && k <= n && s <= 3 })
                                        @Decreases({ n - k })
                                        while (k < n) {
                                            s = s + 1
                                            k = k + 1
                                        }
                                        j = j + 1
                                    }
                                    i = i + 1
                                }
                                return s
                            }
                        }''')],

        [group: "P397 deep nesting", name: "… withheld when no run breaks it",
         expect: [EST, NOTE], refute: "fails on",
         src: tc('''class A {
                            @Requires({ n >= 0 && n <= 1 })
                            static int f(int n) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    int j = 0
                                    @Invariant({ 0 <= j && j <= n })
                                    @Decreases({ n - j })
                                    while (j < n) {
                                        int k = 0
                                        @Invariant({ 0 <= k && k <= n && s <= 3 })
                                        @Decreases({ n - k })
                                        while (k < n) {
                                            s = s + 1
                                            k = k + 1
                                        }
                                        j = j + 1
                                    }
                                    i = i + 1
                                }
                                return s
                            }
                        }''')],

        [group: "P397 deep nesting", name: "a return three loops down is checked",
         expect: ["Cannot prove postcondition of f"],
         src: tc('''class A {
                            @Requires({ n >= 0 })
                            @Ensures({ result >= 0 })
                            static int f(int n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    int j = 0
                                    @Invariant({ 0 <= j && j <= n })
                                    @Decreases({ n - j })
                                    while (j < n) {
                                        int k = 0
                                        @Invariant({ 0 <= k && k <= n })
                                        @Decreases({ n - k })
                                        while (k < n) {
                                            if (i == 1 && j == 1 && k == 1) return -1
                                            k = k + 1
                                        }
                                        j = j + 1
                                    }
                                    i = i + 1
                                }
                                return 0
                            }
                        }''')],

        // Before: `fails on: f(1)`, whose inner entry has s <= 1 — the model's outer-iteration state, no run's.
        [group: "P397 deep nesting", name: "two levels: a nested entry no run breaks shows no call",
         expect: [EST, NOTE], refute: "fails on",
         src: tc('''class A {
                            @Requires({ n >= 0 && n <= 1 })
                            static int f(int n) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    int k = 0
                                    @Invariant({ 0 <= k && k <= n && s <= 3 })
                                    @Decreases({ n - k })
                                    while (k < n) {
                                        s = s + 1
                                        k = k + 1
                                    }
                                    i = i + 1
                                }
                                return s
                            }
                        }''')],

        [group: "P397 deep nesting", name: "a nested do-while holding loops skips loudly",
         expect: ["a nested do-while that holds loops itself"],
         src: tc('''class A {
                            @Requires({ n >= 1 })
                            static int f(int n) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    int j = 0
                                    @Invariant({ 0 <= j && j <= n })
                                    @Decreases({ n - j })
                                    do {
                                        int k = 0
                                        @Invariant({ 0 <= k && k <= n })
                                        @Decreases({ n - k })
                                        while (k < n) { k = k + 1 }
                                        j = j + 1
                                    } while (j < n)
                                    i = i + 1
                                }
                                return s
                            }
                        }''')],
    ]
}
