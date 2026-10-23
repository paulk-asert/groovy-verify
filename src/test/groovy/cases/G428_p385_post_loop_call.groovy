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
 * 'P385 post-loop call' — a postcondition after a loop (or at a return inside it, on a later iteration) is checked in a
 * state the loop's invariant allows, which no run need reach: a weak invariant's refutation showed `fails on: f(0)` for
 * a call that passes. The call is now sought along the exact runs from entry (the prefix, the first iterations — a
 * `continue` taken or not, a branch holding a loop either way, a loop nested one level — then the code to the return),
 * and withheld, with a note, when none fails.
 */
class G428_p385_post_loop_call {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 385: a postcondition refuted after a loop (or at an exit inside it) shows a failing call only from an exact run from entry — its first iterations, a continue either way, a nested loop one level — else withholds it, with a note that the invariant may be too weak."

    static final String WEAK = "no failing call: the failure is in a state the loop's invariant allows when it exits"

    static final List<Map> CASES = [

        // Before: `fails on: f(0)`, which returns 0 == n. The invariant is too weak to prove `result == n`.
        [group: "P385 post-loop call", name: "a weak invariant's refutation shows no call",
         expect: ["Cannot prove postcondition of f", WEAK], refute: "fails on",
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s <= i })
                            @Decreases({ n - i })
                            while (i < n) {
                                s = s + 1
                                i = i + 1
                            }
                            return s
                        }
                    }''')],

        // Before: `fails on: f(0)` too, which passes (s == 0 == n). A real bug: a run from entry fails it — that run is
        // the call (i == 2 isn't counted, so f(3) returns 2).
        [group: "P385 post-loop call", name: "a real bug keeps a call that fails",
         expect: ["Cannot prove postcondition of f", "fails on: f(3)"],
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s <= i })
                            @Decreases({ n - i })
                            while (i < n) {
                                if (i != 2) s = s + 1
                                i = i + 1
                            }
                            return s
                        }
                    }''')],

        // Before: `fails on: f(0)` and `f(1)`, which pass. A return inside the loop, on a later iteration: the
        // invariant's state isn't a run's either (on a run s == i, so `s > 5` returns 6 only when n >= 7).
        [group: "P385 post-loop call", name: "an exit inside the loop from a weak invariant shows no call",
         expect: ["Cannot prove postcondition of f", "no failing call: the failure is at an exit inside the loop"],
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result <= n })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                if (s > 5) return s
                                s = s + 1
                                i = i + 1
                            }
                            return s
                        }
                    }''')],

        // … and a real one keeps its call.
        [group: "P385 post-loop call", name: "a real bad exit inside the loop keeps its call",
         expect: ["Cannot prove postcondition of f", "fails on: f(4)"],
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result < 3 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s == i })
                            @Decreases({ n - i })
                            while (i < n) {
                                if (s == 3) return s
                                s = s + 1
                                i = i + 1
                            }
                            return 0
                        }
                    }''')],

        // Before: `fails on: f(1, 0)` — kept: the run takes the continue on its first iteration.
        [group: "P385 post-loop call", name: "a run through a continue",
         expect: ["Cannot prove postcondition of f", "fails on: f(1, "],
         src: tc('''class A {
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

        // A return inside a nested loop: the run reaches it through the outer loop's branch.
        [group: "P385 post-loop call", name: "a return inside a nested loop, reached through its branch",
         expect: ["Cannot prove postcondition of f", "fails on: f(3, true)"],
         src: tc('''class A {
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
    ]
}
