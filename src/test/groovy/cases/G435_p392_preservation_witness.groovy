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
 * 'P392 preservation witness' — a preservation check starts from any state the invariant allows at an iteration's
 * start, which no run need reach, and its call came from that model: `f(1)` for an invariant that holds on every run
 * but isn't inductive, and `f(1)` again where the run that breaks it is `f(3)`. The call is now sought along the exact
 * runs from entry (an iteration of the first eight, then one more pass of the body), and withheld, with a note, when
 * none breaks the invariant — Phase 385's postcondition witness, for preservation.
 */
class G435_p392_preservation_witness {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 392: a loop invariant's preservation refutation shows the call of an exact run from entry that breaks it, else withholds the call, noting the invariant may hold without being inductive."

    static final String PRES = "Cannot prove loop invariant is preserved by the loop body in f"
    static final String NOTE = "no failing call: the invariant is broken from a state it allows at an iteration's start"

    static final List<Map> CASES = [

        // Before: `fails on: f(1)`, which returns 1 (x never passes 3 for n <= 3).
        [group: "P392 preservation witness", name: "a true invariant that isn't inductive: no call",
         expect: [PRES, NOTE], refute: "fails on",
         src: tc('''class A {
                            @Requires({ n >= 0 && n <= 3 })
                            static int f(int n) {
                                int x = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && x <= 10 })
                                @Decreases({ n - i })
                                while (i < n) {
                                    x = x + 1
                                    i = i + 1
                                }
                                return x
                            }
                        }''')],

        // Before: `fails on: f(1)`, whose s is 1 <= 2: the third iteration breaks it.
        [group: "P392 preservation witness", name: "a broken invariant: the first run that breaks it",
         expect: [PRES, "fails on: f(3)"],
         src: tc('''class A {
                            @Requires({ n >= 0 })
                            static int f(int n) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s <= 2 })
                                @Decreases({ n - i })
                                while (i < n) {
                                    s = s + 1
                                    i = i + 1
                                }
                                return s
                            }
                        }''')],

        [group: "P392 preservation witness", name: "… however late",
         expect: [PRES, "fails on: f(5)"],
         src: tc('''class A {
                            @Requires({ n >= 0 })
                            static int f(int n) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s != 5 })
                                @Decreases({ n - i })
                                while (i < n) {
                                    s = s + 1
                                    i = i + 1
                                }
                                return s
                            }
                        }''')],

        // The return at i == 1 keeps s <= 1 on every run; before: `fails on: f(1)`.
        [group: "P392 preservation witness", name: "an early exit that keeps it: no call",
         expect: [PRES, NOTE], refute: "fails on",
         src: tc('''class A {
                            @Requires({ n >= 0 })
                            static int f(int n) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s <= 2 })
                                @Decreases({ n - i })
                                while (i < n) {
                                    if (i == 1) return s
                                    s = s + 1
                                    i = i + 1
                                }
                                return s
                            }
                        }''')],

        [group: "P392 preservation witness", name: "a for loop's genuine call is kept",
         expect: [PRES, "fails on: f([-1] as int[])"],
         src: tc('''class A {
                            @Requires({ a != null })
                            static int f(int[] a) {
                                int s = 0
                                @Invariant({ 0 <= i && i <= a.length && s >= 0 })
                                for (int i = 0; i < a.length; i++) {
                                    s = s + a[i]
                                }
                                return s
                            }
                        }''')],
    ]
}
