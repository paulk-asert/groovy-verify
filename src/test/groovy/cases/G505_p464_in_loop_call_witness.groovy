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
 * 'P464 a failing call through a loop with no invariant' — Phase 461 checks a call inside a loop with no @Invariant at
 * an arbitrary iteration, and a refutation there named no failing call (the state may be one no run reaches). The
 * call is now sought along the exact runs from entry, as Phase 371 seeks one for the loop's other obligations: the
 * statements before the loop, the loop's first iterations (up to eight), then the body up to the call. The first run
 * that fails is the call shown; with none, the note stays.
 */
class G505_p464_in_loop_call_witness {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 464: a call refuted inside a loop with no @Invariant names a failing call when a run from entry through the loop's first eight iterations reaches the failure (`g(i)` needing `i != 3` fails on f(4)); with none, the note says no run is known to get there."

    static final String NOTE = 'no failing call: the call is inside a loop with no @Invariant'

    static final List<Map> CASES = [

        // ---------- a run reaches it: the call shown ----------
        [group: "P464 a failing call through a loop with no invariant", name: "a later iteration's failure", expect: ['Cannot prove precondition of g', 'fails on: f(4)'],
         src: tc('''class A {
                        static void f(int n) {
                            int i = 0
                            while (i < n) { g(i); i++ }
                        }
                        @Requires({ i != 3 })
                        static void g(int i) { }
                    }''')],

        [group: "P464 a failing call through a loop with no invariant", name: "a value the body builds", expect: ['Cannot prove precondition of g', 'fails on: f(2)'],
         src: tc('''class A {
                        static void f(int n) {
                            int j = 0
                            for (int i = 0; i < n; i++) {
                                j += 2
                                g(j)
                            }
                        }
                        @Requires({ j != 4 })
                        static void g(int j) { }
                    }''')],

        [group: "P464 a failing call through a loop with no invariant", name: "an if in the body", expect: ['Cannot prove precondition of g', 'fails on: f(4)'],
         src: tc('''class A {
                        static void f(int n) {
                            for (int i = 0; i < n; i++) {
                                if (i % 2 == 1) g(i)
                            }
                        }
                        @Requires({ i != 3 })
                        static void g(int i) { }
                    }''')],

        [group: "P464 a failing call through a loop with no invariant", name: "a write before the loop", expect: ['Cannot prove precondition of g', 'fails on: f(3)'],
         src: tc('''class A {
                        static void f(int n) {
                            int i = n
                            while (i > 0) { g(n - i); i-- }
                        }
                        @Requires({ k != 2 })
                        static void g(int k) { }
                    }''')],

        [group: "P464 a failing call through a loop with no invariant", name: "an earlier call's @Ensures on the way", expect: ['Cannot prove precondition of g', 'fails on: f(2)'],
         src: tc('''class A {
                        static void f(int n) {
                            int s = 0
                            for (int i = 0; i < n; i++) {
                                g(s)
                                s = h(s)
                            }
                        }
                        @Ensures({ result == s + 5 })
                        static int h(int s) { s + 5 }
                        @Requires({ s != 5 })
                        static void g(int s) { }
                    }''')],

        // ---------- none known: the note stays ----------
        [group: "P464 a failing call through a loop with no invariant", name: "no run reaches it", expect: ['Cannot prove precondition of g', NOTE], refute: 'fails on',
         src: tc('''class A {
                        static void f(int n) {
                            int i = 0
                            while (i < n) { g(i); i += 2 }
                        }
                        @Requires({ i != 3 })
                        static void g(int i) { }
                    }''')],

        [group: "P464 a failing call through a loop with no invariant", name: "past the eighth iteration", expect: ['Cannot prove precondition of g', NOTE], refute: 'fails on',
         src: tc('''class A {
                        static void f(int n) {
                            int i = 0
                            while (i < n) { g(i); i++ }
                        }
                        @Requires({ i != 10 })
                        static void g(int i) { }
                    }''')],

        [group: "P464 a failing call through a loop with no invariant", name: "a loop nested in another", expect: ['Cannot prove precondition of g', NOTE], refute: 'fails on',
         src: tc('''class A {
                        static void f(int n) {
                            for (int i = 0; i < n; i++) {
                                for (int j = 0; j < n; j++) g(j)
                            }
                        }
                        @Requires({ j != 1 })
                        static void g(int j) { }
                    }''')],
    ]
}
