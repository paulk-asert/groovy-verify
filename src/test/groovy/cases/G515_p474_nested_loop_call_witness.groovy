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
 * 'P474 a failing call through nested loops' — Phase 464 seeks a failing call for a call inside a loop with no
 * @Invariant along the runs from entry through the loop's first iterations; with a second such loop around it (a loop
 * nested in another) it sought none, and the note said no run is known. The search now goes through each loop around
 * the call in turn, outermost first: a run to an iteration of the outer loop begun, its body up to the inner loop, the
 * inner loop's first iterations from there — as the loop's other obligations already do (Phase 371/398).
 */
class G515_p474_nested_loop_call_witness {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 474: a call refuted inside nested loops with no @Invariant names a failing call along the runs through each loop's first iterations in turn (`g(i + j)` needing `i + j != 3` fails on a call that reaches it), where it named none; with no such run, the note stays."

    static final String NOTE = 'no failing call: the call is inside a loop with no @Invariant'

    static final List<Map> CASES = [

        [group: "P474 a failing call through nested loops", name: "two for loops", expect: ['Cannot prove precondition of g', 'fails on: f('],
         src: tc('''class A {
                        static void f(int n) {
                            for (int i = 0; i < n; i++) {
                                for (int j = 0; j < n; j++) g(i + j)
                            }
                        }
                        @Requires({ k != 3 })
                        static void g(int k) { }
                    }''')],

        [group: "P474 a failing call through nested loops", name: "a while in a for, on the outer counter", expect: ['Cannot prove precondition of g', 'fails on: f(2)'],
         src: tc('''class A {
                        static void f(int n) {
                            for (int i = 0; i < n; i++) {
                                int j = 0
                                while (j < n) { g(i); j++ }
                            }
                        }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P474 a failing call through nested loops", name: "the call in the inner guard", expect: ['Cannot prove precondition of g', 'fails on: f('],
         src: tc('''class A {
                        static int f(int n) {
                            int s = 0
                            for (int i = 0; i < n; i++) {
                                int j = 0
                                while (g(i + j) < n) { j++; s++ }
                            }
                            return s
                        }
                        @Requires({ k != 3 })
                        @Ensures({ result == k })
                        static int g(int k) { k }
                    }''')],

        [group: "P474 a failing call through nested loops", name: "three levels", expect: ['Cannot prove precondition of g', 'fails on: f('],
         src: tc('''class A {
                        static void f(int n) {
                            for (int i = 0; i < n; i++) {
                                for (int j = 0; j < n; j++) {
                                    for (int k = 0; k < n; k++) g(i + j + k)
                                }
                            }
                        }
                        @Requires({ s != 2 })
                        static void g(int s) { }
                    }''')],

        // the boundary, shared with the loop's other obligations (Phase 371/398): a run through two whole outer iterations,
        // each running the inner loop through, is longer than the candidates the search builds
        [group: "P474 a failing call through nested loops", name: "a third outer iteration", expect: ['Cannot prove precondition of g', NOTE], refute: 'fails on',
         src: tc('''class A {
                        static void f(int n) {
                            for (int i = 0; i < n; i++) {
                                int j = 0
                                while (j < n) { g(i); j++ }
                            }
                        }
                        @Requires({ i != 2 })
                        static void g(int i) { }
                    }''')],

        [group: "P474 a failing call through nested loops", name: "no run reaches it", expect: ['Cannot prove precondition of g', NOTE], refute: 'fails on',
         src: tc('''class A {
                        static void f(int n) {
                            for (int i = 0; i < n; i += 2) {
                                for (int j = 0; j < n; j += 2) g(i + j)
                            }
                        }
                        @Requires({ k != 3 })
                        static void g(int k) { }
                    }''')],
    ]
}
