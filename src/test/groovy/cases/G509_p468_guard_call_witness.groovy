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
 * 'P468 a failing call through a guard that calls' — Phase 464 seeks a failing call inside a loop with no @Invariant
 * along the runs through its first iterations, each iteration assuming the loop's guard. A guard holding a call
 * (`while (g(i) < n)`) has no translation, so no run got past its first test: a call in such a guard, or in the body
 * of such a loop, named no failing call. The guard is now evaluated on each run into a hidden local — replayed, so its
 * call assumes its @Ensures — and the local assumed.
 */
class G509_p468_guard_call_witness {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 468: a call refuted in a loop with no @Invariant whose guard calls (`while (g(i) < n)`) names a failing call along the runs through the loop's first iterations, the guard's call assuming its @Ensures; it named none, a guard with a call having no translation to assume."

    static final String NOTE = 'no failing call: the call is inside a loop with no @Invariant'

    static final List<Map> CASES = [

        [group: "P468 a failing call through a guard that calls", name: "the call in the guard", expect: ['Cannot prove precondition of g', 'fails on: f(2)'],
         src: tc('''class A {
                        static int f(int n) {
                            int i = 0
                            while (g(i) < n) { i++ }
                            return i
                        }
                        @Requires({ i != 2 })
                        @Ensures({ result == i })
                        static int g(int i) { i }
                    }''')],

        [group: "P468 a failing call through a guard that calls", name: "a call in the body past it", expect: ['Cannot prove precondition of g', 'fails on: f(3)'],
         src: tc('''class A {
                        static void f(int n) {
                            int i = 0
                            while (h(i) < n) { g(i); i++ }
                        }
                        @Ensures({ result == i })
                        static int h(int i) { i }
                        @Requires({ i != 2 })
                        static void g(int i) { }
                    }''')],

        [group: "P468 a failing call through a guard that calls", name: "a do-while's guard", expect: ['Cannot prove precondition of g', 'fails on: f(2)'],
         src: tc('''class A {
                        static int f(int n) {
                            int i = 0
                            do { i++ } while (g(i) < n)
                            return i
                        }
                        @Requires({ i != 2 })
                        @Ensures({ result == i })
                        static int g(int i) { i }
                    }''')],

        [group: "P468 a failing call through a guard that calls", name: "no run reaches it", expect: ['Cannot prove precondition of g', NOTE], refute: 'fails on',
         src: tc('''class A {
                        static int f(int n) {
                            int i = 0
                            while (g(i) < n) { i += 2 }
                            return i
                        }
                        @Requires({ i != 3 })
                        @Ensures({ result == i })
                        static int g(int i) { i }
                    }''')],
    ]
}
