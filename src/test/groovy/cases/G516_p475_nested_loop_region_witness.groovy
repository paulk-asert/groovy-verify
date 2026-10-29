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
 * 'P475 a failing run past an outer loop's first iteration' — a loop's obligations (an index, a division) inside loops
 * with no @Invariant are checked at an arbitrary iteration, and a failing call sought along the runs from entry through
 * the loops' first iterations (Phase 371). For a loop nested in another, the candidates were gathered over each run to
 * an outer iteration, then cut to the first 32 unsorted: the outer loop's first iteration alone filled them, so a
 * failure past it (`100.intdiv(i - 1)`, each earlier outer iteration running the inner loop through) named no call. The
 * shortest over all of them are kept now, as the call-site search does (Phase 474).
 */
class G516_p475_nested_loop_region_witness {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 475: an obligation inside nested loops with no @Invariant whose failure needs a later outer iteration (`100.intdiv(i - 1)`) names a failing call, the runs kept the shortest over every outer iteration where the first outer iteration's filled the cap."

    static final String NOTE = 'no failing call: the failure is at a loop iteration the check reaches through the loop\'s summary'

    static final List<Map> CASES = [

        [group: "P475 a failing run past an outer loop's first iteration", name: "a division in two for loops", expect: ['Possible ArithmeticException', 'fails on: f(2)'],
         src: tc('''class A {
                        static int f(int n) {
                            int s = 0
                            for (int i = 0; i < n; i++) {
                                for (int j = 0; j < n; j++) s += 100.intdiv(i - 1)
                            }
                            return s
                        }
                    }''')],

        [group: "P475 a failing run past an outer loop's first iteration", name: "… a while in a for", expect: ['Possible ArithmeticException', 'fails on: f(2)'],
         src: tc('''class A {
                        static int f(int n) {
                            int s = 0
                            for (int i = 0; i < n; i++) {
                                int j = 0
                                while (j < n) { s += 100.intdiv(i - 1); j++ }
                            }
                            return s
                        }
                    }''')],

        [group: "P475 a failing run past an outer loop's first iteration", name: "an index on the outer counter", expect: ['Possible IndexOutOfBoundsException', 'fails on: f('],
         src: tc('''class A {
                        @Requires({ a != null && a.length == 1 })
                        static int f(int[] a, int n) {
                            int s = 0
                            for (int i = 0; i < n; i++) {
                                for (int j = 0; j < n; j++) s += a[i]
                            }
                            return s
                        }
                    }''')],

        // ---------- unchanged ----------
        [group: "P475 a failing run past an outer loop's first iteration", name: "a failure in the first outer iteration", expect: ['Possible ArithmeticException', 'fails on: f(2)'],
         src: tc('''class A {
                        static int f(int n) {
                            int s = 0
                            for (int i = 0; i < n; i++) {
                                for (int j = 0; j < n; j++) s += 100.intdiv(j - 1)
                            }
                            return s
                        }
                    }''')],

        // the boundary, as for a call (Phase 474): two whole outer iterations, each running the inner loop through, make a
        // run longer than the candidates built
        [group: "P475 a failing run past an outer loop's first iteration", name: "a third outer iteration", expect: ['Possible ArithmeticException', NOTE], refute: 'fails on',
         src: tc('''class A {
                        static int f(int n) {
                            int s = 0
                            for (int i = 0; i < n; i++) {
                                for (int j = 0; j < n; j++) s += 100.intdiv(i - 2)
                            }
                            return s
                        }
                    }''')],
    ]
}
