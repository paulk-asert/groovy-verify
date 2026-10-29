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
 * 'P472 no failing call over an unknown, for any check' — Phase 471's rule for a call site, for every obligation: an
 * index, a division, an assertion, a postcondition. Each check drops a path condition it can't translate (a sound
 * weakening) and lets the model pick a helper's value no run is known to produce (Phase 469/470), and each named a
 * failing call regardless: `if (rnd.nextInt() > 0) return a[n]` said `fails on: f(new int[0], -1, new Random())`, a run
 * that fails only for some draws. The dropped condition or the unknown value now taints the check, and its failing call
 * is withheld with a note saying which.
 */
class G513_p472_any_check_over_unknown {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 472: any check — an index, a division, an assertion, a postcondition — whose path passes a condition the verifier can't evaluate, or whose model picks a helper's value no run is known to produce, names no failing call and says which; it named one that fails only for some draws of `rnd.nextInt()`."

    static final String DROPPED = 'a condition the verifier can\'t evaluate, so no run is known to get there'
    static final String UNKNOWN = 'a value the verifier can\'t evaluate'

    static final List<Map> CASES = [

        // ---------- a check over an unknown: the call withheld ----------
        [group: "P472 no failing call over an unknown, for any check", name: "an index under a condition it can't evaluate", expect: ['Possible IndexOutOfBoundsException', '`rnd.nextInt() > 0`', DROPPED], refute: 'fails on',
         src: tc('''class A {
                        @Requires({ a != null && rnd != null })
                        static int f(int[] a, int n, Random rnd) {
                            if (rnd.nextInt() > 0) return a[n]
                            return 0
                        }
                    }''')],

        [group: "P472 no failing call over an unknown, for any check", name: "… past an early return over one", expect: ['Possible IndexOutOfBoundsException', '`rnd.nextInt() > 0` (false)', DROPPED], refute: 'fails on',
         src: tc('''class A {
                        @Requires({ a != null && rnd != null })
                        static int f(int[] a, int n, Random rnd) {
                            if (rnd.nextInt() > 0) return 0
                            return a[n]
                        }
                    }''')],

        [group: "P472 no failing call over an unknown, for any check", name: "an assertion under one", expect: ['Assertion may not hold', '`rnd.nextInt() > 0`', DROPPED], refute: 'fails on',
         src: tc('''class A {
                        @Requires({ rnd != null })
                        static void f(int n, Random rnd) {
                            if (rnd.nextInt() > 0) assert n != 1
                        }
                    }''')],

        [group: "P472 no failing call over an unknown, for any check", name: "a recursion measure under one", expect: ['recursion measure', '`rnd.nextInt() > 0`', DROPPED], refute: 'fails on',
         src: tc('''class A {
                        @Requires({ rnd != null })
                        @Decreases({ n })
                        static int f(int n, Random rnd) {
                            if (rnd.nextInt() > 0) return f(n - 1, rnd)
                            return 0
                        }
                    }''')],

        [group: "P472 no failing call over an unknown, for any check", name: "a division under a helper's unknown value", expect: ['Possible ArithmeticException', 'what h(…) returns', UNKNOWN], refute: 'fails on',
         src: tc('''class A {
                        static int f(int n) {
                            if (h(n) > 0) return 100.intdiv(n)
                            return 0
                        }
                        static int h(int i) { new Random().nextInt() }
                    }''')],

        [group: "P472 no failing call over an unknown, for any check", name: "a postcondition under one", expect: ['Cannot prove postcondition', 'what h(…) returns', UNKNOWN], refute: 'fails on',
         src: tc('''class A {
                        @Ensures({ result != 1 })
                        static int f(int n) {
                            if (h(n) > 0) return n
                            return 0
                        }
                        static int h(int i) { new Random().nextInt() }
                    }''')],

        // ---------- the unknown doesn't reach it: the call still named ----------
        [group: "P472 no failing call over an unknown, for any check", name: "an index under a condition it can evaluate", expect: ['Possible IndexOutOfBoundsException', 'fails on: f('],
         src: tc('''class A {
                        @Requires({ a != null })
                        static int f(int[] a, int n) {
                            if (n > 0) return a[n]
                            return 0
                        }
                    }''')],

    ]
}
