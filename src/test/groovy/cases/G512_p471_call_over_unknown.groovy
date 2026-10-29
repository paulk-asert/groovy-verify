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
 * 'P471 no failing call over an unknown' — a call site's refutation names a failing call built from the model's entry
 * values. Two things on the path made that call one that fails only sometimes: a condition the verifier can't translate
 * was dropped (the call checked as if its branch were always taken: `if (rnd.nextInt() > 0) g(n)` said `fails on:
 * f(1, new Random())`), and a helper's value no run is known to produce (Phase 469/470's fresh value whose body doesn't
 * translate: `if (h(n) > 0) g(n)` with `h` returning a random number) was picked by the model. Either on the path, or
 * in an argument, now withholds the call with a note saying which.
 */
class G512_p471_call_over_unknown {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 471: a call-site refutation whose path passes a condition the verifier can't evaluate, or rests on a helper's value no run is known to produce, names no failing call and says which (it named a call that fails only for some draws of `rnd.nextInt()`); one the unknown doesn't reach still names its call."

    static final String DROPPED = 'a condition the verifier can\'t evaluate, so no run is known to get there'
    static final String UNKNOWN = 'a value the verifier can\'t evaluate'

    static final List<Map> CASES = [

        // ---------- the path rests on an unknown: the call withheld ----------
        [group: "P471 no failing call over an unknown", name: "a condition it can't evaluate", expect: ['Cannot prove precondition of g', '`rnd != null && rnd.nextInt() > 0`', DROPPED], refute: 'fails on',
         src: tc('''class A {
                        static void f(int n, Random rnd) {
                            if (rnd != null && rnd.nextInt() > 0) g(n)
                        }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P471 no failing call over an unknown", name: "… an early return's, taken false", expect: ['Cannot prove precondition of g', '`rnd == null || rnd.nextInt() > 0` (false)', DROPPED], refute: 'fails on',
         src: tc('''class A {
                        static void f(int n, Random rnd) {
                            if (rnd == null || rnd.nextInt() > 0) return
                            g(n)
                        }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P471 no failing call over an unknown", name: "… a ternary's", expect: ['Cannot prove precondition of g', '`rnd.nextInt() > 0`', DROPPED], refute: 'fails on',
         src: tc('''class A {
                        @Requires({ rnd != null })
                        static int f(int n, Random rnd) {
                            return rnd.nextInt() > 0 ? g(n) : 0
                        }
                        @Requires({ i != 1 })
                        static int g(int i) { i }
                    }''')],

        [group: "P471 no failing call over an unknown", name: "a helper's unknown value", expect: ['Cannot prove precondition of g', 'what h(…) returns', UNKNOWN], refute: 'fails on',
         src: tc('''class A {
                        static void f(int n) {
                            if (h(n) > 0) g(n)
                        }
                        static int h(int i) { new Random().nextInt() }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P471 no failing call over an unknown", name: "… through a local", expect: ['Cannot prove precondition of g', 'what h(…) returns', UNKNOWN], refute: 'fails on',
         src: tc('''class A {
                        static void f(int n) {
                            int r = h(n)
                            if (r > 0) g(n)
                        }
                        static int h(int i) { new Random().nextInt() }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P471 no failing call over an unknown", name: "… as the argument", expect: ['Cannot prove precondition of g', 'what h(…) returns', UNKNOWN], refute: 'fails on',
         src: tc('''class A {
                        static void f(int n) {
                            g(h(n))
                        }
                        static int h(int i) { new Random().nextInt() }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        // ---------- the unknown doesn't reach it: the call still named ----------
        [group: "P471 no failing call over an unknown", name: "an unknown value unused", expect: ['Cannot prove precondition of g', 'fails on: f(1)'],
         src: tc('''class A {
                        static void f(int n) {
                            int r = h(n)
                            g(n)
                        }
                        static int h(int i) { new Random().nextInt() }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P471 no failing call over an unknown", name: "a fresh value its body defines", expect: ['Cannot prove precondition of g', 'fails on: f('],
         src: tc('''class A {
                        static int val(Box b) { b.v }
                        @Requires({ b != null })
                        static void f(Box b, int n) {
                            if (val(b) == 2) g(n)
                        }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }
                    final class Box { int v }''')],
    ]
}
