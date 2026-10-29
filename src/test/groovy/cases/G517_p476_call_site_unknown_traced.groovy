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
 * 'P476 call-site unknowns traced' — Phase 471 withheld a call site's failing call when a helper's unknown value showed
 * in the rendering of a path condition or of any argument: string matching, apart from Phase 473's dependence test
 * every other check uses. So `g(n, h(n))` named no call though g's precondition reads only its first parameter, and
 * `f(1)` fails whatever h returns. A call site's arguments now bind its formals as definitions, and the session's
 * taints and dependence test decide: the call is withheld only when the precondition reads the value.
 */
class G517_p476_call_site_unknown_traced {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 476: a call site's failing call is withheld over a helper's unknown value only when the precondition or the path reads it (Phase 473's dependence test, now for call sites too); an unknown value passed to a parameter the precondition doesn't read names its call (`g(n, h(n))` under `@Requires({ i != 1 })` fails on f(1))."

    static final String UNKNOWN = 'a value the verifier can\'t evaluate'

    static final List<Map> CASES = [

        // ---------- the precondition doesn't read it: the call named ----------
        [group: "P476 call-site unknowns traced", name: "an unknown argument the precondition doesn't read", expect: ['Cannot prove precondition of g', 'fails on: f(1)'],
         src: tc('''class A {
                        static void f(int n) {
                            g(n, h(n))
                        }
                        static int h(int i) { new Random().nextInt() }
                        @Requires({ i != 1 })
                        static void g(int i, int j) { }
                    }''')],

        [group: "P476 call-site unknowns traced", name: "… the first argument", expect: ['Cannot prove precondition of g', 'fails on: f(1)'],
         src: tc('''class A {
                        static void f(int n) {
                            g(h(n), n)
                        }
                        static int h(int i) { new Random().nextInt() }
                        @Requires({ j != 1 })
                        static void g(int i, int j) { }
                    }''')],

        [group: "P476 call-site unknowns traced", name: "… through a local", expect: ['Cannot prove precondition of g', 'fails on: f(1)'],
         src: tc('''class A {
                        static void f(int n) {
                            int r = h(n)
                            g(n, r)
                        }
                        static int h(int i) { new Random().nextInt() }
                        @Requires({ i != 1 })
                        static void g(int i, int j) { }
                    }''')],

        // ---------- the precondition reads it: the call withheld ----------
        [group: "P476 call-site unknowns traced", name: "the precondition reads both", expect: ['Cannot prove precondition of g', 'what h(…) returns', UNKNOWN], refute: 'fails on',
         src: tc('''class A {
                        static void f(int n) {
                            g(n, h(n))
                        }
                        static int h(int i) { new Random().nextInt() }
                        @Requires({ i != j })
                        static void g(int i, int j) { }
                    }''')],

        [group: "P476 call-site unknowns traced", name: "… through a local", expect: ['Cannot prove precondition of g', 'what h(…) returns', UNKNOWN], refute: 'fails on',
         src: tc('''class A {
                        static void f(int n) {
                            int r = h(n)
                            int t = r + 1
                            g(n, t)
                        }
                        static int h(int i) { new Random().nextInt() }
                        @Requires({ i != j })
                        static void g(int i, int j) { }
                    }''')],
    ]
}
