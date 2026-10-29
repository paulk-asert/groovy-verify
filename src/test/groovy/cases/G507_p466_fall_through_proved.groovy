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
 * 'P466 a call proved along every way into its arm' — Phase 463 checks a call in a switch arm with what the arms falling
 * into it write unknown, and Phase 465 seeks a failing call along the ways in. A fall-through's ways in are all of them —
 * each case's entry (first match) and the arms run from it — so when the call holds along each, it holds: the summarised
 * refutation was a state no run reaches. It was a false alarm with a note; it now compiles clean.
 */
class G507_p466_fall_through_proved {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 466: a call in a switch arm that arms fall into is proved when it holds along every way in (each case's entry and the arms run from it), where the arms' writes left unknown refuted it with a note (`case 1: n = n + 1` falling into `g(n)` needing `n > 0`)."

    static final String HAVOC = 'no failing call: the failure rests on what a statement writes inside it'

    static final List<Map> CASES = [

        [group: "P466 a call proved along every way into its arm", name: "one arm falling in", ok: true,
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n, int k) {
                            switch (k) {
                                case 1:
                                    n = n + 1
                                case 2:
                                    return g(n)
                                default:
                                    return 0
                            }
                        }
                        @Requires({ n > 0 })
                        static int g(int n) { n }
                    }''')],

        [group: "P466 a call proved along every way into its arm", name: "two arms falling in", ok: true,
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n, int k) {
                            switch (k) {
                                case 1:
                                    n = n + 1
                                case 2:
                                    n = n * 2
                                case 3:
                                    return g(n)
                                default:
                                    return 0
                            }
                        }
                        @Requires({ n > 0 })
                        static int g(int n) { n }
                    }''')],

        [group: "P466 a call proved along every way into its arm", name: "into the default", ok: true,
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n, int k) {
                            switch (k) {
                                case 1:
                                    return 0
                                case 2:
                                    n = n + 1
                                default:
                                    return g(n)
                            }
                        }
                        @Requires({ n > 0 })
                        static int g(int n) { n }
                    }''')],

        [group: "P466 a call proved along every way into its arm", name: "an arm that writes the subject", ok: true,
         src: tc('''class A {
                        static int f(int k) {
                            switch (k) {
                                case 1:
                                    k = 2
                                case 2:
                                    return g(k)
                                default:
                                    return 0
                            }
                        }
                        @Requires({ k == 2 })
                        static int g(int k) { k }
                    }''')],

        // ---------- not every way known: the note stays ----------
        [group: "P466 a call proved along every way into its arm", name: "a case that isn't a constant", expect: ['Cannot prove precondition of g', HAVOC], refute: 'fails on',
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n, int k, int m) {
                            switch (k) {
                                case m:
                                    n = n + 1
                                case 2:
                                    return g(n)
                                default:
                                    return 0
                            }
                        }
                        @Requires({ n > 0 })
                        static int g(int n) { n }
                    }''')],

        [group: "P466 a call proved along every way into its arm", name: "an arm the replay can't follow", expect: ['Cannot prove precondition of g', HAVOC], refute: 'fails on',
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n, int k) {
                            switch (k) {
                                case 1:
                                    n = n - 1
                                    [1].each { }
                                case 2:
                                    return g(n)
                                default:
                                    return 0
                            }
                        }
                        @Requires({ n > 0 })
                        static int g(int n) { n }
                    }''')],

        [group: "P466 a call proved along every way into its arm", name: "a catch's known throws aren't all of them", expect: ['Cannot prove precondition of g', HAVOC], refute: 'fails on',
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n) {
                            int m = n
                            try {
                                if (n > 5) throw new IllegalStateException()
                                m = 0
                                h()
                                m = n
                            } catch (IllegalStateException e) {
                                return g(m)
                            }
                            return m
                        }
                        static void h() { throw new IllegalStateException() }
                        @Requires({ m > 0 })
                        static int g(int m) { m }
                    }''')],

        [group: "P466 a call proved along every way into its arm", name: "a way that fails still names its call", expect: ['Cannot prove precondition of g', 'fails on: f(1, 1)'],
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n, int k) {
                            switch (k) {
                                case 1:
                                    n = n - 1
                                case 2:
                                    return g(n)
                                default:
                                    return 0
                            }
                        }
                        @Requires({ n > 0 })
                        static int g(int n) { n }
                    }''')],
    ]
}
