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
 * 'P465 a failing call past a try or a switch' — Phase 463 checks a call in a catch, a finally or a
 * switch arm with what the try (or the arms falling in) may have written unknown, and a refutation resting on such a
 * value named no failing call. The call is now sought along the exact ways in, Phase 374's: for a catch, the try block
 * up to a throw it takes (Phase 387); for a finally, the try block run through, or a catch's way in and the catch; for
 * an arm, each entry and the arms run from it. The first way that fails is the call shown; with none, the note stays.
 */
class G506_p465_call_witness_past_try_or_switch {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 465: a call refuted in a catch, a finally or a switch arm, on what the try or the arms falling in may have written, names a failing call when one of the exact ways in fails (the try up to a throw the catch takes, run through to the finally, an arm's entry and the arms from it); with none, the note stays."

    static final String HAVOC = 'no failing call: the failure rests on what a statement writes inside it'

    static final List<Map> CASES = [

        // ---------- a way in fails: the call shown ----------
        [group: "P465 a failing call past a try or a switch", name: "a catch after a throw the try makes", expect: ['Cannot prove precondition of g', 'fails on: f(6)'],
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n) {
                            int m = n
                            try {
                                m = 0
                                if (n > 5) throw new IllegalStateException()
                                m = n
                            } catch (IllegalStateException e) {
                                return g(m)
                            }
                            return m
                        }
                        @Requires({ m > 0 })
                        static int g(int m) { m }
                    }''')],

        [group: "P465 a failing call past a try or a switch", name: "a finally reached through the catch", expect: ['Cannot prove precondition of g', 'fails on: f(6)'],
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static void f(int n) {
                            int m = n
                            try {
                                m = 0
                                if (n > 5) throw new IllegalStateException()
                                m = n
                            } catch (IllegalStateException e) {
                            } finally {
                                g(m)
                            }
                        }
                        @Requires({ m > 0 })
                        static void g(int m) { }
                    }''')],

        [group: "P465 a failing call past a try or a switch", name: "the second of two arms falling in", expect: ['Cannot prove precondition of g', 'fails on: f(1, 2)'],
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n, int k) {
                            switch (k) {
                                case 1:
                                    n = n + 1
                                case 2:
                                    n = n - 1
                                case 3:
                                    return g(n)
                                default:
                                    return 0
                            }
                        }
                        @Requires({ n > 0 })
                        static int g(int n) { n }
                    }''')],

        // ---------- no way in fails, or none is known: the note stays ----------
        [group: "P465 a failing call past a try or a switch", name: "every way into the arm holds", expect: ['Cannot prove precondition of g', HAVOC], refute: 'fails on',
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

        [group: "P465 a failing call past a try or a switch", name: "a catch no run reaches", expect: ['Cannot prove precondition of g', 'm (in the catch) = 0', HAVOC], refute: 'fails on',
         src: tc('''class A {
                        @Requires({ n > 0 && a != null && n < a.length })
                        static int f(int n, int[] a) {
                            int m = n
                            try {
                                m = 0
                                m = a[n]
                            } catch (IndexOutOfBoundsException e) {
                                return g(m)
                            }
                            return m
                        }
                        @Requires({ m > 0 })
                        static int g(int m) { m }
                    }''')],
    ]
}
