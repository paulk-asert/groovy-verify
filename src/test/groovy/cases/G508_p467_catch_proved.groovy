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
 * 'P467 a call proved along every way into its catch' — a call in a catch is checked with what the try block writes
 * unknown (Phase 463), and a failing call is sought along the throws Phase 387 knows (Phase 465). When every throw of
 * the block is known (Phase 391/395's exactTry: no call, index or cast that may throw) those ways are every way in, so
 * a call holding along each holds (Phase 466's proof), and a catch no throw reaches holds trivially. Both were false
 * alarms with the note.
 */
class G508_p467_catch_proved {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 467: a call in a catch is proved when it holds along every way in — each throw of the try block known (a division by zero, an explicit `throw`), the statements before it run — or no throw reaches the catch, where what the try writes left unknown refuted it with a note."

    static final String HAVOC = 'no failing call: the failure rests on what a statement writes inside it'

    static final List<Map> CASES = [

        [group: "P467 a call proved along every way into its catch", name: "a division's throw", ok: true,
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n) {
                            int m = 0
                            try {
                                m = n
                                int r = 100.intdiv(n - 5)
                                m = -1
                                return r
                            } catch (ArithmeticException e) {
                                return g(m)
                            }
                        }
                        @Requires({ m > 0 })
                        static int g(int m) { m }
                    }''')],

        [group: "P467 a call proved along every way into its catch", name: "an explicit throw", ok: true,
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n) {
                            int m = 0
                            try {
                                m = n
                                if (n > 5) throw new IllegalArgumentException()
                                m = -1
                            } catch (IllegalArgumentException e) {
                                return g(m)
                            }
                            return m
                        }
                        @Requires({ m > 5 })
                        static int g(int m) { m }
                    }''')],

        [group: "P467 a call proved along every way into its catch", name: "no throw reaches it", ok: true,
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n) {
                            int m = n
                            try {
                                m = 0
                                m = n
                            } catch (IllegalStateException e) {
                                return g(m)
                            }
                            return m
                        }
                        @Requires({ m > 0 })
                        static int g(int m) { m }
                    }''')],

        [group: "P467 a call proved along every way into its catch", name: "an earlier catch takes the throw", ok: true,
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n) {
                            int m = n
                            try {
                                m = 0
                                m = 100.intdiv(n - 5)
                            } catch (ArithmeticException e) {
                                return 0
                            } catch (Exception e) {
                                return g(m)
                            }
                            return m
                        }
                        @Requires({ m > 0 })
                        static int g(int m) { m }
                    }''')],

        // ---------- not every throw known: the note stays ----------
        [group: "P467 a call proved along every way into its catch", name: "two divisions in a statement", expect: ['Cannot prove precondition of g', HAVOC], refute: 'fails on',
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n, int k) {
                            int m = n
                            try {
                                m = 0
                                m = 100.intdiv(n - 5) + 100.intdiv(k)
                            } catch (ArithmeticException e) {
                                return g(m)
                            }
                            return m
                        }
                        @Requires({ m > 0 })
                        static int g(int m) { m }
                    }''')],

        [group: "P467 a call proved along every way into its catch", name: "a catch of Throwable", expect: ['Cannot prove precondition of g', HAVOC], refute: 'fails on',
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n) {
                            int m = n
                            try {
                                m = 0
                                m = n
                            } catch (Throwable e) {
                                return g(m)
                            }
                            return m
                        }
                        @Requires({ m > 0 })
                        static int g(int m) { m }
                    }''')],

        [group: "P467 a call proved along every way into its catch", name: "a catch of Exception past an index", expect: ['Cannot prove precondition of g', HAVOC], refute: 'fails on',
         src: tc('''class A {
                        @Requires({ n > 0 && a != null })
                        static int f(int n, int[] a) {
                            int m = n
                            try {
                                m = 0
                                m = a[n] + n
                            } catch (Exception e) {
                                return g(m)
                            }
                            return m
                        }
                        @Requires({ m > 0 })
                        static int g(int m) { m }
                    }''')],
    ]
}
