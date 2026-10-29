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
 * 'P463 a call inside a try or a switch' — a call's @Requires is checked at the state at the call: the method's entry,
 * then the statements before the call replayed. The walk that collects them (collectPrefix) stopped at a `try` or a
 * `switch` around the call, so a write inside one before the call was unseen: `try { n = n - 1; return g(n) }` was
 * checked at the entry `n` (a `g` needing `n > 0` passed under `@Requires({ n > 0 })`, though `f(1)` calls `g(0)`).
 * It descends into them now: a try block's statements before the call; for a call in a catch or a finally, what the
 * try (and its catches) may have written unknown; for a switch arm, what the arms falling into it may have written.
 */
class G504_p463_call_in_try_or_switch {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 463 (soundness): a call inside a `try`, a `catch`, a `finally` or a `switch` arm is checked after the writes before it there, where they were unseen (`try { n = n - 1; return g(n) }` was checked at the entry `n`); in a catch or a finally what the try may have written is unknown, in a switch arm what the arms falling into it may have."

    static final String HAVOC = 'no failing call: the failure rests on what a statement writes inside it'

    static final List<Map> CASES = [

        // ---------- a write inside, before the call: passed before ----------
        [group: "P463 a call inside a try or a switch", name: "a write in the try block", expect: ['Cannot prove precondition of g', 'fails on: f(1)'],
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n) {
                            try {
                                n = n - 1
                                return g(n)
                            } catch (IllegalStateException e) {
                                return 0
                            }
                        }
                        @Requires({ n > 0 })
                        static int g(int n) { n }
                    }''')],

        [group: "P463 a call inside a try or a switch", name: "a write in the switch arm", expect: ['Cannot prove precondition of g', 'k = 1', 'fails on: f(1, 1)'],
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n, int k) {
                            switch (k) {
                                case 1:
                                    n = n - 1
                                    return g(n)
                                default:
                                    return 0
                            }
                        }
                        @Requires({ n > 0 })
                        static int g(int n) { n }
                    }''')],

        [group: "P463 a call inside a try or a switch", name: "an arm falling into the call's", expect: ['Cannot prove precondition of g', 'n (after a fall-through) = 0', HAVOC],
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n, int k) {
                            switch (k) {
                                case 1:
                                    n = 0
                                case 2:
                                    return g(n)
                                default:
                                    return 0
                            }
                        }
                        @Requires({ n > 0 })
                        static int g(int n) { n }
                    }''')],

        [group: "P463 a call inside a try or a switch", name: "a catch after the try wrote", expect: ['Cannot prove precondition of g', 'm (in the catch) = 0', HAVOC],
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n) {
                            int m = n
                            try {
                                m = 0
                                h()
                            } catch (IllegalStateException e) {
                                return g(m)
                            }
                            return 0
                        }
                        static void h() { throw new IllegalStateException() }
                        @Requires({ m > 0 })
                        static int g(int m) { m }
                    }''')],

        [group: "P463 a call inside a try or a switch", name: "a finally after the try wrote", expect: ['Cannot prove precondition of g', 'm (in the finally) = 0', HAVOC],
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static void f(int n) {
                            int m = n
                            try {
                                m = 0
                            } finally {
                                g(m)
                            }
                        }
                        @Requires({ m > 0 })
                        static void g(int m) { }
                    }''')],

        [group: "P463 a call inside a try or a switch", name: "an if in the try after a write", expect: ['Cannot prove precondition of g', 'fails on: f(1)'],
         src: tc('''class A {
                        static int f(int n) {
                            try {
                                n = n + 1
                                if (n != 1) return g(n)
                                return 0
                            } catch (IllegalStateException e) {
                                return 0
                            }
                        }
                        @Requires({ n != 2 })
                        static int g(int n) { n }
                    }''')],

        // ---------- the write replayed proves ----------
        [group: "P463 a call inside a try or a switch", name: "the try block's write, replayed", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            try {
                                n = n + 1
                                return g(n)
                            } catch (IllegalStateException e) {
                                return 0
                            }
                        }
                        @Requires({ n > 0 })
                        static int g(int n) { n }
                    }''')],

        [group: "P463 a call inside a try or a switch", name: "the switch arm's write, replayed", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static int f(int n, int k) {
                            switch (k) {
                                case 1:
                                    n = n + 1
                                    return g(n)
                                default:
                                    return 0
                            }
                        }
                        @Requires({ n > 0 })
                        static int g(int n) { n }
                    }''')],

        [group: "P463 a call inside a try or a switch", name: "an arm that breaks doesn't fall in", ok: true,
         src: tc('''class A {
                        @Requires({ n > 0 })
                        static int f(int n, int k) {
                            switch (k) {
                                case 1:
                                    n = 0
                                    break
                                case 2:
                                    return g(n)
                                default:
                                    return 0
                            }
                            return n
                        }
                        @Requires({ n > 0 })
                        static int g(int n) { n }
                    }''')],

        [group: "P463 a call inside a try or a switch", name: "a catch keeps what the try doesn't write", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            n = n + 1
                            try {
                                h()
                            } catch (IllegalStateException e) {
                                return g(n)
                            }
                            return 0
                        }
                        static void h() { throw new IllegalStateException() }
                        @Requires({ n > 0 })
                        static int g(int n) { n }
                    }''')],

        [group: "P463 a call inside a try or a switch", name: "the if in the try, read after the write", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            try {
                                n = n + 1
                                if (n != 2) return g(n)
                                return 0
                            } catch (IllegalStateException e) {
                                return 0
                            }
                        }
                        @Requires({ n != 2 })
                        static int g(int n) { n }
                    }''')],
    ]
}
