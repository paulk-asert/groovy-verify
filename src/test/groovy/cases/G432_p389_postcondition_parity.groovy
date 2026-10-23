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
 * 'P389 postcondition parity' — the obligation checks follow a finally, a switch fall-through and a write inside an
 * expression (Phases 373–374); the postcondition's path walk skipped all three loudly. A finally now runs after the
 * block or a catch (one that falls through, with the try's return value kept when it doesn't write what that reads);
 * an arm without a break runs on into the next; and a statement writing inside its expression runs in Java's
 * evaluation order, one path per way through its short-circuits.
 */
class G432_p389_postcondition_parity {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 389: a postcondition is proved (or refuted) through a finally, a switch arm that falls through, and a write inside an expression (`(n = m) + n`), which were skipped loudly."

    static final String POST = "Cannot prove postcondition of f"

    static final List<Map> CASES = [

        // Before (each): `Skipped verification of postcondition for f ('finally' unsupported …)`.
        [group: "P389 postcondition parity", name: "a finally runs after the block",
         ok: true,
         src: tc('''class A {
                        @Ensures({ result == n + 1 })
                        static int f(int n) {
                            int k = n
                            try {
                                k = k + 1
                            } finally {
                                k = k + 0
                            }
                            return k
                        }
                    }''')],

        [group: "P389 postcondition parity", name: "… and its writes count",
         expect: [POST, "fails on: f("],
         src: tc('''class A {
                        @Ensures({ result == n })
                        static int f(int n) {
                            int k = n
                            try {
                                k = k + 1
                            } finally {
                                k = k * 2
                            }
                            return k
                        }
                    }''')],

        [group: "P389 postcondition parity", name: "a return in the try keeps its value through the finally",
         ok: true,
         src: tc('''class A {
                        @Ensures({ result == n })
                        static int f(int n) {
                            int k = 0
                            try {
                                return n
                            } finally {
                                k = 1
                            }
                        }
                    }''')],

        // 10.intdiv(-6) is -1 (truncated); -1 + 1 is 0
        [group: "P389 postcondition parity", name: "a finally after a catch",
         expect: [POST, "fails on: f(-6)"],
         src: tc('''class A {
                        @Ensures({ result != 0 })
                        static int f(int d) {
                            int k = 0
                            try {
                                k = 10.intdiv(d)
                            } catch (ArithmeticException e) {
                                k = -1
                            } finally {
                                k = k + 1
                            }
                            return k
                        }
                    }''')],

        // The boundary: the return's value is read before the finally runs, which the walk doesn't snapshot
        [group: "P389 postcondition parity", name: "a finally writing what the return reads skips loudly",
         expect: "'finally' writes what the try's return reads",
         src: tc('''class A {
                        @Ensures({ result == n })
                        static int f(int n) {
                            int k = n
                            try {
                                return k
                            } finally {
                                k = 0
                            }
                        }
                    }''')],

        [group: "P389 postcondition parity", name: "a finally that returns skips loudly",
         expect: "'finally' that returns, throws or breaks",
         src: tc('''class A {
                        @Ensures({ result == n })
                        static int f(int n) {
                            int k = n
                            try {
                                k = 1
                            } finally {
                                return k
                            }
                        }
                    }''')],

        // Before: `switch case falls through to the next … only arms that leave are modelled`.
        [group: "P389 postcondition parity", name: "a switch arm falls through to the next",
         ok: true,
         src: tc('''class A {
                        @Ensures({ result >= 1 })
                        static int f(int n) {
                            int r = 0
                            switch (n) {
                                case 1:
                                    r = r + 1
                                case 2:
                                    r = r + 1
                                    break
                                default:
                                    r = 5
                            }
                            return r
                        }
                    }''')],

        [group: "P389 postcondition parity", name: "… and the run it takes counts",
         expect: [POST, "fails on: f(1)"],
         src: tc('''class A {
                        @Ensures({ result == 1 || result == 5 })
                        static int f(int n) {
                            int r = 0
                            switch (n) {
                                case 1:
                                    r = r + 1
                                case 2:
                                    r = r + 1
                                    break
                                default:
                                    r = 5
                            }
                            return r
                        }
                    }''')],

        [group: "P389 postcondition parity", name: "stacked labels share an arm",
         ok: true,
         src: tc('''class A {
                        @Ensures({ result == (n == 1 || n == 2 ? 1 : 0) })
                        static int f(int n) {
                            int r = 0
                            switch (n) {
                                case 1:
                                case 2:
                                    r = 1
                                    break
                                default:
                                    r = 0
                            }
                            return r
                        }
                    }''')],

        [group: "P389 postcondition parity", name: "a case falls into the default",
         expect: [POST, "fails on: f(1)"],
         src: tc('''class A {
                        @Ensures({ result == 1 })
                        static int f(int n) {
                            int r = 0
                            switch (n) {
                                case 1:
                                    r = 1
                                default:
                                    r = r + 1
                            }
                            return r
                        }
                    }''')],

        // Before: `assignment 'r = ((n = m) + n)' is outside fragment`.
        [group: "P389 postcondition parity", name: "a write inside an expression, in evaluation order",
         ok: true,
         src: tc('''class A {
                        @Ensures({ result == 2 * m })
                        static int f(int m) {
                            int n = 0
                            int r = (n = m) + n
                            return r
                        }
                    }''')],

        [group: "P389 postcondition parity", name: "… which a wrong claim refutes",
         expect: [POST, "fails on: f("],
         src: tc('''class A {
                        @Ensures({ result == m })
                        static int f(int m) {
                            int n = 0
                            int r = (n = m) + n
                            return r
                        }
                    }''')],

        [group: "P389 postcondition parity", name: "… in a return",
         ok: true,
         src: tc('''class A {
                        @Ensures({ result == 2 * m })
                        static int f(int m) {
                            int n = 0
                            return (n = m) + n
                        }
                    }''')],

        [group: "P389 postcondition parity", name: "… in a branch condition",
         ok: true,
         src: tc('''class A {
                        @Requires({ m > -1000 })
                        @Ensures({ result >= 0 })
                        static int f(int m) {
                            int n = 0
                            if ((n = m) < 0) return -n
                            return n
                        }
                    }''')],

        // Teeth: the write happens only when the short-circuit gets to it — for 0 < m <= 5, n is m and f returns it
        [group: "P389 postcondition parity", name: "a write a short-circuit may skip",
         expect: [POST, "fails on: f(1)"],
         src: tc('''class A {
                        @Ensures({ result > 5 || result == 0 })
                        static int f(int m) {
                            int n = 7
                            if (m > 0 && (n = m) > 5) return 0
                            return n
                        }
                    }''')],

        [group: "P389 postcondition parity", name: "… and one it reaches",
         ok: true,
         src: tc('''class A {
                        @Ensures({ result > 5 || result == 0 })
                        static int f(int m) {
                            int n = 0
                            if (m > 0 && (n = m) > 5) return n
                            return 0
                        }
                    }''')],
    ]
}
