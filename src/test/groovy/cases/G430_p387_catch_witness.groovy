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
 * 'P387 catch witness' — a catch is entered in any state the try block may leave when it throws, which the check
 * havocs (Phases 192, 373). An obligation inside a catch then showed no call, and a postcondition on a path through
 * one showed the model's — often one that never enters it (`f(-2147483648)` for a catch only `d == 0` reaches). The
 * call is now sought along the exact ways in: the try block up to a throw this catch takes (a division by an integral
 * zero, an `if (c) throw new X(…)`), its earlier statements run through with their own throws not happening.
 */
class G430_p387_catch_witness {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 387: a failure inside a catch (an obligation, or a postcondition on a path through it) shows a failing call from an exact run that throws into the catch — a division by zero or an explicit throw this catch takes — else withholds it."

    static final String DIV = "Possible ArithmeticException: Division by zero"
    static final String POST = "Cannot prove postcondition of f"
    static final String HAVOC = "no failing call: the failure rests on what a statement writes inside it"
    static final String CATCH = "no failing call: the failure is in a catch, in a state the try block may leave when it throws"

    static final List<Map> CASES = [

        // Before: no call (the catch-entry havoc). The catch is entered by d == 0.
        [group: "P387 catch witness", name: "a division in the try throws into the catch",
         expect: [DIV, "fails on: f(0, 0)"],
         src: tc('''class A {
                        static int f(int n, int d) {
                            try {
                                return 10.intdiv(d)
                            } catch (ArithmeticException e) {
                                return 10.intdiv(n)
                            }
                        }
                    }''')],

        [group: "P387 catch witness", name: "a write before the throw is seen in the catch",
         expect: [DIV, "fails on: f(0)"],
         src: tc('''class A {
                        static int f(int d) {
                            int k = 1
                            try {
                                k = 0
                                return 10.intdiv(d)
                            } catch (ArithmeticException e) {
                                return 10.intdiv(k)
                            }
                        }
                    }''')],

        // `k = 10 % d` throws before its write: k is still 1 in the catch
        [group: "P387 catch witness", name: "… and a throwing write isn't",
         expect: [DIV, "fails on: f(-1, 0)"],
         src: tc('''class A {
                        static int f(int n, int d) {
                            int k = 1
                            try {
                                k = 10 % d
                                k = 0
                                return 1
                            } catch (ArithmeticException e) {
                                return 10.intdiv(k + n)
                            }
                        }
                    }''')],

        [group: "P387 catch witness", name: "an explicit throw's condition enters the catch",
         expect: [DIV, "fails on: f(1)"],
         src: tc('''class A {
                        static int f(int n) {
                            int k = 5
                            try {
                                k = n
                                if (n < 3) throw new IllegalArgumentException('small')
                                return 1
                            } catch (IllegalArgumentException e) {
                                return 10.intdiv(k - 1)
                            }
                        }
                    }''')],

        [group: "P387 catch witness", name: "a user exception's subclass is taken by its catch",
         expect: [DIV, "fails on: f(11)"],
         src: tc('''class A {
                        static int f(int n) {
                            int k = 5
                            try {
                                k = n
                                if (n > 10) throw new TooBig()
                                return 1
                            } catch (TooBig e) {
                                return 100.intdiv(k - 11)
                            }
                        }
                    }
                    class TooBig extends RuntimeException { }''')],

        [group: "P387 catch witness", name: "a catch of Exception takes the division",
         expect: [DIV, "fails on: f(0, 0)"],
         src: tc('''class A {
                        static int f(int n, int d) {
                            try {
                                return 10.intdiv(d)
                            } catch (Exception e) {
                                return 10.intdiv(n)
                            }
                        }
                    }''')],

        [group: "P387 catch witness", name: "a catch in a loop: the iteration that throws",
         expect: [DIV, "fails on: f(0, 0)"],
         src: tc('''class A {
                        static int f(int n, int d) {
                            int s = 0
                            for (int i = 0; i < 3; i++) {
                                try {
                                    s = s + 10.intdiv(d)
                                } catch (ArithmeticException e) {
                                    s = s + 10.intdiv(n - i)
                                }
                            }
                            return s
                        }
                    }''')],

        // The earlier catch takes every ArithmeticException, so no run reaches this one by the division. Phase 395 — the
        // block's throws are all known, so that is a proof (it was a warning with the call withheld)
        [group: "P387 catch witness", name: "a throw an earlier catch takes doesn't enter a later one",
         ok: true,
         src: tc('''class A {
                        static int f(int n, int d) {
                            try {
                                return 10.intdiv(d)
                            } catch (ArithmeticException e) {
                                return 1
                            } catch (RuntimeException e) {
                                return 10.intdiv(n)
                            }
                        }
                    }''')],

        // Phase 395 — proved: the IllegalStateException never enters a catch of IllegalArgumentException
        [group: "P387 catch witness", name: "a throw of another type doesn't enter it",
         ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            int k = 5
                            try {
                                k = n
                                if (n > 10) throw new IllegalStateException('big')
                                return 1
                            } catch (IllegalArgumentException e) {
                                return 100.intdiv(k - 11)
                            }
                        }
                    }''')],

        // k is 1 whenever the catch runs, so no run fails. Phase 395 — and the check proves it (its entry was the havoc)
        [group: "P387 catch witness", name: "no run that throws fails: proved",
         ok: true,
         src: tc('''class A {
                        static int f(int n, int d) {
                            int k = n
                            try {
                                k = 1
                                return 10.intdiv(d)
                            } catch (ArithmeticException e) {
                                return 10.intdiv(k)
                            }
                        }
                    }''')],

        [group: "P387 catch witness", name: "a call before the throw: its throws aren't known, no call",
         expect: [DIV, HAVOC], refute: "fails on",
         src: tc('''class A {
                        static int g() { 1 }
                        static int f(int n, int d) {
                            int k = 1
                            try {
                                k = g()
                                return 10.intdiv(d)
                            } catch (ArithmeticException e) {
                                return 10.intdiv(n)
                            }
                        }
                    }''')],

        // Before: a second report, `fails on: f(-2147483648)`, which returns 0.
        [group: "P387 catch witness", name: "a postcondition on the catch's return: a call that throws there",
         expect: [POST, "fails on: f(0)"], refute: "f(-2147483648)",
         src: tc('''class A {
                        @Ensures({ result >= 0 })
                        static int f(int d) {
                            try {
                                return 10.intdiv(d)
                            } catch (ArithmeticException e) {
                                return -1
                            }
                        }
                    }''')],

        // Before: `fails on: f(0, 0)`, which returns 0.
        [group: "P387 catch witness", name: "… with the try's write before the throw",
         expect: [POST, "fails on: f(-2147483648, 0)"], refute: "f(0, 0)",
         src: tc('''class A {
                        @Ensures({ result >= 0 })
                        static int f(int n, int d) {
                            int k = 0
                            try {
                                k = n
                                return 10.intdiv(d)
                            } catch (ArithmeticException e) {
                                return k
                            }
                        }
                    }''')],

        [group: "P387 catch witness", name: "… a try inside a branch",
         expect: [POST, "fails on: f(-2147483648, 0, true)"],
         src: tc('''class A {
                        @Ensures({ result >= 0 })
                        static int f(int n, int d, boolean c) {
                            int k = 0
                            if (c) {
                                try {
                                    k = n
                                    return 10.intdiv(d)
                                } catch (ArithmeticException e) {
                                    return k
                                }
                            }
                            return 0
                        }
                    }''')],

        [group: "P387 catch witness", name: "… withheld when no way in is known",
         expect: [POST, CATCH],
         src: tc('''class A {
                        static int g() { 1 }
                        @Ensures({ result >= 0 })
                        static int f(int n, int d) {
                            int k = 0
                            try {
                                k = n + g()
                                return 10.intdiv(d)
                            } catch (ArithmeticException e) {
                                return k
                            }
                        }
                    }''')],

        // Phase 223's exact entry (nothing havocked, the spec's fact assumed) keeps its call
        [group: "P387 catch witness", name: "a characterised catch entry keeps its call",
         expect: [POST, 'fails on: f("")'],
         src: tc('''class A {
                        @Ensures({ result >= 0 })
                        static int f(String s) {
                            try {
                                return Integer.parseInt(s)
                            } catch (NumberFormatException e) {
                                return -1
                            }
                        }
                    }''')],
    ]
}
