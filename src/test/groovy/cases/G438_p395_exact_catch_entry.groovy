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
 * 'P395 exact catch entry' — a catch was entered, for the postcondition and the obligation checks alike, with what the
 * try block writes havocked: the block may have thrown after any prefix of itself. When every throw the block can raise
 * is known (its integral divisions and explicit throws; no call, cast, index, array creation, GString or boxed read, and
 * no catch of an Error), the catch is entered exactly by Phase 387's ways — so it sees the state it threw from, and a
 * catch no throw reaches adds nothing. The loop engine has done so since Phase 391.
 */
class G438_p395_exact_catch_entry {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 395: when every throw of a try block is known, a catch is entered exactly by its ways for the postcondition and the obligations (no havoc; an unreachable catch adds nothing), else with the havoc as before."

    static final String POST = "Cannot prove postcondition of f"
    static final String CATCH = "no failing call: the failure is in a catch, in a state the try block may leave when it throws"

    static final List<Map> CASES = [

        // Before: unprovable — the catch entry havocked k (Phase 394's boundary).
        [group: "P395 exact catch entry", name: "a catch entered by a known throw sees the state it threw from",
         ok: true,
         src: tc('''class A {
                            @Ensures({ result == 7 })
                            static int f(int d) {
                                int k = 7
                                try {
                                    k = 10.intdiv(d) * 0 + 7
                                    return k
                                } catch (ArithmeticException e) {
                                    return k
                                }
                            }
                        }''')],

        [group: "P395 exact catch entry", name: "… so a write before the throw refutes",
         expect: [POST, "fails on: f(0)"],
         src: tc('''class A {
                            @Ensures({ result == 7 })
                            static int f(int d) {
                                int k = 7
                                try {
                                    k = 0
                                    k = 10.intdiv(d) * 0 + 7
                                    return k
                                } catch (ArithmeticException e) {
                                    return k
                                }
                            }
                        }''')],

        [group: "P395 exact catch entry", name: "a catch no throw reaches adds no path",
         ok: true,
         src: tc('''class A {
                            @Ensures({ result >= 0 })
                            static int f(int n) {
                                try {
                                    return n * 0
                                } catch (ArithmeticException e) {
                                    return -1
                                }
                            }
                        }''')],

        // Before: `Possible ArithmeticException … (k) != 0` with the call withheld; k is 1 whenever the catch runs.
        [group: "P395 exact catch entry", name: "an obligation in the catch, proved along its ways",
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

        // An Error (out of memory, stack overflow) may come from any statement.
        [group: "P395 exact catch entry", name: "a catch of Throwable keeps the havoc",
         expect: [POST, CATCH],
         src: tc('''class A {
                            @Ensures({ result >= 0 })
                            static int f(int n) {
                                try {
                                    return n * 0
                                } catch (Throwable e) {
                                    return -1
                                }
                            }
                        }''')],

        [group: "P395 exact catch entry", name: "… a catch of an Error too",
         expect: [POST, CATCH],
         src: tc('''class A {
                            @Ensures({ result >= 0 })
                            static int f(int n) {
                                try {
                                    return n * 0
                                } catch (StackOverflowError e) {
                                    return -1
                                }
                            }
                        }''')],

        [group: "P395 exact catch entry", name: "a boxed value may throw on unboxing: havoc",
         expect: [POST, CATCH],
         src: tc('''class A {
                            @Ensures({ result >= 0 })
                            static int f(Integer n) {
                                try {
                                    return n * 0
                                } catch (NullPointerException e) {
                                    return -1
                                }
                            }
                        }''')],

        [group: "P395 exact catch entry", name: "an array creation may throw: havoc",
         expect: [POST, CATCH],
         src: tc('''class A {
                            @Ensures({ result >= 0 })
                            static int f(int n) {
                                try {
                                    int[] a = new int[n]
                                    return 0
                                } catch (NegativeArraySizeException e) {
                                    return -1
                                }
                            }
                        }''')],

        [group: "P395 exact catch entry", name: "a GString may throw: havoc",
         expect: [POST, CATCH],
         src: tc('''class A {
                            @Ensures({ result >= 0 })
                            static int f(int n) {
                                try {
                                    String s = "${n}"
                                    return 0
                                } catch (RuntimeException e) {
                                    return -1
                                }
                            }
                        }''')],

        // Phase 192's teeth, over a block that can throw (G269's own block can't, so it now proves).
        [group: "P395 exact catch entry", name: "a block with a call keeps the havoc: a violating catch refutes",
         expect: [POST],
         src: tc('''final class A {
                            static int g(int x) { x }
                            @Ensures({ result >= 5 })
                            static int f(int n) {
                                try {
                                    return g(n) > 5 ? n : 5
                                } catch (RuntimeException e) {
                                    return 0
                                }
                            }
                        }''')],

        [group: "P395 exact catch entry", name: "… and the catch doesn't see what the block assigned",
         expect: [POST],
         src: tc('''final class A {
                            static int g(int x) { x }
                            @Ensures({ result == 2 })
                            static int f() {
                                int x = 1
                                try {
                                    x = 2
                                    x = x + g(0) * 0
                                    return x
                                } catch (RuntimeException e) {
                                    return x
                                }
                            }
                        }''')],
    ]
}
