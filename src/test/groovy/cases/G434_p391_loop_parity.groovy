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
 * 'P391 loop parity' — the loop engine (an annotated loop's body, its prefix) refused a switch statement, a try, a call
 * handing a helper a closure literal, and took no division survival: each now runs as the straight-line engines do
 * (Phases 387–390). A switch is the if/else chain it runs, fall-through included; a try is the block running through or
 * a catch entered — by its exact ways when the block's throws are all known, else in a havocked state — then its
 * finally; a helper's literal argument is the helper's site frame; and a division the body moved past had a non-zero
 * divisor.
 */
class G434_p391_loop_parity {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 391: an annotated loop's body may hold a switch (fall-through too), a try/catch/finally (a catch entered by its exact ways when the block's throws are known), and a call handing a helper a closure literal, and assumes the divisions it moved past didn't throw."

    static final String PRES = "Cannot prove loop invariant is preserved by the loop body in"
    static final String HAVOC = "no failing call: the failure rests on what a statement writes inside it"

    static final List<Map> CASES = [

        [group: "P391 loop parity", name: "a switch in the loop body",
         ok: true,
         src: tc('''class A {
                            @Requires({ n >= 0 })
                            @Ensures({ result >= 0 })
                            static int f(int n) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s >= 0 })
                                @Decreases({ n - i })
                                while (i < n) {
                                    switch (i % 3) {
                                        case 0:
                                            s = s + 1
                                            break
                                        case 1:
                                            s = s + 2
                                            break
                                        default:
                                            s = s + 0
                                    }
                                    i = i + 1
                                }
                                return s
                            }
                        }''')],

        [group: "P391 loop parity", name: "… and an arm falling through to the next",
         expect: [PRES, "fails on: f(2)"],
         src: tc('''class A {
                            @Requires({ n >= 0 })
                            @Ensures({ result >= 0 })
                            static int f(int n) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s >= 0 })
                                @Decreases({ n - i })
                                while (i < n) {
                                    switch (i % 3) {
                                        case 0:
                                            s = s + 1
                                        case 1:
                                            s = s - 2
                                            break
                                        default:
                                            s = s + 0
                                    }
                                    i = i + 1
                                }
                                return s
                            }
                        }''')],

        [group: "P391 loop parity", name: "a try in the loop body whose catch is entered by a division",
         ok: true,
         src: tc('''class A {
                            @Requires({ n >= 0 })
                            @Ensures({ result >= 0 })
                            static int f(int n, int d) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s >= 0 })
                                @Decreases({ n - i })
                                while (i < n) {
                                    try {
                                        s = s + 10.intdiv(d) * 0 + 1
                                    } catch (ArithmeticException e) {
                                        s = s + 1
                                    }
                                    i = i + 1
                                }
                                return s
                            }
                        }''')],

        [group: "P391 loop parity", name: "… a catch no throw of the block reaches isn't entered",
         ok: true,
         src: tc('''class A {
                            @Requires({ n >= 0 })
                            @Ensures({ result >= 0 })
                            static int f(int n, int d) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s >= 0 })
                                @Decreases({ n - i })
                                while (i < n) {
                                    try {
                                        s = s + 1
                                    } catch (ArithmeticException e) {
                                        s = s - 5
                                    }
                                    i = i + 1
                                }
                                return s
                            }
                        }''')],

        [group: "P391 loop parity", name: "… one a division reaches is",
         expect: [PRES, "fails on: f(1, 0)"],
         src: tc('''class A {
                            @Requires({ n >= 0 })
                            @Ensures({ result >= 0 })
                            static int f(int n, int d) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s >= 0 })
                                @Decreases({ n - i })
                                while (i < n) {
                                    try {
                                        s = s + 10.intdiv(d) * 0 + 1
                                    } catch (ArithmeticException e) {
                                        s = s - 3
                                    }
                                    i = i + 1
                                }
                                return s
                            }
                        }''')],

        [group: "P391 loop parity", name: "a finally in the loop body",
         ok: true,
         src: tc('''class A {
                            @Requires({ n >= 0 })
                            @Ensures({ result == n })
                            static int f(int n) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s == i })
                                @Decreases({ n - i })
                                while (i < n) {
                                    try {
                                        s = s + 1
                                    } finally {
                                        i = i + 1
                                    }
                                }
                                return s
                            }
                        }''')],

        [group: "P391 loop parity", name: "a catch after a call: entered in any state the block leaves",
         ok: true,
         src: tc('''final class A {
                            @Ensures({ result >= 0 })
                            static int g(int x) { x * x }
                            @Requires({ n >= 0 })
                            @Ensures({ result >= 0 })
                            static int f(int n) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s >= 0 })
                                @Decreases({ n - i })
                                while (i < n) {
                                    try {
                                        s = s + g(i)
                                    } catch (RuntimeException e) {
                                        s = 0
                                    }
                                    i = i + 1
                                }
                                return s
                            }
                        }''')],

        [group: "P391 loop parity", name: "… whose refutation shows no call",
         expect: [PRES, HAVOC], refute: "fails on",
         src: tc('''final class A {
                            @Ensures({ result >= 0 })
                            static int g(int x) { x * x }
                            @Requires({ n >= 0 })
                            @Ensures({ result >= 0 })
                            static int f(int n) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s >= 0 })
                                @Decreases({ n - i })
                                while (i < n) {
                                    try {
                                        s = s + g(i)
                                    } catch (RuntimeException e) {
                                        s = -1
                                    }
                                    i = i + 1
                                }
                                return s
                            }
                        }''')],

        [group: "P391 loop parity", name: "a helper handed a closure literal in the loop body",
         expect: ["Cannot invoke method call() on null object"], refute: "Skipped loop verification",
         src: tc('''final class A {
                            static void h(Closure c, int[] b) { c.call(b) }
                            @Requires({ a != null && n >= 0 && a.length > 0 && a[0] == 7 })
                            @Ensures({ a[0] == 7 })
                            static void g(int[] a, int n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && a[0] == 7 })
                                @Decreases({ n - i })
                                while (i < n) {
                                    h({ int[] x -> int y = 0 }, a)
                                    i = i + 1
                                }
                            }
                        }''')],

        [group: "P391 loop parity", name: "… and one that writes the array",
         expect: [PRES, "fails on: g([7] as int[], 1)"],
         src: tc('''final class A {
                            static void h(Closure c, int[] b) { c.call(b) }
                            @Requires({ a != null && n >= 0 && a.length > 0 && a[0] == 7 })
                            @Ensures({ a[0] == 7 })
                            static void g(int[] a, int n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && a[0] == 7 })
                                @Decreases({ n - i })
                                while (i < n) {
                                    h({ int[] x -> x[0] = 1 }, a)
                                    i = i + 1
                                }
                            }
                        }''')],

        [group: "P391 loop parity", name: "a division the body moved past didn't divide by zero",
         expect: ["Possible ArithmeticException: Division by zero"], refute: "Cannot prove loop invariant",
         src: tc('''class A {
                            @Requires({ n >= 0 })
                            @Ensures({ result >= 0 })
                            static int f(int n, int d) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s >= 0 })
                                @Decreases({ n - i })
                                while (i < n) {
                                    int q = 10.intdiv(d)
                                    if (d == 0) s = s - 1
                                    i = i + 1
                                }
                                return s
                            }
                        }''')],

        [group: "P391 loop parity", name: "… unless a short-circuit may skip it",
         expect: [PRES, "fails on: f(1, 0)"],
         src: tc('''class A {
                            @Requires({ n >= 0 })
                            @Ensures({ result >= 0 })
                            static int f(int n, int d) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s >= 0 })
                                @Decreases({ n - i })
                                while (i < n) {
                                    boolean ok = d != 0 && 10.intdiv(d) > 0
                                    if (d == 0) s = s - 1
                                    i = i + 1
                                }
                                return s
                            }
                        }''')],

        [group: "P391 loop parity", name: "a switch on a non-constant label skips loudly",
         expect: ["a switch in a loop region"],
         src: tc('''class A {
                            @Requires({ n >= 0 && k >= 0 })
                            @Ensures({ result >= 0 })
                            static int f(int n, int k) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s >= 0 })
                                @Decreases({ n - i })
                                while (i < n) {
                                    switch (i) {
                                        case k:
                                            s = s + 1
                                            break
                                        default:
                                            s = s + 0
                                    }
                                    i = i + 1
                                }
                                return s
                            }
                        }''')],

        [group: "P391 loop parity", name: "… as does an arm that continues",
         expect: ["a switch in a loop region"],
         src: tc('''class A {
                            @Requires({ n >= 0 })
                            @Ensures({ result >= 0 })
                            static int f(int n) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s >= 0 })
                                @Decreases({ n - i })
                                while (i < n) {
                                    i = i + 1
                                    switch (i % 2) {
                                        case 0:
                                            continue
                                        default:
                                            s = s + 1
                                    }
                                }
                                return s
                            }
                        }''')],

        [group: "P391 loop parity", name: "a try that returns from the loop skips loudly",
         expect: ["a try in a loop region that returns"],
         src: tc('''class A {
                            @Requires({ n >= 0 })
                            @Ensures({ result >= 0 })
                            static int f(int n, int d) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n && s >= 0 })
                                @Decreases({ n - i })
                                while (i < n) {
                                    try {
                                        s = s + 1
                                    } catch (ArithmeticException e) {
                                        return 0
                                    }
                                    i = i + 1
                                }
                                return s
                            }
                        }''')],
    ]
}
