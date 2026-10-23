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
 * 'P388 survival' — a postcondition is checked on a normal return, so every division the path moved past didn't
 * divide by zero: its divisor isn't 0 there (an assignment's value, a branch condition, the return value). The try
 * block's own return path used to refute at a model whose division throws (`return 10.intdiv(d)` at d = 0, a run
 * that goes through the catch instead). And Phase 222's survival facts for spec'd calls now cover only what is
 * evaluated on every run: `b != 0 && Math.floorDiv(a, b) > 0` assumed `b != 0` on every path — unsound.
 */
class G431_p388_survival {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 388: a path the program moved past a division on has a non-zero divisor (assignments, branch conditions, the return value), and survival facts cover only what every run evaluates — a short-circuit's right operand no longer counts (unsound before)."

    static final String POST = "Cannot prove postcondition of f"
    static final String DIV = "Possible ArithmeticException: Division by zero"

    static final List<Map> CASES = [

        // Before: the try's return refuted at d = 0 (`fails on: f(0)`, a run that throws into the catch)
        [group: "P388 survival", name: "a try's return refutes at a divisor that doesn't throw",
         expect: [POST, "fails on: f(-5)", "fails on: f(0)"],
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

        // Before: refuted at d = 0, where the assignment throws. Only the division's own obligation remains.
        [group: "P388 survival", name: "an assignment's division survived: the postcondition proves",
         expect: [DIV, "fails on: f(0)"], refute: POST,
         src: tc('''class A {
                        @Ensures({ result != 5 })
                        static int f(int d) {
                            int q = 10.intdiv(d)
                            return d + 5
                        }
                    }''')],

        [group: "P388 survival", name: "… a branch condition's",
         expect: [DIV, "fails on: f(0)"], refute: POST,
         src: tc('''class A {
                        @Ensures({ result != 5 })
                        static int f(int d) {
                            if (10.intdiv(d) > 100) return 0
                            return d + 5
                        }
                    }''')],

        [group: "P388 survival", name: "… a return value's",
         expect: [DIV, "fails on: f(0)"], refute: POST,
         src: tc('''class A {
                        @Ensures({ result != 5 })
                        static int f(int d) {
                            return d + 5 + 0 * 10.intdiv(d)
                        }
                    }''')],

        // Teeth: a short-circuit may skip its right operand
        [group: "P388 survival", name: "a division a short-circuit skips gives no fact",
         expect: [POST, "fails on: f(0)"],
         src: tc('''class A {
                        @Ensures({ result != 5 })
                        static int f(int d) {
                            boolean ok = d != 0 && 10.intdiv(d) > 0
                            return d + 5
                        }
                    }''')],

        [group: "P388 survival", name: "… nor a ternary's arm",
         expect: [POST, "fails on: f(0)"],
         src: tc('''class A {
                        @Ensures({ result != 5 })
                        static int f(int d) {
                            int q = d == 0 ? 0 : 10.intdiv(d)
                            return d + 5
                        }
                    }''')],

        // Before: compiled cleanly — Phase 222 assumed floorDiv's `b == 0` arm false on every path. f(0, 0) returns 0.
        [group: "P388 survival", name: "a spec'd call a short-circuit skips gives no fact (unsound before)",
         expect: [POST, "fails on: f(0, 0)"],
         src: tc('''class A {
                        @Ensures({ result != 0 })
                        static int f(int a, int b) {
                            boolean ok = b != 0 && Math.floorDiv(a, b) > 0
                            return b
                        }
                    }''')],

        // … and an evaluated one still does (Phase 222): the call's own obligation stays, the postcondition proves
        [group: "P388 survival", name: "an evaluated spec'd call still gives its fact",
         expect: "Math.floorDiv(a, b) throws when b == 0", refute: POST,
         src: tc('''class A {
                        @Ensures({ result != 0 })
                        static int f(int a, int b) {
                            int q = Math.floorDiv(a, b)
                            return b
                        }
                    }''')],
    ]
}
