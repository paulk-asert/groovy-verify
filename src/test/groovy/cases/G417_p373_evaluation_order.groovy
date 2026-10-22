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
 * 'P373 evaluation order' — a statement can write more than its top-level target: a nested assignment
 * (`if ((n = m) >= 0 && 100.intdiv(n) > 0)`), an `i++` inside an index or an operand, a write in a ternary or elvis
 * arm, a callable's call (`c()`, `consumer.accept(this)`), whose body may write anything it reaches. And a try or a
 * switch is not one run through: a catch is entered after any prefix of the try block, a finally after the block or a
 * catch, by any exit, a case body by falling through from the case above. Sites inside and after these were checked
 * in the state before them, so their writes were missed — silently. They are now followed or havocked, and a failure
 * that rests on a havocked value has its failing call withheld, with a note — Phase 374 then seeks it along the exact
 * ways the statement runs, so only the catch and the callables below keep the note.
 */
class G417_p373_evaluation_order {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 373: writes inside a statement (nested assignments, `i++` in an operand or index, ternary/elvis arms, a callable\'s call), try blocks in order, catch and finally after any prefix or exit, and switch fall-through are followed or havocked for the sites inside and after them; a failure resting on such a havoc has its failing call withheld.'

    static final String NOTE = 'no failing call: the failure rests on what a statement writes inside it'

    static final List<Map> CASES = [

        // Before: compiled cleanly — the finally's divisor was read as d == 1.
        [group: "P373 evaluation order", name: "a finally after a return",
         expect: ["Possible ArithmeticException: Division by zero", "fails on: f(0)"],  // Phase 374 — its exact witness
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            int d = 1
                            try {
                                d = 0
                                return n
                            } finally {
                                int q = 100.intdiv(d)
                            }
                        }
                    }''')],

        // Before: compiled cleanly.
        [group: "P373 evaluation order", name: "a finally after normal completion",
         expect: ["Possible ArithmeticException: Division by zero", "fails on: f(0)"],  // Phase 374 — its exact witness
         src: tc('''class A {
                        static int f(int n) {
                            int d = 1
                            try {
                                d = n
                            } finally {
                                int q = 100.intdiv(d)
                            }
                            d
                        }
                    }''')],

        // Before: compiled cleanly — the try block's divisor was read in the state before the try.
        [group: "P373 evaluation order", name: "a try block runs in order",
         expect: "Possible ArithmeticException: Division by zero",
         src: tc('''class A {
                        static int f() {
                            int d = 1
                            try {
                                d = 0
                                return 100.intdiv(d)
                            } catch (IllegalStateException e) {
                                return 0
                            }
                        }
                    }''')],

        // Before: compiled cleanly.
        [group: "P373 evaluation order", name: "a catch sees the try block's writes",
         expect: ["Possible ArithmeticException: Division by zero", "d (in the catch) = 0", NOTE],
         src: tc('''class A {
                        static int f(String s) {
                            int d = 1
                            try {
                                d = 0
                                Integer.parseInt(s)
                            } catch (NumberFormatException e) {
                                return 100.intdiv(d)
                            }
                            0
                        }
                    }''')],

        // Before: reported — the try, which the replay can't follow, was havocked whole — but shown as "after a loop".
        [group: "P373 evaluation order", name: "after a try with a finally",
         expect: ["Possible ArithmeticException: Division by zero", "fails on: f()"],  // Phase 374 — its exact witness
         src: tc('''class A {
                        static int f() {
                            int d = 1
                            try {
                                d = 2
                            } finally {
                                d = 0
                            }
                            100.intdiv(d)
                        }
                    }''')],

        // Before: compiled cleanly — case 2's body was checked as if only entered by its own match.
        [group: "P373 evaluation order", name: "a case body entered by falling through",
         expect: ["Possible ArithmeticException: Division by zero", "fails on: f(1)"],  // Phase 374 — its exact witness
         src: tc('''class A {
                        static int f(int k) {
                            int d = 1
                            int s = 0
                            switch (k) {
                                case 1: d = 0
                                case 2: s = 100.intdiv(d); break
                                default: s = 1
                            }
                            s
                        }
                    }''')],

        // Before: reported, but with `fails on: f(-2147483648)`, a call that takes the default arm and doesn't fail.
        [group: "P373 evaluation order", name: "after a switch with fall-through",
         expect: ["Possible ArithmeticException: Division by zero", "fails on: f(1)"],  // Phase 374 — its exact witness
         src: tc('''class A {
                        static int f(int k) {
                            int d = 1
                            switch (k) {
                                case 1: d = 0
                                case 2: d = d + 0; break
                                default: d = 1
                            }
                            100.intdiv(d)
                        }
                    }''')],

        // Before: compiled cleanly — the right operand read the old n.
        [group: "P373 evaluation order", name: "an assignment in a condition",
         expect: ["Possible ArithmeticException: Division by zero", "fails on: f(0)"],  // Phase 374 — its exact witness
         src: tc('''class A {
                        static int f(int m) {
                            int n = 1
                            if ((n = m) >= 0 && 100.intdiv(n) > 0) return 1
                            0
                        }
                    }''')],

        // Before: compiled cleanly — the branch read the old n.
        [group: "P373 evaluation order", name: "an assignment in an if's condition, read in its body",
         expect: ["Possible ArithmeticException: Division by zero", "fails on: f(0)"],  // Phase 374 — its exact witness
         src: tc('''class A {
                        static int f(int m) {
                            int n = 1
                            int s = 0
                            if ((n = m) >= 0) { s = 100.intdiv(n) }
                            s
                        }
                    }''')],

        // Before: compiled cleanly.
        [group: "P373 evaluation order", name: "a write in a ternary arm",
         expect: ["Possible ArithmeticException: Division by zero", "fails on: f(true)"],  // Phase 374 — its exact witness
         src: tc('''class A {
                        static int f(boolean b) {
                            int d = 1
                            int x = b ? (d = 0) : 1
                            100.intdiv(d)
                        }
                    }''')],

        // Before: compiled cleanly.
        [group: "P373 evaluation order", name: "a write in an elvis arm",
         expect: ["Possible ArithmeticException: Division by zero", "fails on: f(0)"],  // Phase 374 — its exact witness
         src: tc('''class A {
                        static int f(Integer x) {
                            int d = 1
                            Integer y = x ?: (d = 0)
                            100.intdiv(d)
                        }
                    }''')],

        // Before: compiled cleanly.
        [group: "P373 evaluation order", name: "an increment inside an operand",
         expect: ["Possible ArithmeticException: Division by zero", "fails on: f()"],  // Phase 374 — its exact witness
         src: tc('''class A {
                        static int f() {
                            int i = 0
                            int x = i++ + i
                            100.intdiv(i - 1)
                        }
                    }''')],

        // Already reported (the replay follows the index's increment); kept beside the shapes that weren't.
        [group: "P373 evaluation order", name: "an increment inside an index",
         expect: ["Possible IndexOutOfBoundsException", "fails on: f(new int[1])"],
         src: tc('''class A {
                        @Requires({ a != null && a.length == 1 })
                        static int f(int[] a) {
                            int i = 0
                            a[i++] = 5
                            a[i]
                        }
                    }''')],

        // The index is read before the value's increment: both stores are in bounds.
        [group: "P373 evaluation order", name: "an increment in a stored value",
         ok: true,
         src: tc('''class A {
                        @Requires({ a != null && a.length == 2 })
                        static int f(int[] a) {
                            int i = 0
                            a[i] = i++
                            a[i]
                        }
                    }''')],

        // Before: compiled cleanly — the closure parameter's call was taken to write nothing.
        [group: "P373 evaluation order", name: "a closure parameter's call may write a field",
         expect: ["Possible ArithmeticException: Division by zero", "count (after a callable's call) = 0"],
         refute: "fails on",
         src: tc('''class A {
                        int count = 1
                        @Requires({ c != null && count == 1 })
                        void f(Closure c) {
                            c()
                            int q = 100.intdiv(count)
                        }
                    }''')],

        // Before: compiled cleanly.
        [group: "P373 evaluation order", name: "a functional interface's call may write what it is given",
         expect: ["Possible ArithmeticException: Division by zero", "count (after a callable's call) = 0"],
         src: tc('''class A {
                        int count = 1
                        @Requires({ c != null && count == 1 })
                        void f(java.util.function.Consumer<A> c) {
                            c.accept(this)
                            int q = 100.intdiv(count)
                        }
                    }''')],

        // Before: the postcondition proved. Now it is skipped, loudly; the receiver is still checked before the call, and
        // its failing call kept (the callable runs after it).
        [group: "P373 evaluation order", name: "a postcondition over a callable's call",
         expect: ["Skipped verification of postcondition for f (call 'c.call()' runs a callable",
                  "Cannot invoke method call() on null object", "fails on: f(null)"],
         src: tc('''class A {
                        int count = 1
                        @Requires({ count == 1 })
                        @Ensures({ count == 1 })
                        void f(Closure c) {
                            c()
                        }
                    }''')],

        // Before: also `Cannot invoke method toString() on null object`. A GString literal is never null; its lazy
        // closure runs at toString(), after d = 0 (Phase 372 already reported that).
        [group: "P373 evaluation order", name: "a lazy GString",
         expect: ["Possible ArithmeticException: Division by zero", "d (when the closure runs) = 0"],
         refute: "on null object",
         src: tc('''class A {
                        static String f() {
                            int d = 1
                            GString g = "${-> 100.intdiv(d)}"
                            d = 0
                            g.toString()
                        }
                    }''')],
    ]
}
