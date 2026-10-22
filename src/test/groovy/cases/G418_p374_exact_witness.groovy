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
 * 'P374 exact witness' — Phase 373 havocked what a statement writes inside it, and a try's or a switch's other ways in,
 * and withheld the failing call. The havocked check still decides the obligation; on a refutation, a witness is now
 * sought along the exact ways the statement runs: its expression lowered in evaluation order (a nested write where
 * Java makes it, each `&&`/`||`/ternary/elvis way with its condition assumed), a try run through to its finally, a
 * switch by each entry and the arms it falls through. The first way that refutes gives the call. And an increment in
 * a short-circuit's right operand is no longer hoisted out of it, where it ran always.
 */
class G418_p374_exact_witness {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 374: a failure behind a nested write, a finally, a fall-through or a switch gets its failing call from an exact replay of the ways the statement runs (evaluation order, each short-circuit way, try-then-finally, each switch entry); an increment in a short-circuit right operand is not hoisted out of it.'

    static final String DIV = 'Possible ArithmeticException: Division by zero'

    static final List<Map> CASES = [

        // Before: compiled cleanly — `i++` was hoisted out of the `&&`, so i == 1 even when b is false.
        [group: "P374 exact witness", name: "an increment under &&",
         expect: [DIV, "fails on: f(false)"],
         src: tc('''class A {
                        static int f(boolean b) {
                            int i = 0
                            boolean t = b && (i++ >= 0)
                            100.intdiv(i)
                        }
                    }''')],

        // Before: compiled cleanly.
        [group: "P374 exact witness", name: "an increment under ||",
         expect: [DIV, "fails on: f(true)"],
         src: tc('''class A {
                        static int f(boolean b) {
                            int i = 0
                            boolean t = b || (++i > 0)
                            100.intdiv(i)
                        }
                    }''')],

        // Before: the postcondition proved, over the hoisted increment. Now it is skipped, loudly.
        [group: "P374 exact witness", name: "a postcondition over an increment under &&",
         expect: "Skipped verification of postcondition for f", refute: "Cannot prove",
         src: tc('''class A {
                        @Ensures({ result == 1 })
                        static int f(boolean b) {
                            int i = 0
                            boolean t = b && (i++ >= 0)
                            i
                        }
                    }''')],

        // The left operand always runs: its increment is hoisted as before.
        [group: "P374 exact witness", name: "an increment in an always-evaluated operand",
         ok: true,
         src: tc('''class A {
                        static int f(boolean b) {
                            int i = 0
                            boolean t = (i++ >= 0) && b
                            100.intdiv(i)
                        }
                    }''')],

        // Before: reported with no failing call (Phase 373's note).
        [group: "P374 exact witness", name: "an increment in a ternary arm",
         expect: [DIV, "fails on: f(false)"],
         src: tc('''class A {
                        static int f(boolean b) {
                            int i = 0
                            int x = b ? i++ : 5
                            100.intdiv(i)
                        }
                    }''')],

        // Before: reported with no failing call.
        [group: "P374 exact witness", name: "a try inside a try",
         expect: [DIV, "fails on: f(1)"],
         src: tc('''class A {
                        static int f(int n) {
                            int d = 1
                            try {
                                try { d = n } finally { d = d - 1 }
                            } finally {
                                int q = 100.intdiv(d)
                            }
                            d
                        }
                    }''')],

        // Before: reported with no failing call. The way through no case.
        [group: "P374 exact witness", name: "a switch without a default",
         expect: [DIV, "fails on: f("], refute: ["fails on: f(1)", "fails on: f(2)"],
         src: tc('''class A {
                        static int f(int k) {
                            int d = 0
                            switch (k) {
                                case 1: d = 1; break
                                case 2: d = 2; break
                            }
                            100.intdiv(d)
                        }
                    }''')],

        // Before: reported with no failing call.
        [group: "P374 exact witness", name: "a switch on a string, falling through",
         expect: [DIV, 'fails on: f("a")'],
         src: tc('''class A {
                        static int f(String s) {
                            int d = 1
                            switch (s) {
                                case 'a': d = 0
                                case 'b': d = d + 0; break
                                default: d = 1
                            }
                            100.intdiv(d)
                        }
                    }''')],

        // Before: reported with no failing call. The way past the early return, which isn't taken.
        [group: "P374 exact witness", name: "a finally after an early return not taken",
         expect: [DIV, "fails on: f(3)"],
         src: tc('''class A {
                        static int f(int n) {
                            int d = 1
                            try {
                                if (n > 5) return 1
                                d = n - 3
                            } finally {
                                int q = 100.intdiv(d)
                            }
                            d
                        }
                    }''')],

        // Before: reported with no failing call. The loop's unrolled iterations are lowered too.
        [group: "P374 exact witness", name: "a nested write in a loop body",
         expect: [DIV, "fails on: f(3)"],
         src: tc('''class A {
                        static int f(int n) {
                            int s = 0
                            for (int i = 0; i < n; i++) {
                                int d = 1
                                int x = (i == 2) ? (d = 0) : 1
                                s += 100.intdiv(d)
                            }
                            s
                        }
                    }''')],

        // A case that isn't a constant (a range) has no exact entry condition: the note stays.
        [group: "P374 exact witness", name: "a switch over a range keeps the note",
         expect: [DIV, "d (after the switch) = 0", "no failing call: the failure rests on what a statement writes inside it"],
         refute: "fails on",
         src: tc('''class A {
                        static int f(int k) {
                            int d = 1
                            switch (k) {
                                case 1..3: d = 0
                                case 4: d = d + 0; break
                                default: d = 1
                            }
                            100.intdiv(d)
                        }
                    }''')],
    ]
}
