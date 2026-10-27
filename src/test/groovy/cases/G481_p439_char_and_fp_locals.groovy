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
 * 'P439 char and floating-point locals' — Phase 429 gave an unwritten local Groovy's default, but not a `char`, `float`
 * or `double` one; probing why, those locals were off the postcondition path even when written. `char c = 'a'` skipped
 * with `internal: Sorts Int and String are incompatible` (the literal is a one-character String to the model), and a
 * `double` local was minted an Int, so `double d = p` skipped with `Sorts Int and (_ FloatingPoint 11 53)` and
 * `double d = 1.5d` with `assignment 'd = 1.5' is outside fragment`.
 *
 * A `char` literal written to a `char` is its code point now (the model holds a char as an int), and a `double`/`float`
 * local is an IEEE-754 value (Phase 73's theory) written and re-read through its SSA versions. An unwritten one holds
 * Groovy's default, `'\u0000'` or `0.0`.
 */
class G481_p439_char_and_fp_locals {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 439: char and double/float locals are on the postcondition path — a char literal written as its code point, an IEEE-754 local written and re-read — and an unwritten one holds Groovy's default ('\\u0000', 0.0); each skipped with an internal sort error before."

    static final List<Map> CASES = [

        // `internal: Sorts Int and String are incompatible`
        [group: "P439 char and floating-point locals", name: "a char local written and defaulted",
         ok: true,
         src: tc('''class A {
                        @Ensures({ result == 97 })
                        static char c1() { char c = 'a'; return c }
                        @Ensures({ result == 0 })
                        static char c0() { char c; return c }
                    }''')],

        [group: "P439 char and floating-point locals", name: "… an unwritten char is '\\u0000'",
         expect: ["Cannot prove postcondition of c2", "fails on: c2(false)"],
         src: tc('''class A {
                        @Ensures({ result > 0 })
                        static char c2(boolean b) { char c; if (b) { c = 'a' }; return c }
                    }''')],

        // `assignment 'd = 1.5' is outside fragment`, `Sorts Int and (_ FloatingPoint 11 53)`
        [group: "P439 char and floating-point locals", name: "a double or float local written, re-read and defaulted",
         ok: true,
         src: tc('''class A {
                        @Ensures({ result == 1.5d })
                        static double d1() { double d = 1.5d; return d }
                        @Ensures({ result == 4.0d })
                        static double d2() { double d = 2.0d; d = d * 2.0d; return d }
                        @Ensures({ result == 0.0d })
                        static double d0() { double d; return d }
                        @Ensures({ result >= 0.0d })
                        static double d4(boolean b) { double d; if (b) { d = 1.5d }; return d }
                        @Ensures({ result == 0.0f })
                        static float f0() { float f; return f }
                        @Ensures({ result == 1 })
                        static int g1() { double d = 2.0d; d = d * 2.0d; if (d > 3.0d) { return 1 } else { return 0 } }
                    }''')],

        [group: "P439 char and floating-point locals", name: "… an unwritten double is 0.0",
         expect: ["Cannot prove postcondition of d3", "fails on: d3(false)"],
         src: tc('''class A {
                        @Ensures({ result > 0.0d })
                        static double d3(boolean b) { double d; if (b) { d = 1.5d }; return d }
                    }''')],

        [group: "P439 char and floating-point locals", name: "a parameter's value through a double local",
         expect: "Cannot prove postcondition of d2",
         src: tc('''class A {
                        @Ensures({ result > 0.0d })
                        static double d2(double p) { double d = p; return d }
                    }''')],
    ]
}
