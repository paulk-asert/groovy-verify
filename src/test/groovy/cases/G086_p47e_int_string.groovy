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

/** 'P47e int/string' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G086_p47e_int_string {

    static final List<Map> CASES = [

        // ---------- Phase 47e: Integer ↔ String conversion ----------
        // Integer.toString folds for non-negative literals (Z3 semantics: int.to.str(n) is
        // the decimal repr for n >= 0).
        [group: 'P47e int/string', name: 'Integer.toString folds for non-negative literal', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "5" })
                        static String f() { Integer.toString(5) }
                    }''')],
        // String.valueOf(int) — same lowering, useful Groovy idiom.
        [group: 'P47e int/string', name: 'String.valueOf(int) folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "42" })
                        static String f() { String.valueOf(42) }
                    }''')],
        // Integer.parseInt — round-trips for digit strings.
        [group: 'P47e int/string', name: 'Integer.parseInt folds for digit string', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 123 })
                        static int f() { Integer.parseInt("123") }
                    }''')],
        // Length composes: Integer.toString(n) for n >= 0 has at least one character.
        // (Z3 knows int.to.str(n) is "" iff n < 0, else has len >= 1 digit count.)
        // parseInt of a non-numeric literal now refutes loudly (Phase 54): Java throws
        // NumberFormatException, so the well-formedness obligation flags it (was: silently == -1).
        [group: 'P47e int/string', name: 'parseInt of non-numeric refutes (NumberFormatException)',
         expect: 'NumberFormatException',
         src: tc('''class C {
                        static int f() { Integer.parseInt("abc") }
                    }''')],
        // Refute wrong toString result.
        [group: 'P47e int/string', name: 'Integer.toString wrong-value refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == "6" })
                        static String f() { Integer.toString(5) }
                    }''')],
        // Symbolic round-trip: parseInt(toString(n)) == n for non-negative n. (Z3 verifies.)
        [group: 'P47e int/string', name: 'parseInt of toString round-trips for non-negative', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int f(int n) { Integer.parseInt(Integer.toString(n)) }
                    }''')],
    ]
}
