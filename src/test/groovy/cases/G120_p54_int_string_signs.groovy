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

/** 'P54 int-string signs' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G120_p54_int_string_signs {

    static final List<Map> CASES = [

        // ---------- Phase 54: sign-faithful Integer.toString / parseInt ----------
        // toString of a negative int is non-empty ("-7"); the old raw `intToString` modelled it as ""
        // and silently *verified* result.isEmpty() — now fixed.
        [group: 'P54 int-string signs', name: 'negative toString is non-empty', ok: true,
         src: tc('''class C {
                        @Requires({ n < 0 })
                        @Ensures({ !result.isEmpty() })
                        static String f(int n) { Integer.toString(n) }
                    }''')],
        [group: 'P54 int-string signs', name: 'negative toString isEmpty now refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ n < 0 })
                        @Ensures({ result.isEmpty() })
                        static String f(int n) { Integer.toString(n) }
                    }''')],
        // toString(-7) == "-7" exactly.
        [group: 'P54 int-string signs', name: 'toString of a specific negative', ok: true,
         src: tc('''class C {
                        @Requires({ n == -7 })
                        @Ensures({ result == "-7" })
                        static String f(int n) { Integer.toString(n) }
                    }''')],
        // Round-trip now holds for ALL n, not just n >= 0 (the old gap needed a non-negative guard).
        [group: 'P54 int-string signs', name: 'parseInt(toString(n)) == n for negative n', ok: true,
         src: tc('''class C {
                        @Requires({ n < 0 })
                        @Ensures({ result == n })
                        static int f(int n) { Integer.parseInt(Integer.toString(n)) }
                    }''')],
        // Loud obligation: parseInt of an *unconstrained* String might throw → refuted (the engine
        // no longer silently models malformed input as -1).
        [group: 'P54 int-string signs', name: 'parseInt of arbitrary string refutes (NFE)',
         expect: 'NumberFormatException',
         src: tc('''class C {
                        @Requires({ s != null })
                        static int f(String s) { Integer.parseInt(s) }
                    }''')],
        // ...and parseInt(toString(n)) is *provably* well-formed → no NumberFormatException fires.
        [group: 'P54 int-string signs', name: 'parseInt of toString is well-formed', ok: true,
         src: tc('''class C {
                        @Ensures({ result == n })
                        static int f(int n) { Integer.parseInt(Integer.toString(n)) }
                    }''')],
    ]
}
