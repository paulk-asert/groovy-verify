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

/** 'P47c regex' — 11 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G084_p47c_regex {

    static final List<Map> CASES = [

        // ---------- Phase 47c: matches with regex parser ----------
        // Literal-only regex: matches iff string equals the literal.
        [group: 'P47c regex', name: 'literal regex matches exact string', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "abc".matches("abc") ? 1 : 0 }
                    }''')],
        [group: 'P47c regex', name: 'literal regex refutes wrong string',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "abc".matches("xyz") ? 1 : 0 }
                    }''')],
        // {@code .} matches any single character.
        [group: 'P47c regex', name: 'any-char dot matches single position', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "abc".matches("a.c") ? 1 : 0 }
                    }''')],
        // Quantifier: {@code a*} matches zero or more 'a's.
        [group: 'P47c regex', name: 'star quantifier matches zero occurrences', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "".matches("a*") ? 1 : 0 }
                    }''')],
        [group: 'P47c regex', name: 'plus quantifier requires one occurrence', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { "".matches("a+") ? 1 : 0 }
                    }''')],
        // Character range: digits.
        [group: 'P47c regex', name: 'digit range matches numeric string', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "123".matches("[0-9]+") ? 1 : 0 }
                    }''')],
        [group: 'P47c regex', name: 'digit range rejects alphabetic string', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { "abc".matches("[0-9]+") ? 1 : 0 }
                    }''')],
        // Character set + range: alphanumeric.
        [group: 'P47c regex', name: 'alphanumeric class matches mixed', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "abc123".matches("[a-zA-Z0-9]+") ? 1 : 0 }
                    }''')],
        // Alternation.
        [group: 'P47c regex', name: 'alternation matches either branch', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "yes".matches("yes|no") ? 1 : 0 }
                    }''')],
        // Symbolic matches: assumed precondition flows through.
        [group: 'P47c regex', name: 'symbolic matches assumption echoes', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.matches("[0-9]+") })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches("[0-9]+") ? 1 : 0 }
                    }''')],
        // Unsupported feature: word-boundary {@code \b} isn't a single-character regex; the
        // parser bails out and the verifier emits an honest skip diagnostic.
        [group: 'P47c regex', name: 'unsupported regex feature honest-skips',
         expect: 'Skipped verification of postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "abc".matches("\\\\babc\\\\b") ? 1 : 0 }
                    }''')],
    ]
}
