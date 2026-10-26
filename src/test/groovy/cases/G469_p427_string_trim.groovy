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
 * 'P427 string trim' — `s.trim()` had no model: `return s.trim()` skipped a postcondition on its value, and
 * `s.trim()[0]` skipped its bounds (Phase 417). Java's contract is exact and needs no universals: the trim is the
 * middle of the one split `s = p + t + q` with p and q all characters `<= ' '` and t empty or starting and ending
 * above it (regular-expression membership, which Z3 decides), each application asserting its own split, and that
 * trimming it again changes nothing.
 *
 * A string witness is now rendered as a Groovy literal: Z3's `\u{1}` read back as the character, then escaped.
 */
class G469_p427_string_trim {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 427: `s.trim()` is modelled exactly (Java's leading and trailing characters `<= ' '` removed): its length, its containment in `s`, idempotence, literal folding and `s.trim()[0]`'s bounds prove or refute, and a string witness renders as a valid Groovy literal (`f(\"\\u0001\")`)."

    static final List<Map> CASES = [

        // Skipped before: no model for the return expression
        [group: "P427 string trim", name: "a trim is no longer, and inside its string",
         ok: true,
         src: tc('''class A {
                        @Requires({ s != null })
                        @Ensures({ result != null && result.length() <= s.length() && s.contains(result) })
                        static String f(String s) { return s.trim() }
                    }''')],

        [group: "P427 string trim", name: "trimming twice is trimming once",
         ok: true,
         src: tc('''class A {
                        @Requires({ s != null })
                        @Ensures({ result == s.trim() })
                        static String f(String s) { return s.trim().trim() }
                    }''')],

        // Each proves; the two in one claim time out (a prefix and a suffix in one disjunction), loudly
        [group: "P427 string trim", name: "a trim starts and ends with no space",
         ok: true,
         src: tc('''class A {
                        @Requires({ s != null })
                        @Ensures({ !result.startsWith(" ") })
                        static String f(String s) { return s.trim() }
                        @Requires({ s != null })
                        @Ensures({ !result.endsWith(" ") })
                        static String g(String s) { return s.trim() }
                    }''')],

        [group: "P427 string trim", name: "a literal's trim folds",
         ok: true,
         src: tc('''class A {
                        @Ensures({ result == "a b" })
                        static String f() { return "  a b \\t".trim() }
                    }''')],

        [group: "P427 string trim", name: "… and its contrary refutes",
         expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Ensures({ result == " a" })
                        static String f() { return " a ".trim() }
                    }''')],

        // Its witness was `f("\u{1}")`, Z3's spelling, not Groovy's
        [group: "P427 string trim", name: "a trim may be shorter, on a valid literal",
         expect: ["Cannot prove postcondition of f", 'fails on: f("'],
         refute: "u{",
         src: tc('''class A {
                        @Requires({ s != null })
                        @Ensures({ result.length() == s.length() })
                        static String f(String s) { return s.trim() }
                    }''')],

        // Java's contract, not "spaces": a control character is trimmed too
        [group: "P427 string trim", name: "no space isn't untrimmed",
         expect: ["Cannot prove postcondition of f", 'fails on: f("'],
         src: tc('''class A {
                        @Requires({ s != null && !s.contains(" ") })
                        @Ensures({ result == s })
                        static String f(String s) { return s.trim() }
                    }''')],

        // Skipped before (Phase 417)
        [group: "P427 string trim", name: "a trim's first character may not be there",
         expect: ["Possible IndexOutOfBoundsException", 'fails on: f("")'],
         src: tc('''class A {
                        @Requires({ s != null })
                        static String f(String s) { return s.trim()[0] }
                    }''')],

        [group: "P427 string trim", name: "… and is, when the trim isn't empty",
         ok: true,
         src: tc('''class A {
                        @Requires({ s != null && !s.trim().isEmpty() })
                        static String f(String s) { return s.trim()[0] }
                    }''')],

        [group: "P427 string trim", name: "a string witness is escaped",
         expect: ["Cannot prove postcondition of f", 'fails on: f("\\"")'],
         src: tc('''class A {
                        @Requires({ s != null })
                        @Ensures({ result != '"' })
                        static String f(String s) { return s }
                    }''')],
    ]
}
