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
 * 'P417 string expression subscripts' — Phase 416 bounded a string variable's subscript by its length; a string that
 * isn't a variable (`s.substring(2)[0]`, `'abc'[3]`, `(s + 'x')[1]`, a list's element, `this.s[0]`) had no
 * obligation, and said nothing. Each is bounded by its own length now where the string translates, and skips loudly,
 * naming it, where it doesn't (`s.trim()`, an open class's property).
 *
 * Found on the way: in the String sort the encoder read any `x.prop` on a variable as an enum constant, so `t.name`
 * was the literal "name" — four characters long, whatever `t` held. No contract reached it (they reject an open
 * class's property first); this phase's bounds would have, proving `t.name[0]` from nothing.
 */
class G459_p417_string_expression_subscripts {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 417: a subscript on a string that isn't a variable (a call's result, a literal, a concatenation, a list's element, `this.s`) is bounded by its own length, and skips loudly where the string is outside the model (soundness fix)."

    static final List<Map> CASES = [

        // Unchecked before, silently
        [group: "P417 string expression subscripts", name: "a substring's subscript proves within it",
         ok: true,
         src: tc('''class A {
                        @Requires({ s != null && s.size() > 2 })
                        static String f(String s) { s.substring(2)[0] }
                    }''')],

        [group: "P417 string expression subscripts", name: "… and refutes when it may be empty",
         expect: ["Possible IndexOutOfBoundsException", "obligation: 0 <= 0 && 0 < s.substring(2).length()", 'fails on: f("'],
         src: tc('''class A {
                        @Requires({ s != null && s.size() > 1 })
                        static String f(String s) { s.substring(2)[0] }
                    }''')],

        [group: "P417 string expression subscripts", name: "a literal's subscript is bounded by its length",
         expect: ["obligation: 0 <= 3 && 3 < 'abc'.length()"],
         refute: "1 < 'abc'",
         src: tc('''class A {
                        static String f() { 'abc'[1] + 'abc'[3] }
                    }''')],

        [group: "P417 string expression subscripts", name: "a concatenation's too",
         expect: ["obligation: 0 <= 1 && 1 < (s + x).length()", 'fails on: f("")'],
         refute: "0 < (s + x)",
         src: tc('''class A {
                        @Requires({ s != null })
                        static String f(String s) { (s + 'x')[0] + (s + 'x')[1] }
                    }''')],

        [group: "P417 string expression subscripts", name: "a list's string element's",
         expect: ["Possible IndexOutOfBoundsException", "obligation: 0 <= 0 && 0 < xs[0].length()"],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] != null })
                        static String f(List<String> xs) { xs[0][0] }
                    }''')],

        // Bounded by an oracle no contract reads before, so it refuted however guarded
        [group: "P417 string expression subscripts", name: "`this.s[0]` proves under its precondition",
         ok: true,
         src: tc('''final class A {
                        String s
                        @Requires({ s != null && s.size() > 0 })
                        String f() { this.s[0] }
                    }''')],

        [group: "P417 string expression subscripts", name: "… and refutes without it",
         expect: ["obligation: 0 <= 0 && 0 < s.length()", "fails on: f()"],
         src: tc('''final class A {
                        String s
                        @Requires({ s != null })
                        String f() { this.s[0] }
                    }''')],

        // ── outside the model: loud ──

        // `s.trim()` was this case's call until Phase 427 modelled it
        [group: "P417 string expression subscripts", name: "a call the model doesn't know skips, naming it",
         expect: "Skipped string index safety check (string 's.strip()' is outside fragment)",
         src: tc('''class A {
                        @Requires({ s != null })
                        static String f(String s) { s.strip()[0] }
                    }''')],

        // Proved from the literal "name" with this phase's bounds alone
        [group: "P417 string expression subscripts", name: "an open class's property skips, not read as its name",
         expect: "Skipped string index safety check (string 't.name' is outside fragment)",
         src: tc('''class A {
                        @Requires({ t != null && t.name != null })
                        static String f(T t) { t.name[0] }
                    }
                    class T { String name }''')],
    ]
}
