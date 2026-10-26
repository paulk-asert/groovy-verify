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
 * 'P428 string literals as written' — a contract's text in a diagnostic is Groovy's own `getText()`, and a string
 * constant's is its bare value: `@Ensures({ result == " a" })` read `ensured: (result ==  a)`, `endsWith(' ')`
 * `endsWith( )`, and the Kerridge gallery quoted `ensured: (result == Hello World)`.
 *
 * A string value is quoted now — as written where the expression is a re-parsed contract (its columns are the captured
 * text's), else as a double-quoted Groovy literal. A property's, a method's or a map key's name is left as it was.
 */
class G470_p428_string_literals_as_written {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 428: a string literal in a diagnostic's contract text keeps its quotes, as written (`ensured: (result == 'Hello World')`, `endsWith(' ')`), where it read as its bare value."

    static final List<Map> CASES = [

        // It read `ensured: ((result ==  a) && !(result.endsWith( )))`
        [group: "P428 string literals as written", name: "an @Ensures keeps each literal's quotes",
         expect: ["Cannot prove postcondition of f", "ensured: ((result == \" a\") && !(result.endsWith(' ')))"],
         src: tc('''class A {
                        @Ensures({ result == " a" && !result.endsWith(' ') })
                        static String f() { return " a ".trim() }
                    }''')],

        [group: "P428 string literals as written", name: "… and a @Requires",
         expect: ["Cannot prove precondition of g", "required: ((s == \"x\") || (s == 'z'))"],
         src: tc('''class A {
                        @Requires({ s == "x" || s == 'z' })
                        static int g(String s) { 1 }
                        static int f() { g("y") }
                    }''')],

        [group: "P428 string literals as written", name: "a property's and a method's name stay bare",
         expect: "ensured: ((result == a.length) && (result != 'q'.length()))",
         src: tc('''class A {
                        @Requires({ a != null })
                        @Ensures({ result == a.length && result != 'q'.length() })
                        static int f(int[] a) { a.length }
                    }''')],

        // An assert's condition is the body's own, not a re-parsed contract: a Groovy literal, escaped
        [group: "P428 string literals as written", name: "an assertion's literal is quoted and escaped",
         expect: 'Assertion may not hold: (s == "a\\$b\\"c")',
         src: tc('''class A {
                        static void f(String s) { assert s == 'a$b"c' }
                    }''')],
    ]
}
