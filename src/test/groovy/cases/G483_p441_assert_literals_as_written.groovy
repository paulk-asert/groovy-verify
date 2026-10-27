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
 * 'P441 assert literals as written' — Phase 428 kept a contract's string literals as written (a re-parsed contract
 * carries its text), but an assertion's condition is the body's own AST, with no captured text: its literals came out
 * re-quoted as double-quoted Groovy literals. Its columns are the file's own, so the literal is now cut from the line.
 */
class G483_p441_assert_literals_as_written {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 441: an assertion's string literals read as written in the diagnostic (`'x'`, `\"a\\tb\"`, `/a+/`), where they were re-quoted as double-quoted Groovy literals."

    static final List<Map> CASES = [

        // It read `(s == "x")`
        [group: "P441 assert literals as written", name: "a single-quoted literal stays single-quoted",
         expect: "Assertion may not hold: ((s == 'x') || (s == \"y\"))",
         src: tc('''class A {
                        static void f(String s) { assert s == 'x' || s == "y" }
                    }''')],

        // It read `"a\tb"` too, but re-escaped from the value: an escape is kept as typed, `\u0041` included
        [group: "P441 assert literals as written", name: "an escape is kept as typed",
         expect: 'Assertion may not hold: ((s == "a\\tb") || (s == \'\\u0041\'))',
         src: tc('''class A {
                        static void f(String s) { assert s == "a\\tb" || s == '\\u0041' }
                    }''')],

        // It read `(s ==~ "a+")`
        [group: "P441 assert literals as written", name: "a slashy literal stays slashy",
         expect: 'Assertion may not hold: (s ==~ /a+/)',
         src: tc('''class A {
                        static void f(String s) { assert s ==~ /a+/ }
                    }''')],

        // A literal spanning lines has no one line to cut from: it keeps Phase 428's double-quoted form
        [group: "P441 assert literals as written", name: "a multi-line literal stays double-quoted",
         expect: 'Assertion may not hold: (s == "a\\nb")',
         src: tc("""class A {
                        static void f(String s) { assert s == '''a
b''' }
                    }""")],
    ]
}
