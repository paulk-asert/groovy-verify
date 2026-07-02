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

/** 'P47h gstring' — 11 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G090_p47h_gstring {

    static final List<Map> CASES = [

        // ---------- Phase 47h: GString interpolation ----------
        // Single String interpolation: "hello $name" with literal name folds to the
        // concrete concatenated string.
        [group: 'P47h gstring', name: 'GString with String literal interpolation folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "hello world" })
                        static String f() { String name = "world"; "hello $name" }
                    }''')],
        // Single int interpolation: "x = $x" routes the int through intToString.
        [group: 'P47h gstring', name: 'GString with int literal interpolation folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "x = 5" })
                        static String f() { int x = 5; "x = $x" }
                    }''')],
        // Mixed: multiple interpolations, mixed types.
        [group: 'P47h gstring', name: 'GString with multiple interpolations', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "a=1, b=hi" })
                        static String f() {
                            int a = 1
                            String b = "hi"
                            "a=$a, b=$b"
                        }
                    }''')],
        // Length of a GString — sums static parts with int.toString length.
        [group: 'P47h gstring', name: 'GString length composes', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == 4 + Integer.toString(n).length() })
                        static int f(int n) { "n = $n".length() }
                    }''')],
        // Symbolic String parameter: "hello $name" length is "hello ".length + name.length.
        [group: 'P47h gstring', name: 'GString length with String param', ok: true,
         src: tc('''class C {
                        @Requires({ name != null })
                        @Ensures({ result == 6 + name.length() })
                        static int f(String name) { "hello $name".length() }
                    }''')],
        // GString as comparison RHS: matches a String literal at runtime.
        [group: 'P47h gstring', name: 'GString equals literal String', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() {
                            String name = "Alice"
                            "hi $name" == "hi Alice" ? 1 : 0
                        }
                    }''')],
        // Refute: wrong interpolated value.
        [group: 'P47h gstring', name: 'GString refutes wrong interpolation',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == "hello Bob" })
                        static String f() { String name = "Alice"; "hello $name" }
                    }''')],
        // GString with ${...} block-form interpolation (computed expression).
        [group: 'P47h gstring', name: 'GString with block-form expression', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "sum=3" })
                        static String f() { int a = 1; int b = 2; "sum=${a + b}" }
                    }''')],
        // GString chained with .startsWith — the result is a String-typed receiver.
        [group: 'P47h gstring', name: 'GString routes through string-receiver dispatch', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() {
                            String name = "Alice"
                            "hi $name".startsWith("hi") ? 1 : 0
                        }
                    }''')],
        // Showcase: idLength under a prefix-constrained input. Verifies via the seq theory's
        // structural fact (startsWith → length(prefix) <= length(s)) composed with substring's
        // length identity.
        [group: 'P47h gstring', name: 'showcase: idLength via startsWith + substring', ok: true,
         src: tc('''class C {
                        @Requires({ s?.startsWith("user:") })
                        @Ensures({ result == s.length() - 5 })
                        static int idLength(String s) { s.substring(5).length() }
                    }''')],
        // Showcase 2: GString + regex + structural concat facts. Verifies via four
        // theory consequences in one method: regex membership preserved through the
        // precondition, GString folds to chained str.++, prefix-of-concat with the literal
        // first operand, suffix-of-concat with the second operand.
        [group: 'P47h gstring', name: 'showcase: greet via gstring + ==~ regex + concat facts', ok: true,
         src: tc('''class C {
                        @Requires({ name ==~ /[a-zA-Z]+/ })
                        @Ensures({ result.startsWith("Hi, ") && result.endsWith(name) })
                        static String greet(String name) { "Hi, $name" }
                    }''')],
    ]
}
