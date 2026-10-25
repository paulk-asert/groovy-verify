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
 * 'P416 string subscript bounds' — a string's subscript was bounded by a size oracle no contract or guard reads (a
 * string's `s.length()`/`s.size()` is its own length), so every `s[i]` refuted, guarded or not, and "failed on" a
 * string that has the character (`f("A")` for `s[0]`). It's bounded by the string's length now: in bounds in
 * `[-length, length)`, a negative index counting from the end (measured: `"abc"[-1]` is "c", `"abc"[-4]` and `""[0]`
 * throw).
 *
 * Found on the way: a local bound to a string literal (`String s = 'abc'`) may be null, the model said, so a call on it
 * refuted on `f()`; a non-null literal is never null now, as a GString and a `new` are.
 */
class G458_p416_string_subscript_bounds {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 416: a string's subscript is bounded by the string's own length (what `s.length()`/`s.size()` read), a negative index counting from the end, and a local bound to a string literal is never null (false-positive fixes)."

    static final List<Map> CASES = [

        // A false positive before: "fails on: f("A")"
        [group: "P416 string subscript bounds", name: "a size() precondition proves s[0]",
         ok: true,
         src: tc('''class A {
                        @Requires({ s != null && s.size() > 0 })
                        static String f(String s) { s[0] }
                    }''')],

        [group: "P416 string subscript bounds", name: "… as does a length() one",
         ok: true,
         src: tc('''class A {
                        @Requires({ s != null && s.length() > 1 })
                        static String f(String s) { s[1] }
                    }''')],

        [group: "P416 string subscript bounds", name: "an index past the precondition fails on a short string",
         expect: ["Possible IndexOutOfBoundsException", "obligation: 0 <= 1 && 1 < s.size()", 'fails on: f("A")'],
         src: tc('''class A {
                        @Requires({ s != null && s.size() > 0 })
                        static String f(String s) { s[1] }
                    }''')],

        [group: "P416 string subscript bounds", name: "an unguarded subscript fails on the empty string",
         expect: ["obligation: 0 <= 0 && 0 < s.length()", 'fails on: f("")'],
         src: tc('''class A {
                        @Requires({ s != null })
                        static String f(String s) { s[0] }
                    }''')],

        [group: "P416 string subscript bounds", name: "s[-1] counts from the end",
         ok: true,
         src: tc('''class A {
                        @Requires({ s != null && !s.isEmpty() })
                        static String f(String s) { s[-1] }
                    }''')],

        [group: "P416 string subscript bounds", name: "… and fails on the empty string",
         expect: ["obligation: 0 <= s.length() - 1 && s.length() - 1 < s.length()", 'fails on: f("")'],
         src: tc('''class A {
                        @Requires({ s != null })
                        static String f(String s) { s[-1] }
                    }''')],

        [group: "P416 string subscript bounds", name: "a guard in the body proves it",
         ok: true,
         src: tc('''class A {
                        static String f(String s, int i) {
                            if (s != null && i >= 0 && i < s.length()) return s[i]
                            return ''
                        }
                    }''')],

        [group: "P416 string subscript bounds", name: "… and one off by one fails",
         expect: ["obligation: 0 <= i && i < s.length()", 'fails on: f("", 0)'],
         src: tc('''class A {
                        static String f(String s, int i) {
                            if (s != null && i >= 0 && i <= s.length()) return s[i]
                            return ''
                        }
                    }''')],

        // A false positive before, twice: the literal's length, and its nullity
        [group: "P416 string subscript bounds", name: "a literal's subscript proves",
         ok: true,
         src: tc('''class A {
                        static String f() {
                            String s = 'abc'
                            return s[2]
                        }
                    }''')],

        [group: "P416 string subscript bounds", name: "… past its end refutes",
         expect: ["obligation: 0 <= 3 && 3 < s.length()", "fails on: f()"],
         src: tc('''class A {
                        static String f() {
                            String s = 'abc'
                            return s[3]
                        }
                    }''')],

        [group: "P416 string subscript bounds", name: "… and before its start",
         expect: ["obligation: 0 <= s.length() - 4 && s.length() - 4 < s.length()", "fails on: f()"],
         src: tc('''class A {
                        static String f() {
                            String s = 'abc'
                            return s[-4]
                        }
                    }''')],

        [group: "P416 string subscript bounds", name: "a call on a literal local has no null obligation",
         ok: true,
         src: tc('''class A {
                        static int f() {
                            String s = 'abc'
                            return s.length()
                        }
                    }''')],

        // "n=$n" may be only three characters long ("n=2")
        [group: "P416 string subscript bounds", name: "a GString's length is its values'",
         expect: ["Possible IndexOutOfBoundsException", "obligation: 0 <= 5 && 5 < s.length()"],
         src: tc('''class A {
                        static String f(int n) {
                            String s = "n=$n"
                            return s[5]
                        }
                    }''')],

        [group: "P416 string subscript bounds", name: "a string field's subscript proves under its precondition",
         ok: true,
         src: tc('''final class A {
                        String s
                        @Requires({ s != null && s.size() > 0 })
                        String f() { s[0] }
                    }''')],

        [group: "P416 string subscript bounds", name: "… and fails without it",
         expect: ["obligation: 0 <= 0 && 0 < s.length()"],
         src: tc('''final class A {
                        String s
                        @Requires({ s != null })
                        String f() { s[0] }
                    }''')],

        [group: "P416 string subscript bounds", name: "a substring's length is the rest",
         ok: true,
         src: tc('''class A {
                        @Requires({ s != null && s.size() > 2 })
                        static String f(String s) {
                            s = s.substring(2)
                            return s[0]
                        }
                    }''')],

        [group: "P416 string subscript bounds", name: "… which may be empty",
         expect: ["Possible IndexOutOfBoundsException"],
         src: tc('''class A {
                        @Requires({ s != null && s.size() > 1 })
                        static String f(String s) {
                            s = s.substring(2)
                            return s[0]
                        }
                    }''')],
    ]
}
