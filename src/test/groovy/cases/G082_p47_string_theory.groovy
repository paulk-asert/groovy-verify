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

/** 'P47 string theory' — 13 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G082_p47_string_theory {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Z3\'s native string theory: prefixof implies equal chars, distinct literals are theory-distinct, literal concat folds.'

    static final List<Map> CASES = [

        // ---------- Phase 47: Z3 string theory adoption ----------
        // The big-ticket structural fact: charAt across a prefix relationship. With the
        // uninterpreted approach (Phase 46a-e), startsWith was opaque to charAt — there was
        // no axiom relating them. With Z3's native seq theory, prefix-of structurally implies
        // that every position before the prefix length has equal characters in both strings.
        // This is the headline win of the theory adoption.
        [group: 'P47 string theory', name: 'prefixof structurally implies equal chars', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && t != null && s.startsWith(t) &&
                                    t.length() > 0 })
                        @Ensures({ result == 1 })
                        static int f(String s, String t) {
                            s.charAt(0) == t.charAt(0) ? 1 : 0
                        }
                    }''')],
        // Distinct literals: theory-distinct via seq theory, no pairwise cascade needed.
        [group: 'P47 string theory', name: 'distinct literals are theory-distinct', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "foo" != "bar" ? 1 : 0 }
                    }''')],
        // Concatenation: literal + literal folds, and length composes.
        [group: 'P47 string theory', name: 'literal concat folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "foobar" })
                        static String f() { "foo" + "bar" }
                    }''')],
        [group: 'P47 string theory', name: 'concat method form folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "foobar" })
                        static String f() { "foo".concat("bar") }
                    }''')],
        // Concat length composes structurally: |s + "x"| = |s| + 1.
        [group: 'P47 string theory', name: 'concat length composes', ok: true,
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ result == s.length() + 1 })
                        static int f(String s) { (s + "x").length() }
                    }''')],
        // Substring: literal substring folds.
        [group: 'P47 string theory', name: 'literal substring folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "ell" })
                        static String f() { "hello".substring(1, 4) }
                    }''')],
        // Substring single-arg form.
        [group: 'P47 string theory', name: 'literal substring single-arg folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "llo" })
                        static String f() { "hello".substring(2) }
                    }''')],
        // Substring bounds: out-of-bounds end refutes.
        [group: 'P47 string theory', name: 'substring out-of-bounds end refutes',
         expect: 'Possible IndexOutOfBoundsException',
         src: tc('''class C {
                        @Requires({ s != null })
                        static String f(String s) { s.substring(0, s.length() + 1) }
                    }''')],
        // Substring bounds: negative begin refutes.
        [group: 'P47 string theory', name: 'substring negative begin refutes',
         expect: 'Possible IndexOutOfBoundsException',
         src: tc('''class C {
                        @Requires({ s != null })
                        static String f(String s) { s.substring(-1, 2) }
                    }''')],
        // Substring length identity: |substring(s, a, b)| = b - a when in bounds.
        [group: 'P47 string theory', name: 'substring length identity', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.length() >= 5 })
                        @Ensures({ result == 3 })
                        static int f(String s) { s.substring(1, 4).length() }
                    }''')],
        // Cross-string: two strings sharing a prefix have equal chars there.
        [group: 'P47 string theory', name: 'prefix sharing gives charAt equality at i==1', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && t != null && s.startsWith("ab") && t.startsWith("ab") })
                        @Ensures({ result == 1 })
                        static int f(String s, String t) {
                            s.charAt(1) == t.charAt(1) ? 1 : 0
                        }
                    }''')],
        // Refute: structurally-equal-at-prefix doesn't imply equal at a position past the prefix.
        [group: 'P47 string theory', name: 'past-prefix charAt not structurally tied',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s != null && t != null && s.startsWith("ab") && t.startsWith("ab")
                                    && s.length() > 2 && t.length() > 2 })
                        @Ensures({ result == 1 })
                        static int f(String s, String t) {
                            s.charAt(2) == t.charAt(2) ? 1 : 0
                        }
                    }''')],
        // s contains t implies t.length() <= s.length() — a theory consequence.
        [group: 'P47 string theory', name: 'contains implies length bound', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && t != null && s.contains(t) })
                        @Ensures({ result >= t.length() })
                        static int f(String s, String t) { s.length() }
                    }''')],
    ]
}
