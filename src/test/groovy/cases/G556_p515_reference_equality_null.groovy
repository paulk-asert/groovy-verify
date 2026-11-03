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
 * 'P515 reference equality null' — two reference parameters compared ({@code s == t} for two {@code String}s,
 * {@code n == m} for two {@code Integer}s) compared their values alone, and a null's value is free: two nulls could
 * differ, and a null equal a non-null. Now a null equals only a null, by the two parameters' null flags. A literal's
 * side is Phase 445's, an element's Phase 492's. Two nulls are one value too (a map keyed by either reads the same
 * entry). Only a {@code String} or a boxed primitive: an enum's or an {@code Object}'s compare by value, as before.
 */
class G556_p515_reference_equality_null {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 515: `s == t` and `s != t` between two reference parameters compare a null as Groovy does, equal only to a null."

    static final List<Map> CASES = [
        [group: "P515 reference equality null", name: "two null Strings, equal", ok: true,
         src: tc('''class C {
                        @Requires({ s == null && t == null })
                        @Ensures({ s == t })
                        static void f(String s, String t) { }
                    }''')],
        [group: "P515 reference equality null", name: "… in a body", ok: true,
         src: tc('''class C {
                        @Requires({ s == null && t == null })
                        @Ensures({ result })
                        static boolean f(String s, String t) { s == t }
                    }''')],
        [group: "P515 reference equality null", name: "a null String and another, not equal", ok: true,
         src: tc('''class C {
                        @Requires({ s == null && t != null })
                        @Ensures({ !result })
                        static boolean f(String s, String t) { s == t }
                    }''')],
        [group: "P515 reference equality null", name: "… by !=", ok: true,
         src: tc('''class C {
                        @Requires({ s == null && t != null })
                        @Ensures({ result })
                        static boolean f(String s, String t) { s != t }
                    }''')],
        [group: "P515 reference equality null", name: "… by != on non-nulls", ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s == t })
                        @Ensures({ !result })
                        static boolean f(String s, String t) { s != t }
                    }''')],
        [group: "P515 reference equality null", name: "two null Integers, equal", ok: true,
         src: tc('''class C {
                        @Requires({ n == null && m == null })
                        @Ensures({ result })
                        static boolean f(Integer n, Integer m) { n == m }
                    }''')],
        [group: "P515 reference equality null", name: "equal to a non-null, non-null", ok: true,
         src: tc('''class C {
                        @Requires({ s == t && s != null })
                        static int f(String s, String t) { t.length() }
                    }''')],
        [group: "P515 reference equality null", name: "a literal list's against a null element", ok: true,
         src: tc('''class C {
                        @Ensures({ result == (s == 'ab' || s == t) })
                        static boolean f(String s, String t) { s in ['ab', t] }
                    }''')],
        [group: "P515 reference equality null", name: "a reassigned parameter, by its new value", ok: true,
         src: tc('''class C {
                        @Requires({ t == null })
                        @Ensures({ !result })
                        static boolean f(String s, String t) { s = 'x'; s == t }
                    }''')],
        [group: "P515 reference equality null", name: "equal, maybe both null", expect: ['Possible NullPointerException', 'fails on: f(null, null)'],
         src: tc('''class C {
                        @Requires({ s == t })
                        static int f(String s, String t) { t.length() }
                    }''')],
        [group: "P515 reference equality null", name: "two Strings, not always equal", expect: ['Cannot prove postcondition', 'fails on: f('],
         src: tc('''class C {
                        @Ensures({ result })
                        static boolean f(String s, String t) { s == t }
                    }''')],
        [group: "P515 reference equality null", name: "a null Integer and a number, not equal", expect: ['Cannot prove postcondition', 'fails on: f(null, '],
         src: tc('''class C {
                        @Requires({ n == null || n == m })
                        @Ensures({ result })
                        static boolean f(Integer n, Integer m) { n == m }
                    }''')],
        [group: "P515 reference equality null", name: "a computed result, by its value", ok: true,
         src: tc('''class C {
                        @Requires({ s == 'abc' && t == 'cba' })
                        @Ensures({ t == result })
                        static String f(String s, String t) { s.reverse() }
                    }''')],
        [group: "P515 reference equality null", name: "ints, as before", ok: true,
         src: tc('''class C {
                        @Requires({ a == b })
                        @Ensures({ result == 0 })
                        static int f(int a, int b) { a - b }
                    }''')],
        [group: "P515 reference equality null", name: "two enums, by value beside a constant", ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        @Ensures({ (leq(a, b) && leq(b, a)) ==> (a == b) })
                        static void f(L a, L b) { }
                    }''')],
        [group: "P515 reference equality null", name: "two Objects, by value as arguments", ok: true,
         src: tc('''class C {
                        @Requires({ a == b })
                        @Ensures({ g.apply(a) == g.apply(b) })
                        static void f(java.util.function.Function g, Object a, Object b) { }
                    }''')],
        [group: "P515 reference equality null", name: "two Strings, as a map's keys", ok: true,
         src: tc('''class C {
                        @Requires({ m != null && s == t })
                        @Ensures({ m[s] == m[t] })
                        static void f(Map<String, Integer> m, String s, String t) { }
                    }''')],
    ]
}
