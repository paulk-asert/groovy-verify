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
 * 'P509 literal list element nullity' — a literal list's element is null when the element it picks is:
 * {@code ['ab', s][i]} is {@code s}'s at {@code i == 1}, and a subscript past either end is null. Phase 508 left a call
 * on one ({@code ['ab', null][1].length()}) and its value unboxed ({@code int v = [1, null][1]}) with no obligation,
 * silently, and a local read from one ({@code String s = ['ab', null][0]}) of unknown nullity, a false alarm.
 */
class G550_p509_literal_list_element_nullity {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 509: a literal list's element is null when the element it picks is (`['ab', null][1].length()` throws, `[1, n][i] + 1` needs `n` non-null at `i == 1`)."

    static final List<Map> CASES = [

        // ---------- a call on a null element ----------
        [group: "P509 literal list element nullity", name: "a call on a literal's null element", expect: ['Possible NullPointerException', 'obligation: [\'ab\', null][1] != null'],
         src: tc('''class C {
                        static int f() { ['ab', null][1].length() }
                    }''')],
        [group: "P509 literal list element nullity", name: "… read by get", expect: ['Possible NullPointerException', 'obligation: [\'ab\', null].get(1) != null'],
         src: tc('''class C {
                        static int f() { ['ab', null].get(1).length() }
                    }''')],
        [group: "P509 literal list element nullity", name: "… a parameter's", expect: ['Possible NullPointerException', 'obligation: [\'ab\', s][1] != null', 'fails on: f(null)'],
         src: tc('''class C {
                        static int f(String s) { ['ab', s][1].length() }
                    }''')],
        [group: "P509 literal list element nullity", name: "… by an index", expect: ['Possible NullPointerException', 'fails on: f(1)'],
         src: tc('''class C {
                        @Requires({ i >= 0 && i < 2 })
                        static int f(int i) { ['ab', null][i].length() }
                    }''')],
        [group: "P509 literal list element nullity", name: "… past the end", expect: ['Possible NullPointerException', 'fails on: f(2)'],
         src: tc('''class C {
                        @Requires({ i >= 0 })
                        static int f(int i) { ['ab', 'cd'][i].length() }
                    }''')],
        [group: "P509 literal list element nullity", name: "… from the end", expect: ['Possible NullPointerException', 'obligation: [\'ab\', null][-1] != null'],
         src: tc('''class C {
                        static int f() { ['ab', null][-1].length() }
                    }''')],
        [group: "P509 literal list element nullity", name: "… an Integer's", expect: ['Possible NullPointerException', 'intValue()'],
         src: tc('''class C {
                        static int f() { [1, null][1].intValue() }
                    }''')],

        // ---------- a null element unboxed ----------
        [group: "P509 literal list element nullity", name: "a null element unboxed", expect: ['Possible GroovyCastException', '[1, null][1] is null for a null element'],
         src: tc('''class C {
                        static int f() { int v = [1, null][1]; v }
                    }''')],
        [group: "P509 literal list element nullity", name: "… in arithmetic", expect: ['Possible NullPointerException', '[1, n][1] is null for a null element', 'fails on: f(null)'],
         src: tc('''class C {
                        static int f(Integer n) { [1, n][1] + 1 }
                    }''')],

        // ---------- non-null ----------
        [group: "P509 literal list element nullity", name: "a call on a non-null element", ok: true,
         src: tc('''class C {
                        static int f() { ['ab', null][0].length() }
                    }''')],
        [group: "P509 literal list element nullity", name: "… a parameter's, required", ok: true,
         src: tc('''class C {
                        @Requires({ s != null })
                        static int f(String s) { ['ab', s][1].length() }
                    }''')],
        [group: "P509 literal list element nullity", name: "… by an index, within", ok: true,
         src: tc('''class C {
                        @Requires({ i == 0 || i == -1 })
                        static int f(int i) { ['ab', 'cd'][i].length() }
                    }''')],
        [group: "P509 literal list element nullity", name: "… from the end, non-null", ok: true,
         src: tc('''class C {
                        static int f() { ['ab', null][-2].length() }
                    }''')],
        [group: "P509 literal list element nullity", name: "… unboxed", ok: true,
         src: tc('''class C {
                        static int f() { int v = [1, null][0]; v }
                    }''')],
        [group: "P509 literal list element nullity", name: "… in arithmetic, required", ok: true,
         src: tc('''class C {
                        @Requires({ n != null })
                        static int f(Integer n) { [1, n][1] + 1 }
                    }''')],
        [group: "P509 literal list element nullity", name: "a local read from a non-null element", ok: true,
         src: tc('''class C {
                        static int f() { String s = ['ab', null][0]; s.length() }
                    }''')],

        // ---------- guards ----------
        [group: "P509 literal list element nullity", name: "a local read from a null element", expect: ['Possible NullPointerException', 'obligation: s != null'],
         src: tc('''class C {
                        static int f() { String s = ['ab', null][1]; s.length() }
                    }''')],
        [group: "P509 literal list element nullity", name: "a safe call on a null element", ok: true,
         src: tc('''class C {
                        static Integer f() { ['ab', null][1]?.length() }
                    }''')],
        [group: "P509 literal list element nullity", name: "a nested literal's element", ok: true,
         src: tc('''class C {
                        static int f() { [['a'], null][0].size() }
                    }''')],

        // ---------- loud ----------
        [group: "P509 literal list element nullity", name: "a spread literal's element", expect: ['Skipped element dereference', 'the nullity of \'[*xs, \'a\'][0]\' isn\'t modelled'],
         src: tc('''class C {
                        static int f(List<String> xs) { [*xs, 'a'][0].length() }
                    }''')],
        [group: "P509 literal list element nullity", name: "a literal's get by an index, as written", expect: ['Skipped list index', '\'[\'ab\', null].get(i)\' indexes the list \'[\'ab\', null]\'', 'fails on: f(1)'],
         src: tc('''class C {
                        @Requires({ i >= 0 && i < 2 })
                        static int f(int i) { ['ab', null].get(i).length() }
                    }''')],
    ]
}
