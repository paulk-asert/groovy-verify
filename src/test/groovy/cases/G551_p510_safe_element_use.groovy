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
 * 'P510 safe call on an element, used' — a safe call on an element ({@code xs[0]?.length()}) is null when the element
 * is, and that null throws where it's used: in arithmetic ({@code xs[0]?.length() + 1}), as a primitive's value
 * ({@code int f() { xs[0]?.length() }}), as an argument. Phase 422 kept the obligation there for a name's safe call
 * ({@code s?.length() + 1}) only: an element's was taken as guarded by its own non-null, and compiled cleanly.
 */
class G551_p510_safe_element_use {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 510: a safe call on an element whose null is used where it throws (`xs[0]?.length() + 1`) owes the element non-null, as a name's does (Phase 422)."

    static String client(String method) { """final class B { List<String> ns; List<Integer> xs }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        ${method}
                    }""" }

    static final List<Map> CASES = [

        // ---------- used where a null throws ----------
        [group: "P510 safe call on an element, used", name: "a parameter's element, in arithmetic", expect: ['Possible NullPointerException', 'xs[0]?.length() is null when xs[0] is', 'obligation: xs[0] != null', 'fails on: f([null])'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 })
                        static int f(List<String> xs) { xs[0]?.length() + 1 }
                    }''')],
        [group: "P510 safe call on an element, used", name: "… read by get", expect: ['Possible NullPointerException', 'xs.get(0)?.length() is null when xs.get(0) is', 'fails on: f([null])'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 })
                        static int f(List<String> xs) { xs.get(0)?.length() + 1 }
                    }''')],
        [group: "P510 safe call on an element, used", name: "… as an int's value", expect: ['Possible NullPointerException', 'xs[0]?.length() is null when xs[0] is', 'fails on: f([null])'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 })
                        static int f(List<String> xs) { xs[0]?.length() }
                    }''')],
        [group: "P510 safe call on an element, used", name: "… as an argument", expect: ['Possible NullPointerException', 'xs[0]?.length() is null when xs[0] is'],
         src: tc('''class C {
                        static int g(int n) { n }
                        @Requires({ xs != null && xs.size() == 1 })
                        static int f(List<String> xs) { g(xs[0]?.length()) }
                    }''')],
        [group: "P510 safe call on an element, used", name: "an array's element", expect: ['Possible NullPointerException', 'a[0]?.length() is null when a[0] is', 'fails on: f(new String[1])'],
         src: tc('''class C {
                        @Requires({ a != null && a.length == 1 })
                        static int f(String[] a) { a[0]?.length() + 1 }
                    }''')],
        [group: "P510 safe call on an element, used", name: "a receiver's element", expect: ['Possible NullPointerException', 'b.xs[0]?.intValue() is null when b.xs[0] is', 'obligation: b.xs[0] != null'],
         src: tc(client('''@Requires({ b != null && b.xs != null && b.xs.size() == 1 })
                        static int f(B b) { b.xs[0]?.intValue() + 1 }'''))],
        [group: "P510 safe call on an element, used", name: "a map's value", expect: ['Possible NullPointerException', "m['k']?.length() is null when m['k'] is"],
         src: tc('''class C {
                        @Requires({ m != null })
                        static int f(Map<String, String> m) { m['k']?.length() + 1 }
                    }''')],
        [group: "P510 safe call on an element, used", name: "a literal's element", expect: ['Possible NullPointerException', "['ab', null][1]?.length() is null when ['ab', null][1] is"],
         src: tc('''class C {
                        static int f() { ['ab', null][1]?.length() + 1 }
                    }''')],
        [group: "P510 safe call on an element, used", name: "an unmodelled list's element, loud", expect: ['Skipped element dereference', "the nullity of 's.ns[0]' isn't modelled"],
         src: tc(client('''@Requires({ s != null && s.ns != null && s.ns.size() == 1 })
                        static int f(B s) { s.ns[0]?.length() + 1 }'''))],

        // ---------- non-null where used ----------
        [group: "P510 safe call on an element, used", name: "a parameter's element, stated non-null", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 && xs[0] != null })
                        static int f(List<String> xs) { xs[0]?.length() + 1 }
                    }''')],
        [group: "P510 safe call on an element, used", name: "… a receiver's", ok: true,
         src: tc(client('''@Requires({ b != null && b.xs != null && b.xs.size() == 1 && b.xs[0] != null })
                        static int f(B b) { b.xs[0]?.intValue() + 1 }'''))],
        [group: "P510 safe call on an element, used", name: "… a literal's", ok: true,
         src: tc('''class C {
                        static int f() { ['ab', null][0]?.length() + 1 }
                    }''')],

        // ---------- harmless where used ----------
        [group: "P510 safe call on an element, used", name: "a safe call's null, compared", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 })
                        static boolean f(List<String> xs) { xs[0]?.length() == 2 }
                    }''')],
        [group: "P510 safe call on an element, used", name: "… under an elvis", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 })
                        static int f(List<String> xs) { xs[0]?.length() ?: 0 }
                    }''')],
        [group: "P510 safe call on an element, used", name: "… as an Integer's value", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 })
                        static Integer f(List<String> xs) { xs[0]?.length() }
                    }''')],
        [group: "P510 safe call on an element, used", name: "… a literal's, as a statement", ok: true,
         src: tc('''class C {
                        static void f() { ['ab', null][1]?.length() }
                    }''')],
        [group: "P510 safe call on an element, used", name: "… an unmodelled list's, as an Integer's value", ok: true,
         src: tc(client('''@Requires({ s != null && s.ns != null && s.ns.size() == 1 })
                        static Integer f(B s) { s.ns[0]?.length() }'''))],

        // ---------- guards ----------
        [group: "P510 safe call on an element, used", name: "a name's safe call, used", expect: ['Possible NullPointerException', 's?.length() is null when s is', 'fails on: f(null)'],
         src: tc('''class C {
                        static int f(String s) { s?.length() + 1 }
                    }''')],
        [group: "P510 safe call on an element, used", name: "a safe call's argument, guarded by its receiver", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 && xs[0] != null })
                        static int f(List<String> xs) { xs[0]?.substring(0).length() }
                    }''')],
    ]
}
