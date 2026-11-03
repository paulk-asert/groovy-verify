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
 * 'P520 a field handed on' — Phase 519's open items. A receiver's field handed to a constructor of this unit's
 * ({@code new Holder(b.xs)}), which may keep it and write it, compiled cleanly; and a local alias of one
 * ({@code List<Integer> ys = b.xs; ys.add(1)}) reported {@code ys} maybe null rather than the invariant it breaks.
 */
class G561_p520_field_handed_on {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 520: a receiver's field handed to a constructor of the unit's, or written through a local alias, says the invariant is unchecked."

    static String client(String inv, String fields, String methods, String extra = '') { """@Invariant({ ${inv} })
                    final class B { ${fields} }
                    ${extra}
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        ${methods}
                    }""" }

    static final String G = "P520 a field handed on"
    static String skipped(String call, String why) { "Skipped the class invariant check of B for 'b' after '${call}' (${why})" }
    static final String HOLDER = "final class Holder { List<Integer> ys; Holder(List<Integer> ys) { this.ys = ys; ys?.add(1) } }"

    static final List<Map> CASES = [
        [group: G, name: "handed to a constructor of the unit's", expect: [skipped("new Holder(b.xs)", "'b.xs' is handed to 'new Holder(b.xs)'")],
         src: tc(client('xs != null && xs.size() < 1', 'List<Integer> xs', '''@Requires({ b != null })
                        static Object f(B b) { new Holder(b.xs) }''', HOLDER))],
        [group: G, name: "a JDK constructor copies", ok: true,
         src: tc(client('xs != null && xs.size() < 1', 'List<Integer> xs', '''@Requires({ b != null })
                        static int f(B b) { List<Integer> c = new ArrayList<Integer>(b.xs); c.add(1); c.size() }'''))],
        [group: G, name: "written through a local alias", expect: [skipped("ys.add(1)", "'ys' is 'b.xs', which the verifier doesn't model as one")],
         src: tc(client('xs != null && xs.size() < 1', 'List<Integer> xs', '''@Requires({ b != null })
                        static void f(B b) { List<Integer> ys = b.xs; ys.add(1) }'''))],
        [group: G, name: "… a StringBuilder's", expect: [skipped("t.append('xxxx')", "'t' is 'b.sb', which the verifier doesn't model as one")],
         src: tc(client('sb != null && sb.length() < 3', 'StringBuilder sb', '''@Requires({ b != null })
                        static void f(B b) { StringBuilder t = b.sb; t.append('xxxx') }'''))],
        [group: G, name: "… handed on", expect: [skipped("Collections.sort(ys)", "'ys' is handed to 'Collections.sort(ys)'")],
         src: tc(client('xs != null && (xs.size() < 2 || xs[0] >= xs[1])', 'List<Integer> xs', '''@Requires({ b != null })
                        static void f(B b) { List<Integer> ys = b.xs; Collections.sort(ys) }'''))],
        [group: G, name: "a local alias read", ok: true,
         src: tc(client('sb != null', 'StringBuilder sb', '''@Requires({ b != null })
                        static String f(B b) { StringBuilder t = b.sb; t.toString() }'''))],
        [group: G, name: "… the field stored first, maybe null", expect: ['Possible NullPointerException'],
         src: tc(client('name != null', 'String name', '''@Requires({ b != null })
                        static int f(B b, String s) { b.name = s; String t = b.name; t.length() }'''))],
    ]
}
