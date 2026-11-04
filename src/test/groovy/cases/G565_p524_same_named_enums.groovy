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
 * 'P524 same-named enums' — two enums of one simple name in a module ({@code C.L} and {@code D.L}) were one Z3
 * sort, named by the simple name, and the {@code values().length} fold was keyed by it too: the second enum's count
 * overwrote the first's, and a constant each enum spells ({@code A}) was one literal in both.
 */
class G565_p524_same_named_enums {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 524: two enums sharing a simple name are two sorts: each its own constant count, its own constants, its own domain closure."

    static final String G = "P524 same-named enums"
    /** the class under test first (tc annotates the first class); D's L has a third constant and shares A */
    static String src(String methods) { """class C {
                        enum L { A, B }
                        ${methods}
                    }
                    class D { enum L { A, Y, Z } }""" }

    static final List<Map> CASES = [
        [group: G, name: "its own count, the short spelling", ok: true,
         src: tc(src('''@Ensures({ result == L.values().length })
                        static int f() { 2 }'''))],
        [group: G, name: "… refuted with the other's count", expect: ['Cannot prove postcondition'],
         src: tc(src('''@Ensures({ result == L.values().length })
                        static int f() { 3 }'''))],
        [group: G, name: "the other's count, through its class", ok: true,
         src: tc(src('''@Ensures({ result == D.L.values().length })
                        static int f() { 3 }'''))],
        [group: G, name: "… refuted with this one's count", expect: ['Cannot prove postcondition'],
         src: tc(src('''@Ensures({ result == D.L.values().length })
                        static int f() { 2 }'''))],
        [group: G, name: "every constant, non-null", ok: true,
         src: tc(src('''@Requires({ a != null })
                        @Ensures({ a == L.A || a == L.B })
                        static void f(L a) { }'''))],
        [group: G, name: "the other's every constant, non-null", ok: true,
         src: tc(src('''@Requires({ a != null })
                        @Ensures({ a == D.L.A || a == D.L.Y || a == D.L.Z })
                        static void f(D.L a) { }'''))],
        [group: G, name: "… one short, refuted", expect: ['Cannot prove postcondition', 'fails on: f(D.L.Z)'],
         src: tc(src('''@Requires({ a != null })
                        @Ensures({ a == D.L.A || a == D.L.Y })
                        static void f(D.L a) { }'''))],
        [group: G, name: "two enums' same-named constants are not equal", expect: ['Cannot prove postcondition'],
         src: tc(src('''@Requires({ a == L.A && b == D.L.A })
                        @Ensures({ result })
                        static boolean f(L a, D.L b) { a == b }'''))],
        [group: G, name: "… and never equal", ok: true,
         src: tc(src('''@Requires({ a != null && b != null })
                        @Ensures({ !result })
                        static boolean f(L a, D.L b) { a == b }'''))],
        [group: G, name: "a map keyed by each", ok: true,
         src: tc(src('''@Requires({ m != null && n != null && m[L.A] == 1 && n[D.L.A] == 2 })
                        @Ensures({ result == 3 })
                        static int f(Map<L, Integer> m, Map<D.L, Integer> n) { m[L.A] + n[D.L.A] }'''))],
        [group: G, name: "the other's constant in a body, not this one's", expect: ['Cannot prove postcondition'],
         src: tc(src('''@Requires({ a == L.A })
                        @Ensures({ result })
                        static boolean f(L a) { a == D.L.A }'''))],
        [group: G, name: "the other's constant in a contract, never this one's", ok: true,
         src: tc(src('''@Requires({ a != null })
                        @Ensures({ a != D.L.A })
                        static void f(L a) { }'''))],
    ]
}
