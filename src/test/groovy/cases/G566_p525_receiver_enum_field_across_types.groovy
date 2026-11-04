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
 * 'P525 receiver enum field across types' — a receiver's enum field compared with a constant or a field of another
 * enum type of the same simple name ({@code b.level == D.L.A}, a {@code C.L} field) met the two sorts in one
 * comparison: an internal sort error, a loud skip. Now it compares as Groovy's {@code ==} does: never equal, unless
 * both sides are null.
 */
class G566_p525_receiver_enum_field_across_types {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 525: a receiver's enum field compared with another enum type's constant or field (two enums of one simple name) is never equal, unless both are null."

    static final String G = "P525 receiver enum field across types"
    /** the class under test first; B's field is C.L, E's is D.L */
    static String src(String methods) { """class C {
                        enum L { A, B }
                        ${methods}
                    }
                    class D { enum L { A, Y, Z } }
                    final class B { C.L level }
                    final class E { D.L level }""" }

    static final List<Map> CASES = [
        [group: G, name: "the other's constant, in a body", ok: true,
         src: tc(src('''@Requires({ b != null && b.level != null })
                        @Ensures({ !result })
                        static boolean f(B b) { b.level == D.L.A }'''))],
        [group: G, name: "… in a contract", ok: true,
         src: tc(src('''@Requires({ b != null && b.level != null })
                        @Ensures({ b.level != D.L.A })
                        static void f(B b) { }'''))],
        [group: G, name: "… a maybe-null field: a null is no constant either", ok: true,
         src: tc(src('''@Requires({ b != null })
                        @Ensures({ b.level != D.L.A })
                        static void f(B b) { }'''))],
        [group: G, name: "its own constant still compares", expect: ['Cannot prove postcondition', 'fails on: f(new B('],
         src: tc(src('''@Requires({ b != null && b.level != null })
                        @Ensures({ !result })
                        static boolean f(B b) { b.level == L.A }'''))],
        [group: G, name: "two receivers' fields of two types, never equal", ok: true,
         src: tc(src('''@Requires({ b != null && e != null && b.level != null })
                        @Ensures({ !result })
                        static boolean f(B b, E e) { b.level == e.level }'''))],
        [group: G, name: "… equal when both null", ok: true,
         src: tc(src('''@Requires({ b != null && e != null && b.level == null && e.level == null })
                        @Ensures({ result })
                        static boolean f(B b, E e) { b.level == e.level }'''))],
        [group: G, name: "… maybe both null, refuted", expect: ['Cannot prove postcondition'],
         src: tc(src('''@Requires({ b != null && e != null })
                        @Ensures({ !result })
                        static boolean f(B b, E e) { b.level == e.level }'''))],
        [group: G, name: "a field and the other type's parameter", ok: true,
         src: tc(src('''@Requires({ b != null && a != null })
                        @Ensures({ result })
                        static boolean f(B b, D.L a) { b.level != a }'''))],
    ]
}
