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
 * 'P516 enum equality null' — an enum parameter compared with its constant ({@code a == L.Low}) compared its value
 * alone, and an enum's value is always one of its constants (the domain closure), so a null enum equalled one. Now a
 * null equals no constant ({@code null == L.Low} is false), and two enum parameters compare as Phase 515's do: equal
 * only to a null. A lemma over an enum's values that a null breaks ({@code leq(null, null)} is false) is refuted.
 */
class G557_p516_enum_equality_null {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 516: an enum parameter compared with its constant, or with another enum parameter, compares a null as Groovy does: equal to no constant, and only to a null."

    static final List<Map> CASES = [
        [group: "P516 enum equality null", name: "equal to a constant, non-null", ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        @Requires({ a == L.Low })
                        static String f(L a) { a.name() }
                    }''')],
        [group: "P516 enum equality null", name: "… the constant on the left", ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        @Requires({ L.High == a })
                        static String f(L a) { a.name() }
                    }''')],
        [group: "P516 enum equality null", name: "not equal to a constant, maybe null", expect: ['Possible NullPointerException', 'fails on: f(null)'],
         src: tc('''class C {
                        enum L { Low, High }
                        @Requires({ a != L.Low })
                        static String f(L a) { a.name() }
                    }''')],
        [group: "P516 enum equality null", name: "a null equal to no constant, in a body", ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        @Requires({ a == null })
                        @Ensures({ !result })
                        static boolean f(L a) { a == L.Low || a == L.High }
                    }''')],
        [group: "P516 enum equality null", name: "a constant, or not null", ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        @Ensures({ result == (a == L.Low || a == L.High) })
                        static boolean f(L a) { a != null }
                    }''')],
        [group: "P516 enum equality null", name: "every constant, refuted on a null", expect: ['Cannot prove postcondition', 'fails on: f(null)'],
         src: tc('''class C {
                        enum L { Low, High }
                        @Ensures({ a == L.Low || a == L.High })
                        static void f(L a) { }
                    }''')],
        [group: "P516 enum equality null", name: "two null enums, equal", ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        @Requires({ a == null && b == null })
                        @Ensures({ a == b })
                        static void f(L a, L b) { }
                    }''')],
        [group: "P516 enum equality null", name: "a null and a constant, not equal", ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        @Requires({ a == null && b == L.High })
                        @Ensures({ !result })
                        static boolean f(L a, L b) { a == b }
                    }''')],
        [group: "P516 enum equality null", name: "equal to a non-null, non-null", ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        @Requires({ a == b && a == L.Low })
                        static String f(L a, L b) { b.name() }
                    }''')],
        [group: "P516 enum equality null", name: "equal, maybe both null", expect: ['Possible NullPointerException', 'fails on: f(null, null)'],
         src: tc('''class C {
                        enum L { Low, High }
                        @Requires({ a == b })
                        static String f(L a, L b) { b.name() }
                    }''')],
        [group: "P516 enum equality null", name: "a lattice's reflexivity, refuted on a null", expect: ['Cannot prove postcondition', 'fails on: reflexive(null)'],
         src: tc('''class Sec {
                        enum L { Low, High }
                        static boolean leq(L l1, L l2) { l1 == L.Low || l2 == L.High }
                        @Ensures({ leq(l1, l1) })
                        static void reflexive(L l1) { }
                    }''')],
        [group: "P516 enum equality null", name: "… proved for a non-null level", ok: true,
         src: tc('''class Sec {
                        enum L { Low, High }
                        static boolean leq(L l1, L l2) { l1 == L.Low || l2 == L.High }
                        @Requires({ l1 != null })
                        @Ensures({ leq(l1, l1) })
                        static void reflexive(L l1) { }
                    }''')],
        [group: "P516 enum equality null", name: "two enums, maybe unequal", expect: ['Cannot prove postcondition', 'fails on: f('],
         src: tc('''class C {
                        enum L { Low, High }
                        @Ensures({ result })
                        static boolean f(L a, L b) { a == b }
                    }''')],
        [group: "P516 enum equality null", name: "two constants, by value", ok: true,
         src: tc('''class C {
                        enum L { Low, High }
                        @Requires({ a != null && b != null && a != b && a == L.Low })
                        @Ensures({ result })
                        static boolean f(L a, L b) { b == L.High }
                    }''')],
    ]
}
