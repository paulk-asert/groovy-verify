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
 * 'P521 null enum field' — Phase 518's open item. An enum field's value was pinned to one of its constants, a null's
 * too (the domain closure), so a null field equalled a constant by value and a map read keyed by it read a constant's
 * entry. Now a field's null is the sort's null literal, as a parameter's is (Phase 518): no constant, the null key.
 */
class G562_p521_null_enum_field {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 521: a null enum field is no constant, and a map read keyed by it reads the null key's entry."

    static final String G = "P521 null enum field"

    static final List<Map> CASES = [
        [group: G, name: "a null field equal to no constant", ok: true,
         src: tc('''class C {
                        enum L { A, B }
                        L level
                        @Requires({ level == null })
                        @Ensures({ !result })
                        boolean f() { level == L.A || level == L.B }
                    }''')],
        [group: G, name: "every constant, refuted on a null field", expect: ['Cannot prove postcondition'],
         src: tc('''class C {
                        enum L { A, B }
                        L level
                        @Ensures({ level == L.A || level == L.B })
                        void f() { }
                    }''')],
        [group: G, name: "a null field's key, not a constant's", expect: ['Cannot prove postcondition'],
         src: tc('''class C {
                        enum L { A, B }
                        L level
                        Map<L, Integer> m
                        @Requires({ m != null && m[L.A] == 0 && m[L.B] == 0 })
                        @Ensures({ m[level] == 0 })
                        void f() { }
                    }''')],
        [group: G, name: "… a non-null one is a constant", ok: true,
         src: tc('''class C {
                        enum L { A, B }
                        L level
                        Map<L, Integer> m
                        @Requires({ m != null && level != null && m[L.A] == 0 && m[L.B] == 0 })
                        @Ensures({ m[level] == 0 })
                        void f() { }
                    }''')],
        [group: G, name: "a field written, then read", ok: true,
         src: tc('''class C {
                        enum L { A, B }
                        L level
                        @Ensures({ level == L.A })
                        void f() { level = L.A }
                    }''')],
        [group: G, name: "a null local, no constant", ok: true,
         src: tc('''class C {
                        enum L { A, B }
                        @Requires({ p == null })
                        @Ensures({ !result })
                        static boolean f(L p) { L x = p; x == L.A || x == L.B }
                    }''')],
    ]
}
