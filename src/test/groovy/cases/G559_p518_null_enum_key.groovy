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
 * 'P518 null enum key' — a null enum's value was pinned to one of its constants (the domain closure, Phase 28), so a map
 * read keyed by a null enum ({@code m[p]}) read a constant's entry, where Groovy reads the null key's: a map may hold
 * one ({@code [(null): 1]}). Now a null enum's value is its own, distinct from every constant's, so {@code m[p]} for a
 * null {@code p} is the null key's entry; two nulls read the same one (Phase 515's domain fact).
 */
class G559_p518_null_enum_key {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 518: a map read keyed by a null enum reads the null key's entry, not a constant's."

    static final List<Map> CASES = [
        [group: "P518 null enum key", name: "a null key's entry, not a constant's", expect: ['Cannot prove postcondition', 'fails on: f([(null): 1, (L.A): 0, (L.B): 0], null)'],
         src: tc('''class C {
                        enum L { A, B }
                        @Requires({ m != null && m[p] == 1 && m[L.A] == 0 && m[L.B] == 0 })
                        @Ensures({ false })
                        static void f(Map<L, Integer> m, L p) { }
                    }''')],
        [group: "P518 null enum key", name: "… so the key is null", ok: true,
         src: tc('''class C {
                        enum L { A, B }
                        @Requires({ m != null && m[p] == 1 && m[L.A] == 0 && m[L.B] == 0 })
                        @Ensures({ p == null })
                        static void f(Map<L, Integer> m, L p) { }
                    }''')],
        [group: "P518 null enum key", name: "a non-null key is a constant", ok: true,
         src: tc('''class C {
                        enum L { A, B }
                        @Requires({ m != null && p != null && m[L.A] == 0 && m[L.B] == 0 })
                        @Ensures({ m[p] == 0 })
                        static void f(Map<L, Integer> m, L p) { }
                    }''')],
        // no failing call shown: the model's map may hold a key that's no constant and not null (an enum's key-set isn't closed)
        [group: "P518 null enum key", name: "a null key's entry is free", expect: ['Cannot prove postcondition'],
         src: tc('''class C {
                        enum L { A, B }
                        @Requires({ m != null && m[L.A] == 0 && m[L.B] == 0 })
                        @Ensures({ m[p] == 0 })
                        static void f(Map<L, Integer> m, L p) { }
                    }''')],
        [group: "P518 null enum key", name: "two null keys, one entry", ok: true,
         src: tc('''class C {
                        enum L { A, B }
                        @Requires({ m != null && p == null && q == null })
                        @Ensures({ m[p] == m[q] })
                        static void f(Map<L, Integer> m, L p, L q) { }
                    }''')],
        [group: "P518 null enum key", name: "a put at a constant doesn't write the null key", expect: ['Cannot prove postcondition', 'fails on: f('],
         src: tc('''class C {
                        enum L { A, B }
                        @Requires({ m != null })
                        @Ensures({ m[p] == 5 })
                        static void f(Map<L, Integer> m, L p) { m[L.A] = 5; m[L.B] = 5 }
                    }''')],
        [group: "P518 null enum key", name: "… for a non-null key it does", ok: true,
         src: tc('''class C {
                        enum L { A, B }
                        @Requires({ m != null && p != null })
                        @Ensures({ m[p] == 5 })
                        static void f(Map<L, Integer> m, L p) { m[L.A] = 5; m[L.B] = 5 }
                    }''')],
        [group: "P518 null enum key", name: "a null level is no constant", ok: true,
         src: tc('''class C {
                        enum L { A, B }
                        @Requires({ p == null })
                        @Ensures({ !result })
                        static boolean f(L p) { p == L.A || p == L.B }
                    }''')],
        [group: "P518 null enum key", name: "every non-null level is a constant", ok: true,
         src: tc('''class C {
                        enum L { A, B, C }
                        @Requires({ p != null && p != L.A && p != L.B })
                        @Ensures({ result })
                        static boolean f(L p) { p == L.C }
                    }''')],
    ]
}
