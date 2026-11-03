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
 * 'P522 receiver enum field' — a receiver's enum field ({@code b.level}) wasn't modelled: it translated as an Int, so a
 * comparison with a constant was outside the fragment and the implicit checks crashed on the sorts ("Sorts Int and L
 * are incompatible"). Now it's a value of the enum's sort under the domain closure tied to its null flag (Phase 521's),
 * and {@code b.level == null} reads that flag, which the receiver's invariant states.
 */
class G563_p522_receiver_enum_field {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 522: a receiver's enum field is modelled: compared with a constant or with null, a map key, under its class invariant."

    static final String G = "P522 receiver enum field"
    static String client(String inv, String methods) { """enum L { A, B }
                    ${inv ? "@Invariant({ ${inv} })" : ''}
                    final class B { L level; Map<L, Integer> m }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        ${methods}
                    }""" }

    static final List<Map> CASES = [
        [group: G, name: "a null field, no constant", ok: true,
         src: tc(client(null, '''@Requires({ b != null && b.level == null })
                        @Ensures({ !result })
                        static boolean f(B b) { b.level == L.A || b.level == L.B }'''))],
        [group: G, name: "every constant, refuted on a null", expect: ['Cannot prove postcondition', 'fails on: f(new B())'],
         src: tc(client(null, '''@Requires({ b != null })
                        @Ensures({ b.level == L.A || b.level == L.B })
                        static void f(B b) { }'''))],
        [group: G, name: "… non-null, every constant", ok: true,
         src: tc(client(null, '''@Requires({ b != null && b.level != null })
                        @Ensures({ b.level == L.A || b.level == L.B })
                        static void f(B b) { }'''))],
        [group: G, name: "non-null by its invariant", ok: true,
         src: tc(client('level != null', '''@Requires({ b != null })
                        @Ensures({ b.level == L.A || b.level == L.B })
                        static void f(B b) { }'''))],
        [group: G, name: "a constant, by its invariant", ok: true,
         src: tc(client('level == L.A', '''@Requires({ b != null })
                        @Ensures({ result })
                        static boolean f(B b) { b.level != L.B }'''))],
        [group: G, name: "as a map's key", ok: true,
         src: tc(client(null, '''@Requires({ m != null && b != null && b.level == L.A && m[L.A] == 3 })
                        @Ensures({ result == 3 })
                        static int f(Map<L, Integer> m, B b) { m[b.level] }'''))],
        [group: G, name: "… a null key's entry", expect: ["m[b.level] is null for a missing key or a null value, and a null can't be cast to int"],
         src: tc(client(null, '''@Requires({ m != null && b != null && m[L.A] == 3 && m[L.B] == 3 })
                        @Ensures({ result == 3 })
                        static int f(Map<L, Integer> m, B b) { m[b.level] }'''))],
    ]
}
