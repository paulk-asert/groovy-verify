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
 * 'P523 nested enum constant' — a nested enum's constant spelled through its outer class in a contract
 * ({@code C.L.A}, a property of a property once the contract is re-parsed) wasn't read as a constant: the contract was
 * outside the fragment. Now the outer class's spelling names the same constant as {@code L.A} does.
 */
class G564_p523_nested_enum_constant {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 523: a nested enum's constant spelled through its outer class (C.L.A) in a contract is the constant L.A."

    static final String G = "P523 nested enum constant"
    static String client(String inv, String methods) { """${inv ? "@Invariant({ ${inv} })" : ''}
                    final class B { enum L { A, B }; B.L level }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        ${methods}
                    }""" }

    static final List<Map> CASES = [
        [group: G, name: "a parameter equal to it, non-null", ok: true,
         src: tc('''class C {
                        enum L { A, B }
                        @Requires({ a == C.L.A })
                        static String f(L a) { a.name() }
                    }''')],
        [group: G, name: "every constant, refuted on a null", expect: ['Cannot prove postcondition', 'fails on: f(null)'],
         src: tc('''class C {
                        enum L { A, B }
                        @Ensures({ a == C.L.A || a == C.L.B })
                        static void f(L a) { }
                    }''')],
        [group: G, name: "… mixed spellings, non-null", ok: true,
         src: tc('''class C {
                        enum L { A, B }
                        @Requires({ a != null })
                        @Ensures({ a == C.L.A || a == L.B })
                        static void f(L a) { }
                    }''')],
        [group: G, name: "the same constant as the short spelling", ok: true,
         src: tc('''class C {
                        enum L { A, B }
                        @Requires({ a == L.A })
                        @Ensures({ result })
                        static boolean f(L a) { a == C.L.A }
                    }''')],
        [group: G, name: "a different constant", expect: ['Cannot prove postcondition'],
         src: tc('''class C {
                        enum L { A, B }
                        @Requires({ a == C.L.B })
                        @Ensures({ result })
                        static boolean f(L a) { a == L.A }
                    }''')],
        [group: G, name: "as a map's key", ok: true,
         src: tc('''class C {
                        enum L { A, B }
                        @Requires({ m != null && m[C.L.A] == 3 })
                        @Ensures({ result == 3 })
                        static int f(Map<L, Integer> m) { m[L.A] }
                    }''')],
        [group: G, name: "in a set", ok: true,
         src: tc('''class C {
                        enum L { A, B }
                        @Requires({ s != null && C.L.A in s })
                        @Ensures({ result })
                        static boolean f(Set<L> s) { s.contains(L.A) }
                    }''')],
        [group: G, name: "a receiver's field, through its class", ok: true,
         src: tc(client(null, '''@Requires({ b != null && b.level == B.L.A })
                        @Ensures({ result })
                        static boolean f(B b) { b.level != B.L.B }'''))],
        [group: G, name: "… by its invariant", ok: true,
         src: tc(client('level == B.L.A', '''@Requires({ b != null })
                        @Ensures({ result })
                        static boolean f(B b) { b.level == B.L.A }'''))],
        [group: G, name: "its constants counted", ok: true,
         src: tc('''class C {
                        enum L { A, B, D }
                        @Requires({ n == C.L.values().length })
                        @Ensures({ result == 3 })
                        static int f(int n) { n }
                    }''')],
        [group: G, name: "a simple name two enums share, each its own (Phase 524)", ok: true,
         src: tc('''class C {
                        enum L { A, B }
                        static class D { enum L { X, Y } }
                        @Requires({ a == C.L.A })
                        static String f(L a) { a.name() }
                    }''')],
        [group: G, name: "a missing entry, echoed as written", expect: ["m[C.L.A] is null for a missing key"],
         src: tc('''class C {
                        enum L { A, B }
                        @Requires({ m != null })
                        static int f(Map<L, Integer> m) { m[C.L.A] }
                    }''')],
    ]
}
