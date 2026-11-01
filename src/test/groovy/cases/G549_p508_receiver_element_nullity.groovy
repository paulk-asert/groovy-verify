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
 * 'P508 receiver element nullity' — a receiver's list element compared with a number
 * ({@code b.xs[1] == 4}, {@code b.xs[1] > 3}) is non-null where the comparison holds, as a
 * list parameter's is (Phases 445, 487, 488): a null equals only a null and is below every number. The comparison
 * didn't map {@code b.xs} to its named list {@code b$xs} (Phase 500), so the element's null flag stayed free, and
 * {@code b.xs[1] + 1} under {@code @Requires({ b.xs[1] == 4 })} reported a null element, with a repro the precondition
 * rules out ({@code f(new B(xs: [null, null]))}). And a call on an element of a list the verifier doesn't model
 * ({@code s.ns[0].length()} on a receiver's {@code List<String>}, {@code g()[0].length()}) had no null obligation,
 * silently: it's skipped loudly now.
 */
class G549_p508_receiver_element_nullity {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 508: a receiver's list element compared with a number (`b.xs[1] == 4`, `b.xs[1] > 3`) is non-null where the comparison holds; a call on an element of a list not modelled is skipped loudly."

    static String client(String method) { """final class B { List<Integer> xs }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        ${method}
                    }""" }

    static final List<Map> CASES = [

        // ---------- non-null by the comparison ----------
        [group: "P508 receiver element nullity", name: "an element equal to a number, unboxed", ok: true,
         src: tc(client('''@Requires({ b != null && b.xs != null && b.xs.size() == 2 && b.xs[1] == 4 })
                        static int f(B b) { b.xs.size() + b.xs[1] }'''))],
        [group: "P508 receiver element nullity", name: "… read by get", ok: true,
         src: tc(client('''@Requires({ b != null && b.xs != null && b.xs.size() == 2 && b.xs.get(1) == 4 })
                        static int f(B b) { b.xs[1] + 1 }'''))],
        [group: "P508 receiver element nullity", name: "… the number first", ok: true,
         src: tc(client('''@Requires({ b != null && b.xs != null && b.xs.size() == 2 && 4 == b.xs[1] })
                        static int f(B b) { b.xs[1] + 1 }'''))],
        [group: "P508 receiver element nullity", name: "… above a number", ok: true,
         src: tc(client('''@Requires({ b != null && b.xs != null && b.xs.size() == 2 && b.xs[1] > 3 })
                        static int f(B b) { b.xs[1] + 1 }'''))],
        [group: "P508 receiver element nullity", name: "… its value, ensured", ok: true,
         src: tc(client('''@Requires({ b != null && b.xs != null && b.xs.size() == 2 && b.xs[1] == 4 })
                        @Ensures({ result == 5 })
                        static int f(B b) { b.xs[1] + 1 }'''))],
        [group: "P508 receiver element nullity", name: "… after a write to the list", ok: true,
         src: tc(client('''@Requires({ b != null && b.xs != null && b.xs.size() == 2 && b.xs[1] == 4 })
                        static int f(B b) { b.xs.add(3); b.xs[1] + 1 }'''))],

        // ---------- still null where the comparison allows it ----------
        [group: "P508 receiver element nullity", name: "an element not equal to a number", expect: ['b.xs[1] is null for a null element', 'fails on: f(new B(xs: ['],
         src: tc(client('''@Requires({ b != null && b.xs != null && b.xs.size() == 2 && b.xs[1] != 4 })
                        static int f(B b) { b.xs[1] + 1 }'''))],
        [group: "P508 receiver element nullity", name: "… below a number", expect: ['b.xs[1] is null for a null element', 'fails on: f(new B(xs: ['],
         src: tc(client('''@Requires({ b != null && b.xs != null && b.xs.size() == 2 && b.xs[1] < 3 })
                        static int f(B b) { b.xs[1] + 1 }'''))],
        [group: "P508 receiver element nullity", name: "… another element's", expect: ['b.xs[1] is null for a null element', 'fails on: f(new B(xs: ['],
         src: tc(client('''@Requires({ b != null && b.xs != null && b.xs.size() == 2 && b.xs[0] == 4 })
                        static int f(B b) { b.xs[1] + 1 }'''))],
        [group: "P508 receiver element nullity", name: "a call on an element", expect: ['Possible NullPointerException', 'b.xs[0]', 'fails on: f(new B(xs: [null'],
         src: tc(client('''@Requires({ b != null && b.xs != null && b.xs.size() == 2 })
                        static int f(B b) { b.xs[0].intValue() }'''))],
        [group: "P508 receiver element nullity", name: "… equal to a number", ok: true,
         src: tc(client('''@Requires({ b != null && b.xs != null && b.xs.size() == 2 && b.xs[0] == 4 })
                        static int f(B b) { b.xs[0].intValue() }'''))],

        // ---------- an element of a list not modelled: loud ----------
        [group: "P508 receiver element nullity", name: "a call on an unmodelled list's element", expect: ["Skipped element dereference", "the nullity of 's.ns[0]' isn't modelled: it's an element of the list 's.ns'"],
         src: tc('''final class S { List<String> ns }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        @Requires({ s != null && s.ns != null && s.ns.size() == 1 })
                        static int f(S s) { s.ns[0].length() }
                    }''')],
        [group: "P508 receiver element nullity", name: "… read by get", expect: ["Skipped element dereference", "the nullity of 's.ns.get(0)' isn't modelled"],
         src: tc('''final class S { List<String> ns }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        @Requires({ s != null && s.ns != null && s.ns.size() == 1 })
                        static int f(S s) { s.ns.get(0).length() }
                    }''')],
        [group: "P508 receiver element nullity", name: "… a call's result's", expect: ["Skipped element dereference", "it's an element of the list 'g()'"],
         src: tc('''class C {
                        static List<String> g() { [null] }
                        static int f() { g()[0].length() }
                    }''')],
        [group: "P508 receiver element nullity", name: "… by a safe call, harmless", ok: true,
         src: tc('''final class S { List<String> ns }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        @Requires({ s != null && s.ns != null && s.ns.size() == 1 })
                        static Integer f(S s) { s.ns[0]?.length() }
                    }''')],

        // ---------- guards ----------
        [group: "P508 receiver element nullity", name: "an element stated non-null", ok: true,
         src: tc(client('''@Requires({ b != null && b.xs != null && b.xs.size() == 2 && b.xs[1] != null })
                        static int f(B b) { b.xs[1] + 1 }'''))],
    ]
}
