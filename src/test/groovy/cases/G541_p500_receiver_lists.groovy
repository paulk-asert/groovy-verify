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
 * 'P500 receiver lists' — a receiver's list field read in a body ({@code b.xs.size()}, {@code b.xs[i]}), as Phase 413
 * reads a receiver's int array: the named list {@code b$xs}, the name a foreign invariant assumed for {@code b} speaks
 * of (Phase 496). So {@code B}'s {@code @Invariant({ xs != null && xs.size() > 0 })} proves {@code b.xs.size() > 0}.
 */
class G541_p500_receiver_lists {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 500: a receiver's `List<Integer>` field reads in a body — `b.xs.size()`, `b.xs[i]`, `b.xs.get(i)` — as the list its class invariant speaks of."

    static String client(String inv, String method) { """@Invariant({ ${inv} })
                    final class B { List<Integer> xs }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        ${method}
                    }""" }

    static final List<Map> CASES = [

        // ---------- what the invariant says of it ----------
        [group: "P500 receiver lists", name: "a receiver's list size, by its invariant", ok: true,
         src: tc(client('xs != null && xs.size() > 0', '''@Requires({ b != null })
                        @Ensures({ result > 0 })
                        static int f(B b) { b.xs.size() }'''))],
        [group: "P500 receiver lists", name: "… not without it", expect: ['Cannot prove postcondition', 'counterexample: b.xs.size() = 0', 'fails on: f(new B(xs: []))'],
         src: tc(client('xs != null', '''@Requires({ b != null })
                        @Ensures({ result > 0 })
                        static int f(B b) { b.xs.size() }'''))],
        [group: "P500 receiver lists", name: "… an element", ok: true,
         src: tc(client('xs != null && xs.size() > 0 && xs[0] == 3', '''@Requires({ b != null })
                        @Ensures({ result == 3 })
                        static Integer f(B b) { b.xs[0] }'''))],
        [group: "P500 receiver lists", name: "… by get", ok: true,
         src: tc(client('xs != null && xs.size() > 0 && xs[0] == 3', '''@Requires({ b != null })
                        @Ensures({ result == 3 })
                        static Integer f(B b) { b.xs.get(0) }'''))],
        [group: "P500 receiver lists", name: "… its nullity", ok: true,
         src: tc(client('xs != null && xs.size() > 0 && xs[0] != null', '''@Requires({ b != null })
                        @Ensures({ result })
                        static boolean f(B b) { b.xs[0] != null }'''))],
        [group: "P500 receiver lists", name: "… isEmpty", ok: true,
         src: tc(client('xs != null && xs.size() > 0', '''@Requires({ b != null })
                        @Ensures({ !result })
                        static boolean f(B b) { b.xs.isEmpty() }'''))],
        [group: "P500 receiver lists", name: "the method's own precondition on it", ok: true,
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 2 })
                        @Ensures({ result == 2 })
                        static int f(B b) { b.xs.size() }'''))],

        // ---------- its obligations ----------
        [group: "P500 receiver lists", name: "a get past the end throws", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 1 && 1 < b.xs.size()', 'fails on: f(new B(xs: [0]))'],
         src: tc(client('xs != null && xs.size() > 0', '''@Requires({ b != null })
                        static Integer f(B b) { b.xs.get(1) }'''))],
        [group: "P500 receiver lists", name: "… in bounds by the invariant", ok: true,
         src: tc(client('xs != null && xs.size() > 1', '''@Requires({ b != null })
                        static Integer f(B b) { b.xs.get(1) }'''))],
        [group: "P500 receiver lists", name: "a null list's size throws", expect: ['Possible NullPointerException: Cannot invoke method size() on null object', 'obligation: b.xs != null', 'fails on: f(new B(xs: null))'],
         src: tc(client('true', '''@Requires({ b != null })
                        static int f(B b) { b.xs.size() }'''))],
        [group: "P500 receiver lists", name: "an unboxed null element", expect: ['Possible NullPointerException: b.xs[0] is null for a null element', 'fails on: f(new B(xs: [null]))'],
         src: tc(client('xs != null && xs.size() > 0', '''@Requires({ b != null })
                        static int f(B b) { b.xs[0] + 1 }'''))],
        [group: "P500 receiver lists", name: "a subscript's bounds", expect: ['List index may be outside [0, size)', 'b.xs.size()'],
         src: tc(client('xs != null', '''@Requires({ b != null })
                        static Integer f(B b) { b.xs[0] }'''))],

        // ---------- what isn't modelled ----------
        [group: "P500 receiver lists", name: "a method that writes the list", expect: ['Skipped verification of postcondition'],
         src: tc(client('xs != null && xs.size() > 0', '''@Requires({ b != null })
                        @Ensures({ result > 0 })
                        static int f(B b) { b.xs.clear(); b.xs.size() }'''))],
        [group: "P500 receiver lists", name: "… or writes it through a local", expect: ['share its contents with'],
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 0 })
                        @Ensures({ result == 0 })
                        static int f(B b) { List<Integer> t = b.xs; t.add(5); b.xs.size() }'''))],
        [group: "P500 receiver lists", name: "two receivers of the class", expect: ['outside fragment'],
         src: tc(client('xs != null && xs.size() > 0', '''@Requires({ b != null && c != null })
                        @Ensures({ result > 0 })
                        static int f(B b, B c) { b.xs.size() }'''))],
    ]
}
