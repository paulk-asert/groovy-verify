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
 * 'P501 receiver list writes' — a statement that mutates a receiver's list directly ({@code b.xs.add(v)},
 * {@code add(i, v)}, {@code clear()}, {@code pop()}, {@code removeLast()}, {@code removeAt(i)}) writes the named list
 * {@code b$xs} (Phase 500), as a list parameter's mutation is modelled. Such a method's lists were unmodelled, so a
 * {@code b.xs.clear()} that broke {@code B}'s {@code @Invariant({ xs.size() > 0 })} compiled cleanly: {@code b} owes
 * its invariant at the exit now, as a field written through it does (Phase 433). A write in a loop, or a receiver
 * handed to a call, keeps the lists unmodelled (a removal used as a value did too, until Phase 504).
 */
class G542_p501_receiver_list_writes {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 501: `b.xs.add(v)`, `b.xs.clear()` and the other list mutations on a receiver's list are modelled, and `b` owes its class invariant at the exit."

    static String client(String inv, String method) { """@Invariant({ ${inv} })
                    final class B { List<Integer> xs }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        ${method}
                    }""" }

    static final List<Map> CASES = [

        // ---------- the write ----------
        [group: "P501 receiver list writes", name: "an add, then the size", ok: true,
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 0 })
                        @Ensures({ result == 1 })
                        static int f(B b) { b.xs.add(5); b.xs.size() }'''))],
        [group: "P501 receiver list writes", name: "… and the element", ok: true,
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 1 })
                        @Ensures({ result == 5 })
                        static Integer f(B b) { b.xs.add(5); b.xs[1] }'''))],
        [group: "P501 receiver list writes", name: "a pop shifts the rest down", ok: true,
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 2 && b.xs[1] == 7 })
                        @Ensures({ result == 7 })
                        static Integer f(B b) { b.xs.pop(); b.xs[0] }'''))],
        [group: "P501 receiver list writes", name: "an insertion at the front", ok: true,
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 1 })
                        @Ensures({ result == 4 })
                        static Integer f(B b) { b.xs.add(0, 4); b.xs[0] }'''))],
        [group: "P501 receiver list writes", name: "under an if", ok: true,
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 0 })
                        @Ensures({ result == (k > 0 ? 1 : 0) })
                        static int f(B b, int k) { if (k > 0) b.xs.add(1); b.xs.size() }'''))],
        [group: "P501 receiver list writes", name: "a clear, then a get", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 0 && 0 < b.xs.size()'],
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 1 })
                        static Integer f(B b) { b.xs.clear(); b.xs.get(0) }'''))],

        // ---------- the receiver's invariant ----------
        [group: "P501 receiver list writes", name: "a write that breaks the receiver's invariant", expect: ["Cannot prove class invariant of B holds for 'b' at exit of f, after a write through it"],
         src: tc(client('xs != null && xs.size() > 0', '''@Requires({ b != null })
                        static void f(B b) { b.xs.clear() }'''))],
        [group: "P501 receiver list writes", name: "… a removal that may", expect: ["Cannot prove class invariant of B holds for 'b'", 'fails on: f(new B(xs: [0]))'],
         src: tc(client('xs != null && xs.size() > 0', '''@Requires({ b != null })
                        static void f(B b) { b.xs.removeLast() }'''))],
        [group: "P501 receiver list writes", name: "… one that keeps it", ok: true,
         src: tc(client('xs != null && xs.size() > 0', '''@Requires({ b != null })
                        static void f(B b) { b.xs.add(3) }'''))],
        [group: "P501 receiver list writes", name: "… a removal that keeps it", ok: true,
         src: tc(client('xs != null && xs.size() > 0', '''@Requires({ b != null && b.xs.size() > 1 })
                        static void f(B b) { b.xs.pop() }'''))],

        // ---------- still unmodelled ----------
        // modelled since Phase 504: the pop leaves one
        [group: "P501 receiver list writes", name: "a removal's value", expect: ['Cannot prove postcondition', 'fails on: f(new B(xs: ['],
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 2 })
                        @Ensures({ result == 2 })
                        static int f(B b) { Integer r = b.xs.pop(); b.xs.size() }'''))],
        [group: "P501 receiver list writes", name: "a write in a loop", expect: ['Skipped verification of postcondition'],
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 0 })
                        @Ensures({ result == 2 })
                        static int f(B b) { for (int i = 0; i < 2; i++) { b.xs.add(i) }; b.xs.size() }'''))],
        [group: "P501 receiver list writes", name: "a receiver handed to a call", expect: ['outside fragment'],
         src: tc('''@Invariant({ xs != null })
                    final class B { List<Integer> xs }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        static void h(B b) { }
                        @Requires({ b != null && b.xs.size() == 0 })
                        @Ensures({ result == 1 })
                        static int f(B b) { b.xs.add(1); h(b); b.xs.size() }
                    }''')],
        [group: "P501 receiver list writes", name: "… a pure one, which assumes the invariant the write broke", expect: ['Skipped verification of postcondition'],
         src: tc('''@Invariant({ xs != null && xs.size() > 0 })
                    final class B { List<Integer> xs }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        @Requires({ b != null })
                        @Modifies({ [] })
                        @Ensures({ result > 0 })
                        static int h(B b) { b.xs.size() }
                        @Requires({ b != null })
                        @Ensures({ result > 0 })
                        static int f(B b) { b.xs.clear(); int n = h(b); b.xs.add(1); n }
                    }''')],
    ]
}
