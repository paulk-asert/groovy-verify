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
 * 'P504 receiver list values' — a removal whose value is kept ({@code Integer r = b.xs.pop()}) and an element store
 * ({@code b.xs[i] = v}) on a receiver's list are modelled, as on a list parameter's: both kept the method's lists
 * unmodelled (loud since Phase 503). A list parameter's removal kept as a value wrote nothing in the obligation passes,
 * so {@code Integer r = xs.pop(); xs.get(1)} on a two-element list compiled cleanly. And a method that writes a
 * receiver's list (Phase 501) read any other list as apart from it, though the caller may pass {@code b.xs} itself:
 * {@code b.xs.add(5); ys.size()} proved {@code ys} unchanged. The written list must be the only list it reads now.
 */
class G545_p504_receiver_list_values {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 504: a kept removal (`Integer r = b.xs.pop()`) and an element store (`b.xs[i] = v`) on a receiver's list are modelled; a list parameter's kept removal shrinks the list; a written receiver list must be the only list the method reads."

    static String client(String inv, String method, String fields = 'List<Integer> xs') { """@Invariant({ ${inv} })
                    final class B { ${fields} }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        ${method}
                    }""" }

    static final List<Map> CASES = [

        // ---------- a removal's value ----------
        [group: "P504 receiver list values", name: "a receiver's pop, kept", ok: true,
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 2 && b.xs[0] == 7 })
                        @Ensures({ result == 7 })
                        static Integer f(B b) { Integer r = b.xs.pop(); r }'''))],
        [group: "P504 receiver list values", name: "… and the list after it", ok: true,
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 2 })
                        @Ensures({ result == 1 })
                        static int f(B b) { Integer r = b.xs.pop(); b.xs.size() }'''))],
        [group: "P504 receiver list values", name: "removeLast's value", ok: true,
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 2 && b.xs[1] == 9 })
                        @Ensures({ result == 9 })
                        static Integer f(B b) { Integer r = b.xs.removeLast(); r }'''))],
        [group: "P504 receiver list values", name: "a removal's value that may be wrong", expect: ['Cannot prove postcondition'],
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 2 && b.xs[1] == 9 })
                        @Ensures({ result == 9 })
                        static Integer f(B b) { Integer r = b.xs.pop(); r }'''))],
        [group: "P504 receiver list values", name: "a removal's value, unboxed", expect: ['b.xs.removeAt(0) is null for a null element'],
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() > 0 })
                        static int f(B b) { int r = b.xs.removeAt(0); r }'''))],
        [group: "P504 receiver list values", name: "a removal's value, as an index", ok: true,
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 2 && b.xs[0] == 0 })
                        static Integer f(B b) { Integer r = b.xs.pop(); b.xs.get(r) }'''))],
        [group: "P504 receiver list values", name: "a removal from a list that may be empty", expect: ['Possible IndexOutOfBoundsException'],
         src: tc(client('xs != null', '''@Requires({ b != null })
                        static Integer f(B b) { Integer r = b.xs.pop(); r }'''))],
        [group: "P504 receiver list values", name: "a removal's value, then a read past the end", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 1 && 1 < b.xs.size()'],
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 2 })
                        static Integer f(B b) { Integer r = b.xs.pop(); b.xs.get(1) }'''))],

        // ---------- a list parameter's removal, kept ----------
        [group: "P504 receiver list values", name: "a list parameter's removal, then a read past the end", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 1 && 1 < xs.size()'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 })
                        static Integer f(List<Integer> xs) { Integer r = xs.pop(); xs.get(1) }
                    }''')],
        [group: "P504 receiver list values", name: "… assigned", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 1 && 1 < xs.size()'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 })
                        static Integer f(List<Integer> xs) { Integer r; r = xs.pop(); xs.get(1) }
                    }''')],
        [group: "P504 receiver list values", name: "… into a parameter", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 1 && 1 < xs.size()'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 })
                        static Integer f(List<Integer> xs, Integer p) { p = xs.pop(); xs.get(1) }
                    }''')],
        [group: "P504 receiver list values", name: "… and its value, as an index", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == 0 })
                        static Integer f(List<Integer> xs, Integer p) { p = xs.pop(); xs.get(p) }
                    }''')],
        [group: "P504 receiver list values", name: "… in an if's arm", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 1 && 1 < xs.size()'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 })
                        static Integer f(List<Integer> xs, int k) { if (k > 0) { Integer r = xs.pop() }; xs.get(1) }
                    }''')],
        [group: "P504 receiver list values", name: "… and a read it keeps in bounds", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 })
                        static Integer f(List<Integer> xs) { Integer r; r = xs.pop(); xs.get(0) }
                    }''')],

        // ---------- an element store ----------
        [group: "P504 receiver list values", name: "an element store", ok: true,
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 2 })
                        @Ensures({ result == 5 })
                        static Integer f(B b) { b.xs[0] = 5; b.xs[0] }'''))],
        [group: "P504 receiver list values", name: "… the size kept", ok: true,
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 2 })
                        @Ensures({ result == 2 })
                        static int f(B b) { b.xs[1] = 5; b.xs.size() }'''))],
        [group: "P504 receiver list values", name: "a store whose value writes", expect: ['Skipped verification of postcondition'],
         src: tc('''@Invariant({ xs != null })
                    final class B { List<Integer> xs }
                    final class D { int n }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        @Requires({ b != null && d != null && b.xs.size() > 0 && d.n == 0 })
                        @Ensures({ d.n == 0 })
                        static void f(B b, D d) { b.xs[0] = (d.n = 5) }
                    }''')],
        [group: "P504 receiver list values", name: "a store that breaks the receiver's invariant", expect: ["Cannot prove class invariant of B holds for 'b' at exit of f, after a write through it"],
         src: tc(client('xs != null && xs.size() > 0 && xs[0] > 0', '''@Requires({ b != null })
                        static void f(B b) { b.xs[0] = -1 }'''))],
        [group: "P504 receiver list values", name: "… one that keeps it", ok: true,
         src: tc(client('xs != null && xs.size() > 0 && xs[0] > 0', '''@Requires({ b != null })
                        static void f(B b) { b.xs[0] = 3 }'''))],
        [group: "P504 receiver list values", name: "a store, then a read it puts out of bounds", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= b.xs[0] && b.xs[0] < b.xs.size()'],
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 2 })
                        static Integer f(B b) { b.xs[0] = 2; b.xs.get(b.xs[0]) }'''))],
        [group: "P504 receiver list values", name: "… or keeps in bounds", ok: true,
         src: tc(client('xs != null', '''@Requires({ b != null && b.xs.size() == 2 })
                        static Integer f(B b) { b.xs[0] = 1; b.xs.get(b.xs[0]) }'''))],

        // ---------- the written list, by another name ----------
        [group: "P504 receiver list values", name: "a list parameter beside a written list", expect: ['Skipped verification of postcondition'],
         src: tc(client('xs != null', '''@Requires({ b != null && ys != null && b.xs.size() == 0 && ys.size() == 0 })
                        @Ensures({ result == 0 })
                        static int f(B b, List<Integer> ys) { b.xs.add(5); ys.size() }'''))],
        [group: "P504 receiver list values", name: "… the receiver's other list", expect: ['Skipped verification of postcondition'],
         src: tc(client('xs != null && ys != null', '''@Requires({ b != null && b.xs.size() == 0 && b.ys.size() == 0 })
                        @Ensures({ result == 0 })
                        static int f(B b) { b.xs.add(5); b.ys.size() }''', 'List<Integer> xs; List<Integer> ys'))],
        [group: "P504 receiver list values", name: "… a field a contract reads", expect: ['Skipped verification of postcondition'],
         src: tc('''class C {
                        List<Integer> zs
                        @Requires({ b != null && zs != null && zs.size() == 0 })
                        @Ensures({ zs.size() == 0 })
                        void f(B b) { b.xs.add(5) }
                    }
                    @Invariant({ xs != null })
                    final class B { List<Integer> xs }''')],
        [group: "P504 receiver list values", name: "… a list parameter only a contract reads", expect: ['Skipped verification of postcondition'],
         src: tc(client('xs != null', '''@Requires({ b != null && ys != null && ys.size() == 0 })
                        @Ensures({ ys.size() == 0 })
                        static void f(B b, List<Integer> ys) { b.xs.add(5) }'''))],
        [group: "P504 receiver list values", name: "… the receiver's other list its invariant reads", expect: ["Skipped the class invariant check of B for 'b' after 'b.xs.add(5)'"],
         src: tc(client('xs != null && ys != null && ys.size() == 0', '''@Requires({ b != null })
                        static void f(B b) { b.xs.add(5) }''', 'List<Integer> xs; List<Integer> ys'))],
        [group: "P504 receiver list values", name: "… a field the body reads", expect: ['Skipped verification of postcondition'],
         src: tc('''class C {
                        List<Integer> zs
                        @Requires({ b != null })
                        @Ensures({ result == 1 })
                        int f(B b) { if (zs == null) return 1; int n = zs.size(); b.xs.add(5); n == zs.size() ? 1 : 0 }
                    }
                    @Invariant({ xs != null })
                    final class B { List<Integer> xs }''')],
        [group: "P504 receiver list values", name: "… a field its own class invariant reads", expect: ['Skipped verification of postcondition'],
         src: tc('''@Invariant({ zs != null && zs.size() == 0 })
                    class C {
                        List<Integer> zs
                        @Requires({ b != null })
                        void f(B b) { b.xs.add(5) }
                    }
                    @Invariant({ xs != null })
                    final class B { List<Integer> xs }''')],
        [group: "P504 receiver list values", name: "… but not an array", ok: true,
         src: tc(client('xs != null', '''@Requires({ b != null && a != null && b.xs.size() == 0 })
                        @Ensures({ result == a.length + 1 })
                        static int f(B b, int[] a) { b.xs.add(5); a.length + b.xs.size() }'''))],
    ]
}
