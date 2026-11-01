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
 * 'P505 removals in expressions' — a removal inside an expression ({@code xs.pop() + xs.get(0)}, {@code g(xs.pop())},
 * {@code if (xs.pop() > 0)}) wrote nothing in the obligation passes: they take a kept removal's value and write
 * (Phase 504) only at the top of a statement. So a read after it, in the statement or after it, saw the list as it was,
 * and {@code xs.pop() + xs.get(0)} on a one-element list compiled cleanly. Each such removal is now a declaration of its
 * value before the statement, where it runs, and a part evaluated before it is kept first. One that may not run (under
 * {@code &&}, {@code ||} or {@code ?:}) and any other list write used as a value ({@code boolean t = xs.remove(o)}) are
 * a write inside the statement (Phase 373), and its postcondition is skipped. (Phase 506 runs one that may not run on
 * its way only: the cases below that read it as any list now see it removed, or not, by the way taken.)
 */
class G546_p505_removals_in_expressions {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 505: a removal inside an expression (`xs.pop() + xs.get(0)`, `g(xs.pop())`, `if (xs.pop() > 0)`) shrinks the list where it runs; another list write used as a value is a write inside the statement."

    static String client(String method) { """final class B { List<Integer> xs }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        ${method}
                    }""" }

    static final List<Map> CASES = [

        // ---------- a removal, then a read past the end ----------
        [group: "P505 removals in expressions", name: "a removal, then a read in the same expression", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 0 && 0 < xs.size()', 'fails on: f(['],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 && xs[0] != null })
                        static int f(List<Integer> xs) { xs.pop() + xs.get(0) }
                    }''')],
        [group: "P505 removals in expressions", name: "… returned", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 0 && 0 < xs.size()'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 && xs[0] != null })
                        static int f(List<Integer> xs) { return xs.removeLast() + xs.get(0) }
                    }''')],
        [group: "P505 removals in expressions", name: "… in a declaration's value", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 0 && 0 < xs.size()'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 && xs[0] != null })
                        static void f(List<Integer> xs) { int r = xs.pop() + xs.get(0) }
                    }''')],
        [group: "P505 removals in expressions", name: "… as a call's arguments", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 0 && 0 < xs.size()'],
         src: tc('''class C {
                        static int g(int a, int b) { a + b }
                        @Requires({ xs != null && xs.size() == 1 && xs[0] != null })
                        static int f(List<Integer> xs) { g(xs.pop(), xs.get(0)) }
                    }''')],
        [group: "P505 removals in expressions", name: "… by index", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 1 && 1 < xs.size()'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[1] != null })
                        static int f(List<Integer> xs) { xs.removeAt(1) * 2 + xs.get(1) }
                    }''')],
        [group: "P505 removals in expressions", name: "a removal inside a declaration, then a read after it", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 1 && 1 < xs.size()'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] != null })
                        static Integer f(List<Integer> xs) { int r = xs.pop() + 1; xs.get(1) }
                    }''')],
        [group: "P505 removals in expressions", name: "a removal in an if's condition, then a read in its arm", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 0 && 0 < xs.size()'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 && xs[0] != null })
                        static int f(List<Integer> xs) { if (xs.pop() > 0) { return xs.get(0) }; 0 }
                    }''')],
        [group: "P505 removals in expressions", name: "… or after the if", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 1 && 1 < xs.size()'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] != null })
                        static Integer f(List<Integer> xs, int n) { if (xs.pop() > n) { n = 0 }; xs.get(1) }
                    }''')],
        [group: "P505 removals in expressions", name: "a stack's two removals, one past the end", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 0 && 0 < xs.size()'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 && xs[0] != null })
                        static void f(List<Integer> xs) { xs.add(xs.removeLast() + xs.removeLast()) }
                    }''')],
        [group: "P505 removals in expressions", name: "a removal in a loop's body", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 0 && 0 < xs.size()'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 && xs[0] != null })
                        static int f(List<Integer> xs) { int s = 0; int i = 0; while (i < 1) { s = s + xs.pop() + xs.get(0); i++ }; s }
                    }''')],

        // ---------- what the removal leaves ----------
        [group: "P505 removals in expressions", name: "a read before the removal", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 && xs[0] != null })
                        static int f(List<Integer> xs) { xs.get(0) + xs.pop() }
                    }''')],
        [group: "P505 removals in expressions", name: "… its value, kept from before it", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == 1 && xs[1] == 5 })
                        @Ensures({ result == 2 })
                        static int f(List<Integer> xs) { xs.get(0) + xs.pop() }
                    }''')],
        [group: "P505 removals in expressions", name: "… not the one after it", expect: ['Cannot prove postcondition', 'fails on: f([1, 5])'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == 1 && xs[1] == 5 })
                        @Ensures({ result == 6 })
                        static int f(List<Integer> xs) { xs.get(0) + xs.pop() }
                    }''')],
        [group: "P505 removals in expressions", name: "two removals", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 3 && xs[0] == 1 && xs[1] == 5 })
                        @Ensures({ result == 6 && xs.size() == 1 })
                        static int f(List<Integer> xs) { xs.pop() + xs.pop() }
                    }''')],
        [group: "P505 removals in expressions", name: "a stack's two removals and a push", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 3 && xs[1] == 2 && xs[2] == 5 })
                        @Ensures({ xs.size() == 2 && xs[1] == 7 })
                        static void f(List<Integer> xs) { xs.add(xs.removeLast() + xs.removeLast()) }
                    }''')],
        [group: "P505 removals in expressions", name: "a size either side of the removal", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 })
                        @Ensures({ result == 3 })
                        static int f(List<Integer> xs) { xs.size() + (xs.pop() == null ? 0 : 0) + xs.size() }
                    }''')],
        [group: "P505 removals in expressions", name: "a removal's value, unboxed, as written", expect: ['Possible NullPointerException: xs.pop() is null for a null element', 'obligation: xs.pop() != null'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 })
                        static int f(List<Integer> xs) { xs.pop() + 1 }
                    }''')],

        // ---------- a receiver's list ----------
        [group: "P505 removals in expressions", name: "a receiver's removal, then a read", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 0 && 0 < b.xs.size()', 'fails on: f(new B(xs: ['],
         src: tc(client('''@Requires({ b != null && b.xs != null && b.xs.size() == 1 && b.xs[0] != null })
                        static int f(B b) { b.xs.pop() + b.xs.get(0) }'''))],
        [group: "P505 removals in expressions", name: "… its sizes either side", ok: true,
         src: tc(client('''@Requires({ b != null && b.xs != null && b.xs.size() == 2 })
                        @Ensures({ result == 3 && b.xs.size() == 1 })
                        static int f(B b) { b.xs.size() + (b.xs.pop() == null ? 0 : 0) + b.xs.size() }'''))],

        // ---------- a write that may not run, or used as a value ----------
        [group: "P505 removals in expressions", name: "a removal under &&, then a read", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 1 && 1 < xs.size()'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] != null })
                        static Integer f(List<Integer> xs, boolean b) { boolean t = b && xs.pop() > 0; xs.get(1) }
                    }''')],
        [group: "P505 removals in expressions", name: "… in a ternary's arm", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 1 && 1 < xs.size()'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] != null })
                        static Integer f(List<Integer> xs, boolean b) { int t = b ? xs.pop() : 0; xs.get(1) }
                    }''')],
        [group: "P505 removals in expressions", name: "… its postcondition, on the way that doesn't remove", expect: ['Cannot prove postcondition', 'fails on: f([', ', false)'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] != null })
                        @Ensures({ xs.size() == 1 })
                        static void f(List<Integer> xs, boolean b) { boolean t = b && xs.pop() > 0 }
                    }''')],
        [group: "P505 removals in expressions", name: "… and returned", expect: ['Cannot prove postcondition', 'fails on: f([', ', false)'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] != null })
                        @Ensures({ xs.size() == 1 })
                        static boolean f(List<Integer> xs, boolean b) { return b && xs.pop() > 0 }
                    }''')],
        [group: "P505 removals in expressions", name: "… a ternary's arm, its postcondition", expect: ['Cannot prove postcondition', 'fails on: f([', ', false)'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] != null })
                        @Ensures({ result == 1 })
                        static int f(List<Integer> xs, boolean b) { int t = b ? xs.pop() : 0; xs.size() }
                    }''')],
        [group: "P505 removals in expressions", name: "a guarded removal under &&", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && !xs.contains(null) })
                        static boolean f(List<Integer> xs) { boolean t = !xs.isEmpty() && xs.pop() > 0; t }
                    }''')],
        [group: "P505 removals in expressions", name: "a list's write as a value, then a read", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 1 && 1 < xs.size()'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 })
                        static Integer f(List<Integer> xs) { boolean t = xs.remove((Object) 5); xs.get(1) }
                    }''')],
        [group: "P505 removals in expressions", name: "… its postcondition, skipped", expect: ["Skipped verification of postcondition for f (a list written inside an expression, 'xs.retainAll(ys)'"],
         src: tc('''class C {
                        @Requires({ xs != null && ys != null && xs.size() == 2 })
                        @Ensures({ result == 2 })
                        static int f(List<Integer> xs, List<Integer> ys) { boolean t = xs.retainAll(ys); xs.size() }
                    }''')],
        [group: "P505 removals in expressions", name: "an add's value, always true", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 })
                        @Ensures({ result == 3 })
                        static int f(List<Integer> xs) { boolean t = xs.add(5); t ? xs.size() : 0 }
                    }''')],
        [group: "P505 removals in expressions", name: "… and the list it grew", expect: ['Cannot prove postcondition', 'fails on: f(['],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 })
                        @Ensures({ result == 2 })
                        static int f(List<Integer> xs) { boolean t = xs.add(5); xs.size() }
                    }''')],
        [group: "P505 removals in expressions", name: "… read inside an expression", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 0 })
                        static Integer f(List<Integer> xs) { boolean t = xs.add(5) && xs.size() == 1; xs.get(0) }
                    }''')],
    ]
}
