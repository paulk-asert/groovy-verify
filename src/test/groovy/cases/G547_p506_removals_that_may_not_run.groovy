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
 * 'P506 removals that may not run' — a removal under {@code &&}, {@code ||}, {@code ?:} or an elvis runs only on the
 * way that reaches it. Phase 505 left one inside the statement, a write the safety checks took as any list (so
 * {@code b && xs.pop() > 0} on a two-element list falsely reported a read of {@code xs.get(0)} after it) and the
 * postcondition skipped. Each is now an if that runs the removal on its way only, its value a local
 * ({@code boolean $c = false; if (b) { Integer $r = xs.pop(); if ($r > 0) $c = true }}).
 */
class G547_p506_removals_that_may_not_run {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 506: a removal that may not run (`b && xs.pop() > 0`, `b ? xs.pop() : 0`, `n ?: xs.pop()`) shrinks the list only on the way that reaches it."

    static String client(String method) { """final class B { List<Integer> xs }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        ${method}
                    }""" }

    static final List<Map> CASES = [

        // ---------- a read after it, on either way ----------
        [group: "P506 removals that may not run", name: "a removal under &&, then a read either way", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] != null })
                        static Integer f(List<Integer> xs, boolean b) { boolean t = b && xs.pop() > 0; xs.get(0) }
                    }''')],
        [group: "P506 removals that may not run", name: "… under ||", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] != null })
                        static Integer f(List<Integer> xs, boolean b) { boolean t = b || xs.pop() > 0; xs.get(0) }
                    }''')],
        [group: "P506 removals that may not run", name: "… in a ternary's arm", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] != null })
                        static Integer f(List<Integer> xs, boolean b) { int t = b ? xs.pop() : 0; xs.get(0) }
                    }''')],
        [group: "P506 removals that may not run", name: "… in an if's condition", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == 5 })
                        static Integer f(List<Integer> xs, boolean b) { if (b && xs.pop() > 0) { return xs.get(0) }; xs.get(1) }
                    }''')],
        [group: "P506 removals that may not run", name: "a guard on the size, then a read", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() >= 1 && !xs.contains(null) })
                        static Integer f(List<Integer> xs) { boolean t = xs.size() > 1 && xs.pop() > 0; xs.get(0) }
                    }''')],
        [group: "P506 removals that may not run", name: "a receiver's removal under &&, then a read", ok: true,
         src: tc(client('''@Requires({ b != null && b.xs != null && b.xs.size() == 2 && b.xs[0] != null })
                        static Integer f(B b, boolean c) { boolean t = c && b.xs.pop() > 0; b.xs.get(0) }'''))],

        // ---------- still past the end, on the way that removes ----------
        [group: "P506 removals that may not run", name: "a read past the end on the way that removes", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 1 && 1 < xs.size()', 'fails on: f([', ', true)'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] != null })
                        static Integer f(List<Integer> xs, boolean b) { boolean t = b && xs.pop() > 0; xs.get(1) }
                    }''')],
        [group: "P506 removals that may not run", name: "… under || on the way that removes", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 1 && 1 < xs.size()', 'fails on: f([', ', false)'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] != null })
                        static Integer f(List<Integer> xs, boolean b) { boolean t = b || xs.pop() > 0; xs.get(1) }
                    }''')],
        [group: "P506 removals that may not run", name: "… in a ternary's other arm", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 1 && 1 < xs.size()', 'fails on: f([', ', false)'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] != null })
                        static Integer f(List<Integer> xs, boolean b) { int t = b ? 0 : xs.pop(); xs.get(1) }
                    }''')],
        [group: "P506 removals that may not run", name: "two removals under &&, the second past the end", expect: ['Possible IndexOutOfBoundsException', 'fails on: f([', ', true)'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 && xs[0] == 5 })
                        static boolean f(List<Integer> xs, boolean b) { b && xs.pop() > 0 && xs.pop() > 0 }
                    }''')],
        [group: "P506 removals that may not run", name: "… on a removal taken when the left value is negative", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 1 && 1 < xs.size()', 'fails on: f([', ', true)'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] != null })
                        static Integer f(List<Integer> xs, boolean b) { if (b && xs.pop() > 0) { return xs.get(0) }; xs.get(1) }
                    }''')],
        [group: "P506 removals that may not run", name: "a removal from an empty list, on its way", expect: ['fails on: f([], true)'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.isEmpty() })
                        static boolean f(List<Integer> xs, boolean b) { b && xs.pop() > 0 }
                    }''')],
        [group: "P506 removals that may not run", name: "an arm's value, unboxed, as written", expect: ['xs.pop() is null for a null element', 'obligation: xs.pop() != null'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 })
                        static int f(List<Integer> xs, boolean b) { int t = b ? xs.pop() : 0; t }
                    }''')],

        // ---------- postconditions, by the way taken ----------
        [group: "P506 removals that may not run", name: "a size after &&, by the way taken", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] != null })
                        @Ensures({ xs.size() == (b ? 1 : 2) })
                        static void f(List<Integer> xs, boolean b) { boolean t = b && xs.pop() > 0 }
                    }''')],
        [group: "P506 removals that may not run", name: "… not either way", expect: ['Cannot prove postcondition', 'fails on: f([', ', false)'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] != null })
                        @Ensures({ xs.size() == 1 })
                        static void f(List<Integer> xs, boolean b) { boolean t = b && xs.pop() > 0 }
                    }''')],
        [group: "P506 removals that may not run", name: "&&'s value, returned", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == 5 })
                        @Ensures({ result == b && xs.size() == (b ? 1 : 2) })
                        static boolean f(List<Integer> xs, boolean b) { return b && xs.pop() > 0 }
                    }''')],
        [group: "P506 removals that may not run", name: "||'s value, returned", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == -5 })
                        @Ensures({ result == b && xs.size() == (b ? 2 : 1) })
                        static boolean f(List<Integer> xs, boolean b) { return b || xs.pop() > 0 }
                    }''')],
        [group: "P506 removals that may not run", name: "a ternary's value and size", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == 5 })
                        @Ensures({ result == (b ? 6 : 2) && xs.size() == (b ? 1 : 2) })
                        static int f(List<Integer> xs, boolean b) { (b ? xs.pop() : 0) + xs.size() }
                    }''')],
        [group: "P506 removals that may not run", name: "… a value read before it, kept", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == 5 && xs[1] == 7 })
                        @Ensures({ result == (b ? 10 : 5) })
                        static int f(List<Integer> xs, boolean b) { xs.get(0) + (b ? xs.pop() : 0) }
                    }''')],
        [group: "P506 removals that may not run", name: "… not the one after it", expect: ['Cannot prove postcondition', 'fails on: f([5, 7], true)'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == 5 && xs[1] == 7 })
                        @Ensures({ result == (b ? 12 : 5) })
                        static int f(List<Integer> xs, boolean b) { xs.get(0) + (b ? xs.pop() : 0) }
                    }''')],
        [group: "P506 removals that may not run", name: "an elvis's other arm", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == 5 && (n == null || n > 0) })
                        @Ensures({ result == (n == null ? 5 : n) && xs.size() == (n == null ? 1 : 2) })
                        static Integer f(List<Integer> xs, Integer n) { n ?: xs.pop() }
                    }''')],
        [group: "P506 removals that may not run", name: "a receiver's size after &&", ok: true,
         src: tc(client('''@Requires({ b != null && b.xs != null && b.xs.size() == 2 && b.xs[0] != null })
                        @Ensures({ b.xs.size() == (c ? 1 : 2) })
                        static void f(B b, boolean c) { boolean t = c && b.xs.pop() > 0 }'''))],

        // ---------- in a loop ----------
        [group: "P506 removals that may not run", name: "a removal under && in a loop's body", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 0 && 0 < xs.size()'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 && xs[0] != null })
                        static int f(List<Integer> xs, boolean b) { int s = 0; int i = 0; while (i < 1) { if (b && xs.pop() > 0) s = s + xs.get(0); i++ }; s }
                    }''')],
    ]
}
