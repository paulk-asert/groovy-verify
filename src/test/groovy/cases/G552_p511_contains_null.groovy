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
 * 'P511 contains null' — {@code xs.contains(null)} is true when some element is null, by the elements' null flags, so
 * {@code @Requires({ !xs.contains(null) })} states each non-null, as {@code xs.every { it != null }} does. It was
 * outside the fragment: the precondition was dropped (a false alarm on {@code xs[1] + 1}) or the postcondition skipped.
 * And a loop's stable precondition dropped any conjunct's negation ({@code !(s != null)} was assumed as
 * {@code s != null}), so a for-in body's {@code s.length()} compiled cleanly where it throws.
 */
class G552_p511_contains_null {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 511: `!xs.contains(null)` states each element non-null (`xs[i].length()`, a for-in's `x`), and a loop's precondition keeps a conjunct's negation."

    static String client(String method) { """final class B { List<Integer> xs }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        ${method}
                    }""" }

    static final List<Map> CASES = [

        // ---------- non-null by !xs.contains(null) ----------
        [group: "P511 contains null", name: "an element unboxed", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && !xs.contains(null) })
                        static int f(List<Integer> xs) { xs[1] + 1 }
                    }''')],
        [group: "P511 contains null", name: "… a call on one", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && !xs.contains(null) })
                        static int f(List<Integer> xs) { xs[1].intValue() }
                    }''')],
        [group: "P511 contains null", name: "… a String's", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && !xs.contains(null) })
                        static int f(List<String> xs) { xs[1].length() }
                    }''')],
        [group: "P511 contains null", name: "… by an index", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && i >= 0 && i < xs.size() && !xs.contains(null) })
                        static int f(List<Integer> xs, int i) { xs[i] + 1 }
                    }''')],
        [group: "P511 contains null", name: "… a receiver's", ok: true,
         src: tc(client('''@Requires({ b != null && b.xs != null && b.xs.size() == 2 && !b.xs.contains(null) })
                        static int f(B b) { b.xs[1] + 1 }'''))],
        [group: "P511 contains null", name: "… an array's", ok: true,
         src: tc('''class C {
                        @Requires({ a != null && a.length == 2 && !a.contains(null) })
                        static int f(String[] a) { a[1].length() }
                    }''')],
        [group: "P511 contains null", name: "… a local read from one", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 && !xs.contains(null) })
                        static int f(List<Integer> xs) { Integer v = xs[0]; v.intValue() }
                    }''')],
        [group: "P511 contains null", name: "… a for-in's element, a call on it", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && !xs.contains(null) })
                        static int f(List<Integer> xs) { int s = 0; for (Integer x : xs) { s = s + x.intValue() }; s }
                    }''')],
        [group: "P511 contains null", name: "… unboxed", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && !xs.contains(null) })
                        static int f(List<Integer> xs) { int s = 0; for (Integer x : xs) { s = s + x }; s }
                    }''')],
        [group: "P511 contains null", name: "a postcondition kept after an add", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && !xs.contains(null) })
                        @Ensures({ !xs.contains(null) })
                        static void f(List<Integer> xs) { xs.add(5) }
                    }''')],
        [group: "P511 contains null", name: "… and after a write", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && !xs.contains(null) })
                        @Ensures({ !xs.contains(null) })
                        static void f(List<Integer> xs) { xs[0] = 7 }
                    }''')],

        // ---------- still reported ----------
        [group: "P511 contains null", name: "contains(null), not its negation", expect: ['Possible NullPointerException', 'obligation: xs[1] != null', 'fails on: f([null, null])'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs.contains(null) })
                        static int f(List<Integer> xs) { xs[1] + 1 }
                    }''')],
        [group: "P511 contains null", name: "another list's element", expect: ['Possible NullPointerException', 'obligation: ys[0] != null', 'fails on: f([], [null])'],
         src: tc('''class C {
                        @Requires({ xs != null && ys != null && ys.size() == 1 && !xs.contains(null) })
                        static int f(List<Integer> xs, List<Integer> ys) { ys[0] + 1 }
                    }''')],
        [group: "P511 contains null", name: "a postcondition not from the precondition", expect: ['Cannot prove postcondition', 'fails on: f([null])'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 })
                        @Ensures({ !xs.contains(null) })
                        static void f(List<Integer> xs) { xs.add(5) }
                    }''')],

        // ---------- a loop's precondition, negated ----------
        [group: "P511 contains null", name: "a negated conjunct in a loop's precondition, kept", expect: ['Possible NullPointerException', 'obligation: s != null'],
         src: tc('''class C {
                        @Requires({ xs != null && !(s != null) })
                        static int f(List<Integer> xs, String s) { int t = 0; for (Integer x : xs) { t = t + s.length() }; t }
                    }''')],
        [group: "P511 contains null", name: "… an element's", expect: ['Possible NullPointerException', 'obligation: x != null'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 && !(xs[0] != null) })
                        static int f(List<Integer> xs) { int t = 0; for (Integer x : xs) { t = t + x.intValue() }; t }
                    }''')],
        [group: "P511 contains null", name: "… proving non-null", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && !(s == null) })
                        static int f(List<Integer> xs, String s) { int t = 0; for (Integer x : xs) { t = t + s.length() }; t }
                    }''')],

        // ---------- guards ----------
        [group: "P511 contains null", name: "an int array's, never null, not vacuous", expect: ['Cannot prove postcondition', 'fails on: f(['],
         src: tc('''class C {
                        @Requires({ a != null && a.length == 1 && !a.contains(null) })
                        @Ensures({ result == 1 })
                        static int f(int[] a) { a[0] }
                    }''')],
        [group: "P511 contains null", name: "every element stated non-null by every", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && !xs.isEmpty() && xs.every { it != null } })
                        static int f(List<Integer> xs) { int s = 0; for (Integer x : xs) { s = s + x.intValue() }; s }
                    }''')],
        [group: "P511 contains null", name: "a negated conjunct in a while loop's precondition", expect: ['Possible NullPointerException', 'fails on: f(null)'],
         src: tc('''class C {
                        @Requires({ !(s != null) })
                        static int f(String s) { int t = 0; int i = 0; while (i < 3) { t = t + s.length(); i++ }; t }
                    }''')],
    ]
}
