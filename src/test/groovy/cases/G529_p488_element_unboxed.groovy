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
 * 'P488 an element unboxed' — a list's or a boxed array's element ({@code xs[i]}, {@code xs.get(i)}, {@code a[i]}) may be
 * null, and where a boxed number's value is unboxed a null throws as a map's value does (Phase 486) — measured on Groovy
 * 6.0.0, @TypeChecked: an arithmetic operation's left operand or a negation ({@code NullPointerException}), its right
 * operand ({@code GroovyRuntimeException}; a {@code %}'s is a {@code NullPointerException}), a compound assignment's right
 * operand ({@code s += xs[0]}: {@code GroovyRuntimeException}; {@code %=}: {@code NullPointerException}; a String's takes
 * the null), a primitive's value ({@code GroovyCastException}). A parameter's or a field's element compares as Groovy
 * compares a null — below every number — so {@code xs.every { it >= 0 }} makes each non-null, and {@code it <= 9} doesn't.
 */
class G529_p488_element_unboxed {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 488: a list's or a boxed array's element unboxed where it's used — an arithmetic operand, a compound assignment's right side, a primitive's value — must not be null: `xs[0] + 1` on `[null]` throws, and is checked against the elements' nullity (`xs.every { it != null }`, `List<@NonNull Integer>`, or a comparison a null fails, `xs.every { it >= 0 }`)."

    static final List<Map> CASES = [

        // ---------- where a null element throws ----------
        [group: 'P488 an element unboxed', name: 'a left operand', expect: ["Possible NullPointerException: xs[0] is null for a null element, and a null operand throws", 'obligation: xs[0] != null', 'fails on: f([null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<Integer> xs) { xs[0] + 1 }
                    }''')],
        [group: 'P488 an element unboxed', name: '… a get', expect: ["Possible GroovyCastException: xs.get(0) is null for a null element, and a null can't be cast to int", 'fails on: f([null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<Integer> xs) { xs.get(0) }
                    }''')],
        [group: 'P488 an element unboxed', name: '… an Integer[]', expect: ["Possible NullPointerException: a[0] is null for a null element", 'fails on: f(new Integer[1])'],
         src: tc('''class A {
                        @Requires({ a != null && a.length > 0 })
                        static int f(Integer[] a) { a[0] * 2 }
                    }''')],
        [group: 'P488 an element unboxed', name: 'a right operand', expect: ["Possible GroovyRuntimeException: xs[0] is null for a null element", 'fails on: f([null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<Integer> xs) { 1 + xs[0] }
                    }''')],
        [group: 'P488 an element unboxed', name: "a compound assignment's right operand", expect: ["Possible GroovyRuntimeException: xs[0] is null for a null element", 'fails on: f([null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<Integer> xs) { int s = 1; s += xs[0]; s }
                    }''')],
        [group: 'P488 an element unboxed', name: '… a remainder', expect: ["Possible NullPointerException: xs[0] is null for a null element", 'fails on: f([null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] != 0 })
                        static int f(List<Integer> xs) { int s = 7; s %= xs[0]; s }
                    }''')],
        [group: 'P488 an element unboxed', name: "… a String's", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static String f(List<Integer> xs) { String s = 'a'; s += xs[0]; s }
                    }''')],
        [group: 'P488 an element unboxed', name: 'a negation', expect: ["Possible NullPointerException: xs[0] is null for a null element", 'fails on: f([null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static long f(List<Long> xs) { -xs[0] }
                    }''')],
        [group: 'P488 an element unboxed', name: "a primitive local's value", expect: ["Possible GroovyCastException: xs[1] is null for a null element, and a null can't be cast to int", 'fails on: f([null, null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 1 })
                        static int f(List<Integer> xs) { int v = xs[1]; v }
                    }''')],
        [group: 'P488 an element unboxed', name: 'an add before a read of an earlier element', expect: ["Possible GroovyCastException: xs[0] is null for a null element", 'fails on: f([null], 0)'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 1 })
                        static int f(List<Integer> xs, int v) { xs.add(v); xs[0] }
                    }''')],

        // ---------- an element the method knows ----------
        [group: 'P488 an element unboxed', name: 'every element stated non-null', ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs.every { it != null } })
                        static int f(List<Integer> xs) { int v = xs[0]; xs[0] + v * 2 }
                    }''')],
        [group: 'P488 an element unboxed', name: '… declared non-null', ok: true,
         src: HDR + NONNULL_TYPEUSE_ANN + tc('''class A {
                        @Requires({ xs.size() > 0 })
                        static int f(List<@NonNull Integer> xs) { xs[0] + 1 } }''')],
        [group: 'P488 an element unboxed', name: 'a comparison a null fails', ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs.every { it >= 0 } })
                        static int f(List<Integer> xs) { xs[0] + 1 }
                    }''')],
        [group: 'P488 an element unboxed', name: "… an index quantifier's", ok: true,
         src: tc('''class A {
                        @Requires({ a != null && a.length > 0 && (0..<a.length).every { a[it] > 0 } })
                        static int f(Integer[] a) { a[0] - 1 }
                    }''')],
        [group: 'P488 an element unboxed', name: '… one it meets', expect: ["Possible NullPointerException: xs[0] is null for a null element", 'fails on: f([null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs.every { it <= 9 } })
                        static int f(List<Integer> xs) { xs[0] + 1 }
                    }''')],
        [group: 'P488 an element unboxed', name: '… on its right', ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && 3 < xs[0] })
                        static int f(List<Integer> xs) { xs[0] + 1 }
                    }''')],
        [group: 'P488 an element unboxed', name: 'a guard', ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<Integer> xs) { xs[0] != null ? xs[0] + 1 : 0 }
                    }''')],
        [group: 'P488 an element unboxed', name: "a literal's elements", ok: true,
         src: tc('''class A {
                        static int f() { List<Integer> xs = [1, 2]; xs[0] + xs[1] }
                    }''')],
        [group: 'P488 an element unboxed', name: "a primitive's add", ok: true,
         src: tc('''class A {
                        static int f(int n) { List<Integer> xs = []; xs.add(n); xs[0] + 1 }
                    }''')],
        [group: 'P488 an element unboxed', name: "an int[]'s element", ok: true,
         src: tc('''class A {
                        @Requires({ a != null && a.length > 0 })
                        static int f(int[] a) { a[0] + 1 }
                    }''')],
        [group: 'P488 an element unboxed', name: 'a caught exception', ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<Integer> xs) { try { return xs[0] + 1 } catch (NullPointerException e) { return 0 } }
                    }''')],
        [group: 'P488 an element unboxed', name: "a findAll's a null fails", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        static int f(List<Integer> xs) { List<Integer> ps = xs.findAll { it > 0 }; ps.size() > 0 ? ps[0] + 1 : 0 }
                    }''')],
        [group: 'P488 an element unboxed', name: "… a predicate a null meets", expect: ["Possible NullPointerException: ps[0] is null for a null element", 'fails on: f([null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() < 2 })
                        static int f(List<Integer> xs) { List<Integer> ps = xs.findAll { it < 5 }; ps.size() > 0 ? ps[0] + 1 : 0 }
                    }''')],
        [group: 'P488 an element unboxed', name: "a fill's value", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<Integer> xs) { Collections.fill(xs, 9); xs[0] + 1 }
                    }''')],
        [group: 'P488 an element unboxed', name: "… one that may be null", expect: ["Possible NullPointerException: xs[0] is null for a null element"],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<Integer> xs, Integer v) { Collections.fill(xs, v); xs[0] + 1 }
                    }''')],
        [group: 'P488 an element unboxed', name: "a sort's of two or more", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 1 })
                        static int f(List<Integer> xs) { Collections.sort(xs); xs[0] + xs[1] }
                    }''')],
        [group: 'P488 an element unboxed', name: "… of one", expect: ["Possible NullPointerException: xs[0] is null for a null element"],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<Integer> xs) { Collections.sort(xs); xs[0] + 1 }
                    }''')],
        [group: 'P488 an element unboxed', name: "the last element", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs[xs.size() - 1] != null })
                        static int f(List<Integer> xs) { xs[-1] + 1 }
                    }''')],

        // ---------- where a null is harmless ----------
        [group: 'P488 an element unboxed', name: 'an Elvis', ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<Integer> xs) { (xs[0] ?: 0) + 1 }
                    }''')],
        [group: 'P488 an element unboxed', name: 'a comparison', ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static boolean f(List<Integer> xs) { xs[0] < 3 }
                    }''')],
        [group: 'P488 an element unboxed', name: 'a boxed result', ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static Integer f(List<Integer> xs) { xs[0] }
                    }''')],
    ]
}
