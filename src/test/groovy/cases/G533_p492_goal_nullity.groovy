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
 * 'P492 goals read null' — a list's or a reference array's element compares as Groovy compares a null (below every
 * value, equal only to null) in a goal too, not only in an assumed @Requires (Phase 488): {@code xs[0] >= xs.min()}
 * proved, and is false on {@code [null, 3]}. The value models agree: {@code max}/{@code min} skip a null element,
 * {@code isSorted()} puts nulls first, {@code Sorted.ascending} throws on one, {@code contains} and {@code minus} match
 * a null only to a null, and an {@code every { int t -> … }} holds of none (its unboxing throws).
 */
class G533_p492_goal_nullity {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 492: an element compares as Groovy compares a null in a goal too — `xs[0] >= xs.min()` is refuted on `[null, 3]`, and max/min, isSorted, contains and minus treat a null element as Groovy does."

    static final List<Map> CASES = [

        // ---------- a goal's comparison ----------
        [group: "P492 goals read null", name: "a null element is below the minimum", expect: ['Cannot prove postcondition'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ xs[0] >= xs.min() })
                        static void f(List<Integer> xs) { }
                    }''')],
        [group: "P492 goals read null", name: "… none when every element isn't", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs.every { it != null } })
                        @Ensures({ xs[0] >= xs.min() })
                        static void f(List<Integer> xs) { }
                    }''')],

        // ---------- a callee's @Requires at its call (Phase 488's gap) ----------
        [group: "P492 goals read null", name: "a callee's precondition met with a null", expect: ['Cannot prove precondition of g'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.every { it >= 0 } })
                        static int g(List<Integer> xs) { xs.size() > 0 ? xs[0] + 1 : 0 }
                        @Requires({ ys != null && ys.size() > 0 && ys[0] == null })
                        static int f(List<Integer> ys) { g(ys) }
                    }''')],
        [group: "P492 goals read null", name: "… and with none", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.every { it >= 0 } })
                        static int g(List<Integer> xs) { xs.size() > 0 ? xs[0] + 1 : 0 }
                        @Requires({ ys != null && ys.every { it != null && it >= 0 } })
                        static int f(List<Integer> ys) { g(ys) }
                    }''')],

        // ---------- the value models ----------
        [group: "P492 goals read null", name: "a maximum skips a null", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == null && xs[1] == 3 })
                        @Ensures({ xs.max() == 3 })
                        static void f(List<Integer> xs) { }
                    }''')],
        [group: "P492 goals read null", name: "a null sorts first", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == null })
                        @Ensures({ xs.isSorted() })
                        static void f(List<Integer> xs) { }
                    }''')],
        [group: "P492 goals read null", name: "… and not last", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == 1 && xs[1] == null })
                        @Ensures({ !xs.isSorted() })
                        static void f(List<Integer> xs) { }
                    }''')],
        [group: "P492 goals read null", name: "a pairwise sortedness has none", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() >= 2 && Sorted.ascending(xs) })
                        @Ensures({ xs[1] != null })
                        static void f(List<Integer> xs) { }
                    }''')],
        [group: "P492 goals read null", name: "a null isn't an int's member", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 1 && xs[0] == null })
                        @Ensures({ !xs.contains(0) })
                        static void f(List<Integer> xs) { }
                    }''')],
        [group: "P492 goals read null", name: "… nor removed with one", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 1 && xs[0] == null })
                        @Ensures({ result.size() == 1 })
                        static List<Integer> f(List<Integer> xs, int n) { xs - n }
                    }''')],
        [group: "P492 goals read null", name: "an unboxing predicate holds of none", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.every { int t -> t < 0 } })
                        @Ensures({ xs.every { it != null } })
                        static void f(List<Integer> xs) { }
                    }''')],

        // ---------- what a stored value's nullity is ----------
        [group: "P492 goals read null", name: "a pure helper's value", ok: true,
         src: tc('''class A {
                        static Integer clip(int n) { n > 0 ? n : 0 }
                        @Ensures({ result[0] == clip(n) })
                        static Integer[] f(int n) { Integer[] r = new Integer[1]; r[0] = clip(n); r }
                    }''')],
        [group: "P492 goals read null", name: "a number's String", ok: true,
         src: tc('''class A {
                        @Ensures({ result[0] == n.toString() })
                        static String[] f(int n) { String[] r = new String[1]; r[0] = n.toString(); r }
                    }''')],
        [group: "P492 goals read null", name: "an index isn't null", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 2 && (0..<2).every { xs[it] == it } })
                        @Ensures({ xs[1] != null })
                        static void f(List<Integer> xs) { }
                    }''')],
        [group: "P492 goals read null", name: "an enum's constant", ok: true,
         src: tc('''class A {
                        enum Color { RED, BLUE }
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ xs[0] == Color.RED })
                        static void f(List<Color> xs) { xs[0] = Color.RED }
                    }''')],
    ]
}
