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
 * 'P490 list building keeps nullity' — a list built from others (a concatenation {@code [x] + xs} or {@code xs + n}, a
 * spread literal {@code [x, *xs]}, a repeat {@code xs * 2}, a {@code drop(k)}) has each element's nullity from the one
 * it copies, or from the value put in ({@code [x]} with an {@code int x} isn't null); they were fresh, so its element
 * unboxed (Phase 488) was reported however its source was stated. And {@code xs << v} as a statement is
 * {@code xs.add(v)} (Phase 341's reading in a body and a loop): before an obligation it havocked the list, so
 * {@code ys << 'ab'; ys[0].size()} failed its bounds. Measured on Groovy 6.0.0: each copies its source's nulls.
 */
class G531_p490_list_building_nullity {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 490: a list built by `+`, a spread literal, `* k` or `drop(k)` keeps each element's nullity from what it copies (`[x] + xs` with an `int x` has a non-null head; `xs.drop(1)` of a list stated non-null has none), and `xs << v` as a statement appends `v` rather than forgetting the list."

    static final List<Map> CASES = [

        // ---------- a concatenation ----------
        [group: 'P490 list building keeps nullity', name: "a concatenation's head", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        static int f(int x, List<Integer> xs) { List<Integer> ys = [x] + xs; ys[0] + 1 }
                    }''')],
        [group: 'P490 list building keeps nullity', name: "… its tail of a list stated non-null", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs.every { it != null } })
                        static int f(int x, List<Integer> xs) { List<Integer> ys = [x] + xs; ys[1] + 1 }
                    }''')],
        [group: 'P490 list building keeps nullity', name: "… of one that isn't", expect: ["Possible NullPointerException: ys[1] is null for a null element", ', [null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 1 })
                        static int f(int x, List<Integer> xs) { List<Integer> ys = [x] + xs; ys[1] + 1 }
                    }''')],
        [group: 'P490 list building keeps nullity', name: "an appended element", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        static int f(int x, List<Integer> xs) { List<Integer> ys = xs + x; ys[ys.size() - 1] + 1 }
                    }''')],
        [group: 'P490 list building keeps nullity', name: "… a boxed one", expect: ["Possible NullPointerException: ys[0] is null for a null element", 'fails on: f(null, [])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 0 })
                        static int f(Integer x, List<Integer> xs) { List<Integer> ys = xs + [x]; ys[0] + 1 }
                    }''')],
        [group: 'P490 list building keeps nullity', name: "a spread literal's", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.every { it != null } })
                        static int f(int x, List<Integer> xs) { List<Integer> ys = [x, *xs, x]; ys[0] + ys[xs.size()] + ys[ys.size() - 1] }
                    }''')],
        [group: 'P490 list building keeps nullity', name: "a repeat's second copy", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs.every { it != null } })
                        static int f(List<Integer> xs) { List<Integer> ys = xs * 2; ys[xs.size()] + 1 }
                    }''')],
        [group: 'P490 list building keeps nullity', name: "a drop's", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 1 && xs.every { it != null } })
                        static int f(List<Integer> xs) { List<Integer> ys = xs.drop(1); ys[0] + 1 }
                    }''')],
        [group: 'P490 list building keeps nullity', name: "… of a list that isn't", expect: ["Possible NullPointerException: ys[0] is null for a null element", ', null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] != null })
                        static int f(List<Integer> xs) { List<Integer> ys = xs.drop(1); ys[0] + 1 }
                    }''')],
        [group: 'P490 list building keeps nullity', name: "… of one element stated", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 2 && xs[1] != null })
                        static int f(List<Integer> xs) { List<Integer> ys = xs.drop(1); ys[0] + 1 }
                    }''')],
        [group: 'P490 list building keeps nullity', name: "a removal's", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.every { it != null } })
                        static int f(List<Integer> xs) { List<Integer> ys = xs - 5; ys.size() > 0 ? ys[0] + 1 : 0 }
                    }''')],

        // ---------- a left shift ----------
        [group: 'P490 list building keeps nullity', name: "a shifted element", ok: true,
         src: tc('''class A {
                        static int f(int n) { List<Integer> ys = []; ys << n; ys[0] + 1 }
                    }''')],
        [group: 'P490 list building keeps nullity', name: "… a boxed one", expect: ["Possible NullPointerException: ys[0] is null for a null element", 'fails on: f(null)'],
         src: tc('''class A {
                        static int f(Integer n) { List<Integer> ys = []; ys << n; ys[0] + 1 }
                    }''')],
        [group: 'P490 list building keeps nullity', name: "a chain's", ok: true,
         src: tc('''class A {
                        static int f(int a, int b) { List<Integer> ys = []; ys << a << b; ys[1] - ys[0] }
                    }''')],
        [group: 'P490 list building keeps nullity', name: "a shifted String's bounds", ok: true,
         src: tc('''class A {
                        static int f() { List<String> ys = []; ys << 'ab'; ys[0].size() }
                    }''')],
        [group: 'P490 list building keeps nullity', name: "… past its end", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 1 && 1 < ys.size()'],
         src: tc('''class A {
                        static int f() { List<String> ys = []; ys << 'ab'; ys[1].size() }
                    }''')],
    ]
}
