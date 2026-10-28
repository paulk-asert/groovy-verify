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
 * 'P458 elements removed from a list' — `xs - n` (an int) and `xs - ys` (`List.minus`) take out every occurrence and
 * keep the rest in order; nothing modelled them, so they were a loud skip. The result is a fresh list whose elements
 * are the source's, none of them removed, and whose size is the source's exactly when nothing was removed. Which kept
 * element lands where isn't modelled.
 */
class G499_p458_list_minus {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 458: elements removed from a list with `-` (`xs - n` for an int `n`, `xs - ys` for an Int list) are modelled — every element is one of the source's and none is removed; the size never grows, stays put exactly when nothing is removed, and drops when something is — where it was a loud skip."

    static final List<Map> CASES = [

        // ---------- xs - n ----------
        [group: "P458 elements removed from a list", name: "removing an int leaves none of it", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        @Ensures({ result != null && !result.contains(n) })
                        static List<Integer> f(List<Integer> xs, int n) { xs - n }
                    }''')],

        [group: "P458 elements removed from a list", name: "… never grows the list", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        @Ensures({ result.size() <= xs.size() })
                        static List<Integer> f(List<Integer> xs, int n) { xs - n }
                    }''')],

        [group: "P458 elements removed from a list", name: "… keeps the size when it's absent", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && !xs.contains(n) })
                        @Ensures({ result.size() == xs.size() })
                        static List<Integer> f(List<Integer> xs, int n) { xs - n }
                    }''')],

        [group: "P458 elements removed from a list", name: "… shrinks the list when it's there", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.contains(n) })
                        @Ensures({ result.size() < xs.size() })
                        static List<Integer> f(List<Integer> xs, int n) { xs - n }
                    }''')],

        [group: "P458 elements removed from a list", name: "… keeps only the list's own elements", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.every { int t -> t > 0 } })
                        @Ensures({ result.every { int t -> t > 0 } })
                        static List<Integer> f(List<Integer> xs, int n) {
                            List<Integer> ys = xs - n
                            return ys
                        }
                    }''')],

        // every occurrence goes, not just one
        [group: "P458 elements removed from a list", name: "… may remove more than one", expect: 'Cannot prove postcondition',
         src: tc('''class A {
                        @Requires({ xs != null && xs.contains(n) })
                        @Ensures({ result.size() == xs.size() - 1 })
                        static List<Integer> f(List<Integer> xs, int n) { xs - n }
                    }''')],

        [group: "P458 elements removed from a list", name: "… may leave the list empty", expect: 'Cannot prove postcondition',
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result.size() > 0 })
                        static List<Integer> f(List<Integer> xs, int n) { xs - n }
                    }''')],

        [group: "P458 elements removed from a list", name: "a recursion removing its element", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result != null && result.size() <= n })
                        @Decreases({ n })
                        static List<Integer> f(int n) { n == 0 ? [] : f(n - 1) - n }
                    }''')],

        [group: "P458 elements removed from a list", name: "removing an element gives a callee a list it accepts", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() <= 10 })
                        static int f(List<Integer> xs, int n) { g(xs - n) }
                        @Requires({ ys != null && ys.size() <= 10 })
                        static int g(List<Integer> ys) { 0 }
                    }''')],

        // ---------- xs - ys ----------
        [group: "P458 elements removed from a list", name: "removing a list leaves none of its elements", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && ys != null })
                        @Ensures({ result.every { int t -> !ys.contains(t) } })
                        static List<Integer> f(List<Integer> xs, List<Integer> ys) { xs - ys }
                    }''')],

        [group: "P458 elements removed from a list", name: "a list minus itself is empty", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        @Ensures({ result.isEmpty() })
                        static List<Integer> f(List<Integer> xs) { xs - xs }
                    }''')],

        [group: "P458 elements removed from a list", name: "removing a disjoint list keeps the size", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && ys != null && xs.every { int t -> t > 0 } && ys.every { int t -> t < 0 } })
                        @Ensures({ result.size() == xs.size() })
                        static List<Integer> f(List<Integer> xs, List<Integer> ys) { xs - ys }
                    }''')],

        [group: "P458 elements removed from a list", name: "removing a list that shares an element shrinks it", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && ys != null && xs.size() > 0 && ys.contains(xs[0]) })
                        @Ensures({ result.size() < xs.size() })
                        static List<Integer> f(List<Integer> xs, List<Integer> ys) { xs - ys }
                    }''')],

        [group: "P458 elements removed from a list", name: "removing a list may empty it", expect: 'Cannot prove postcondition',
         src: tc('''class A {
                        @Requires({ xs != null && ys != null && xs.size() > ys.size() })
                        @Ensures({ result.size() > 0 })
                        static List<Integer> f(List<Integer> xs, List<Integer> ys) { xs - ys }
                    }''')],

        // ---------- not modelled ----------
        // `n - xs` isn't a list operator; an Integer n may be null, which removes the list's nulls instead
        [group: "P458 elements removed from a list", name: "an Integer removed is still a skip", expect: 'outside fragment',
         src: tc('''class A {
                        @Requires({ xs != null })
                        @Ensures({ result.size() <= xs.size() })
                        static List<Integer> f(List<Integer> xs, Integer n) { xs - n }
                    }''')],

        [group: "P458 elements removed from a list", name: "an int's - is still subtraction", ok: true,
         src: tc('''class A {
                        @Ensures({ result == a - b })
                        static int f(int a, int b) { a - b }
                    }''')],
    ]
}
