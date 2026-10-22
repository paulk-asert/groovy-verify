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
 * 'P377 list alias' — Phase 375 made a re-assigned list share an alias's size only while neither is written into,
 * and counted every call argument as a write: `List<Integer> v = xs` before a loop calling `v = grow(v)` lost `v`'s
 * size at the alias, so the loop invariant failed on entry. A call argument now counts as written only when the
 * callee's frame writes that formal (any other call's argument still counts). And `new ArrayList()` / `new
 * LinkedList()` (or with a capacity) is an empty list, `new ArrayList(xs)` a copy of `xs` — they were unmodelled.
 */
class G421_p377_list_alias {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 377: a list alias keeps its source\'s size and contents unless one is written into (a call argument by its callee\'s frame), and `new ArrayList()` / `new LinkedList()` / with a capacity are empty lists, `new ArrayList(xs)` a copy of `xs`.'

    static final String LGROW = '''
                        @Requires({ a != null })
                        @Ensures({ result != null && result.size() == a.size() + 1 })
                        static List<Integer> grow(List<Integer> a) { List<Integer> r = []; r.addAll(a); r.add(0); r }'''

    static final String GROW_SKIP = 'Skipped verification of postcondition for grow'

    static final List<Map> CASES = [

        // Before: `Cannot prove loop invariant holds on entry` (v's size unrelated to xs's).
        [group: "P377 list alias", name: "a local alias before a loop",
         expect: GROW_SKIP, refute: ["Cannot prove", "Could not decide"],
         src: tc("""class A {${LGROW}
                        @Requires({ n >= 1 && xs != null })
                        @Ensures({ result == xs.size() + n })
                        static int f(int n, List<Integer> xs) {
                            List<Integer> v = xs
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && v != null && v.size() == xs.size() + i })
                            @Decreases({ n - i })
                            while (i < n) {
                                v = grow(v)
                                i = i + 1
                            }
                            v.size()
                        }
                    }""")],

        // Before: refuted at the entry, where it holds. Now where it is false: the loop body.
        [group: "P377 list alias", name: "… a false invariant over it",
         expect: "Cannot prove loop invariant is preserved by the loop body in f", refute: "holds on entry",
         src: tc("""class A {${LGROW}
                        @Requires({ n >= 1 && xs != null })
                        static int f(int n, List<Integer> xs) {
                            List<Integer> v = xs
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && v != null && v.size() == xs.size() })
                            @Decreases({ n - i })
                            while (i < n) {
                                v = grow(v)
                                i = i + 1
                            }
                            v.size()
                        }
                    }""")],

        // Before: `Cannot prove loop invariant holds on entry` (new ArrayList() unmodelled).
        [group: "P377 list alias", name: "a new ArrayList before a loop",
         expect: GROW_SKIP, refute: ["Cannot prove", "Could not decide"],
         src: tc("""class A {${LGROW}
                        @Requires({ n >= 1 })
                        @Ensures({ result == n })
                        static int f(int n) {
                            List<Integer> v = new ArrayList<Integer>()
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && v != null && v.size() == i })
                            @Decreases({ n - i })
                            while (i < n) {
                                v = grow(v)
                                i = i + 1
                            }
                            v.size()
                        }
                    }""")],

        // Before: skipped (the constructor was outside the fragment).
        [group: "P377 list alias", name: "an ArrayList with a capacity is empty",
         ok: true,
         src: tc('''class A {
                        @Requires({ k >= 0 })
                        @Ensures({ result == 0 })
                        static int f(int k) {
                            List<Integer> v = new ArrayList<Integer>(k)
                            v.size()
                        }
                    }''')],

        // Before: skipped. A copy is its own object: the source's later add doesn't reach it.
        [group: "P377 list alias", name: "a copy keeps its size when the source grows",
         ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 2 })
                        @Ensures({ result == 2 })
                        static int f(List<Integer> xs) {
                            List<Integer> v = new ArrayList<Integer>(xs)
                            xs.add(1)
                            v.size()
                        }
                    }''')],

        // Before: skipped.
        [group: "P377 list alias", name: "… so it isn't the source's new size",
         expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Requires({ xs != null })
                        @Ensures({ result == xs.size() })
                        static int f(List<Integer> xs) {
                            List<Integer> v = new ArrayList<Integer>(xs)
                            xs.add(1)
                            v.size()
                        }
                    }''')],

        // An alias whose source is written into: still Phase 366's loud skip.
        [group: "P377 list alias", name: "an alias whose source is added to",
         expect: "makes 'v' share its contents with 'xs', and 'xs' is written",
         src: tc('''class A {
                        @Requires({ n >= 1 && xs != null })
                        static int f(int n, List<Integer> xs) {
                            List<Integer> v = xs
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && v != null })
                            @Decreases({ n - i })
                            while (i < n) {
                                xs.add(i)
                                i = i + 1
                            }
                            v.size()
                        }
                    }''')],
    ]
}
