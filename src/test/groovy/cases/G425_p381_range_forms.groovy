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
 * 'P381 range forms' — Groovy has four range forms (`a..b`, `a..<b`, `a<..b`, `a<..<b`), and iterates one whose end is
 * below its start downwards (`5..0` is 5..0, `0..<-1` is [0], `2<..<0` is [1]). Quantifiers, slices, constant ranges
 * as lists and Phase 380's closure ranges read every range as ascending from `from`: a descending one was empty (or, as
 * Phase 380's closure fact, a contradiction, so its sites proved vacuously) and `<..` kept its start. They now read
 * the ints the range iterates, and a refutation whose model runs a range backwards says so. A non-integral range
 * (`4.5..6.5`, a NumberRange stepping by one from 4.5) is outside the fragment.
 */
class G425_p381_range_forms {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 381: a range is read as the ints Groovy iterates — either direction, either end excluded — in quantifiers, slices, constant ranges as lists and closure ranges; a refutation running a range backwards says so."

    static final String BACKWARDS = 'runs backwards here'

    static final List<Map> CASES = [

        // Before: compiled cleanly — `2..0` was read as empty, so nothing was checked.
        [group: "P381 range forms", name: "a descending quantifier as an obligation",
         expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Requires({ a != null && a.length == 3 })
                        @Ensures({ (2..0).every { a[it] > 0 } })
                        static void f(int[] a) { a[0] = 0 }
                    }''')],

        [group: "P381 range forms", name: "… which proves when it holds",
         ok: true,
         src: tc('''class A {
                        @Requires({ a != null && a.length == 3 })
                        @Ensures({ (2..0).every { a[it] == 7 } })
                        static void f(int[] a) { a[0] = 7; a[1] = 7; a[2] = 7 }
                    }''')],

        // Before: compiled cleanly — a symbolic end below the start.
        [group: "P381 range forms", name: "a symbolic descending quantifier",
         expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Requires({ a != null && n >= 1 && n < a.length })
                        @Ensures({ (n..0).every { a[it] == 1 } })
                        static void f(int[] a, int n) { a[0] = 1 }
                    }''')],

        // Before: compiled cleanly — `0<..<3` was assumed of index 0 too.
        [group: "P381 range forms", name: "an exclusive start assumes nothing of it",
         expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Requires({ a != null && a.length == 3 && (0<..<3).every { a[it] > 0 } })
                        @Ensures({ result > 0 })
                        static int f(int[] a) { a[0] }
                    }''')],

        [group: "P381 range forms", name: "… and what it covers, it gives",
         ok: true,
         src: tc('''class A {
                        @Requires({ a != null && a.length == 3 && (0<..<3).every { a[it] > 0 } })
                        @Ensures({ result > 0 })
                        static int f(int[] a) { a[1] }
                    }''')],

        // Before: compiled cleanly — the slice's sum counted a[0].
        [group: "P381 range forms", name: "a slice with an exclusive start",
         expect: "postcondition of f",
         src: tc('''class A {
                        @Requires({ a != null && a.length == 3 && a[0] == 5 && a[1] == 1 && a[2] == 1 })
                        @Ensures({ a[0<..2].sum(0) == 7 })
                        static void f(int[] a) { }
                    }''')],

        // Before: undecided.
        [group: "P381 range forms", name: "… summing what it takes",
         ok: true,
         src: tc('''class A {
                        @Requires({ a != null && a.length == 3 && a[0] == 5 && a[1] == 1 && a[2] == 1 })
                        @Ensures({ a[0<..2].sum(0) == 2 })
                        static void f(int[] a) { }
                    }''')],

        // Before: compiled cleanly — `a[2..0]` (the reversed sublist) was read as empty.
        [group: "P381 range forms", name: "a descending slice isn't empty",
         expect: "postcondition of f",
         src: tc('''class A {
                        @Requires({ a != null && a.length == 3 && a[0] == 5 && a[1] == 1 && a[2] == 1 })
                        @Ensures({ a[2..0].sum(0) == 0 })
                        static void f(int[] a) { }
                    }''')],

        // Before: undecided.
        [group: "P381 range forms", name: "… it sums the same elements",
         ok: true,
         src: tc('''class A {
                        @Requires({ a != null && a.length == 3 && a[0] == 5 && a[1] == 1 && a[2] == 1 })
                        @Ensures({ a[2..0].sum(0) == 7 })
                        static void f(int[] a) { }
                    }''')],

        // Before: compiled cleanly — `5..0` as a list had size 0.
        [group: "P381 range forms", name: "a descending range as a list",
         expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Ensures({ result == 0 })
                        static int f() {
                            List<Integer> r = 5..0
                            r.size()
                        }
                    }''')],

        // Before: refuted, falsely.
        [group: "P381 range forms", name: "… has its six elements",
         ok: true,
         src: tc('''class A {
                        @Ensures({ result == 6 })
                        static int f() {
                            List<Integer> r = 5..0
                            r.size()
                        }
                    }''')],

        // Before: compiled cleanly — `(0<..3).toList()` began at 0.
        [group: "P381 range forms", name: "an exclusive start as a list",
         expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Ensures({ result == 0 })
                        static int f() {
                            List<Integer> r = (0<..3).toList()
                            r[0]
                        }
                    }''')],

        // Before (Phase 380, 582dd3a): compiled cleanly — the closure's range fact `5 <= it <= 0` was a contradiction.
        [group: "P381 range forms", name: "a closure over a descending range",
         expect: ["Possible IndexOutOfBoundsException", "it = 3, j.length = 3"],
         src: tc('''class A {
                        @Requires({ j != null && j.length == 3 })
                        static boolean f(int[] j) { (5..0).every { j[it] >= 0 } }
                    }''')],

        // Before: warned (`it` free).
        [group: "P381 range forms", name: "closures over descending and exclusive ranges in bounds",
         ok: true,
         src: tc('''class A {
                        @Requires({ j != null && j.length > 2 })
                        static boolean f(int[] j) {
                            ((j.length - 1)..0).every { j[it] >= 0 } && (-1<..<j.length).every { j[it] >= 0 } &&
                                (j.length<..<0).every { j[it] >= 0 }
                        }
                    }''')],

        // `4.5..6.5` is Groovy's NumberRange [4.5, 5.5, 6.5], not ints: outside the fragment, said so. Before (the
        // working tree's first cut of this phase): its 4.5 truncated to 4, so `every { it > 4 }` over it was refuted.
        [group: "P381 range forms", name: "a decimal range is outside the fragment",
         expect: "is outside fragment", refute: ["Cannot prove", "Could not decide"],
         src: tc('''class A {
                        @Ensures({ (4.5..6.5).every { it > 4 } })
                        static void f() { }
                    }''')],

        // … and is never assumed as ints: assumed so, `4 > 4` was a contradiction and anything after it proved.
        [group: "P381 range forms", name: "… nor assumed as ints",
         expect: "is outside fragment", refute: "Cannot prove",
         src: tc('''class A {
                        @Requires({ a != null && a.length == 10 && (4.5..6.5).every { it > 4 } })
                        @Ensures({ result == 0 })
                        static int f(int[] a) { 1 }
                    }''')],

        // A long range is an int range.
        [group: "P381 range forms", name: "a long range is iterated as its ints",
         expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Requires({ a != null && a.length == 4 })
                        @Ensures({ (1L..3L).every { a[(int) it] == 0 } })
                        static void f(int[] a) { a[1] = 0; a[2] = 0 }
                    }''')],

        // A sortedness spec over a possibly-empty array: `0..<-1` is [0], so it reads a[0] — the refutation says why.
        [group: "P381 range forms", name: "a refutation that runs a range backwards says so",
         expect: ["Cannot prove postcondition of f", "a.length = 0", "note: the range (0..<(a.length - 1)) " + BACKWARDS],
         src: tc('''class A {
                        @Requires({ a != null && a.length <= 1 })
                        @Ensures({ (0..<a.length - 1).every { a[it] <= a[it + 1] } })
                        static void f(int[] a) { }
                    }''')],

        // … guarded against the empty array, it proves (as the corpus's sortedness specs now are).
        [group: "P381 range forms", name: "… and guarded for the empty array, proves",
         ok: true,
         src: tc('''class A {
                        @Requires({ a != null && a.length <= 1 })
                        @Ensures({ a.length == 0 || (0..<a.length - 1).every { a[it] <= a[it + 1] } })
                        static void f(int[] a) { }
                    }''')],
    ]
}
