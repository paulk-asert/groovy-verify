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
 * 'P380 closure range' — a site inside a closure that iterates a range was checked with the closure's parameter free:
 * `boolean all = (0..<j.length).every { j[it] >= 0 }` warned `index may be out of bounds` with `it = -1`, and so did
 * `j.indices.any`, `n.times`, `upto`, `downto` and `collect` over a range. The parameter now satisfies its range there.
 */
class G424_p380_closure_range {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 380: a closure iterating a range (lo..<hi / lo..hi with every, any, each, collect, findAll, find, count, sum; a.indices; n.times; a.upto(b); a.downto(b)) has its parameter in that range at the sites inside it."

    static final String OOB = 'Possible IndexOutOfBoundsException'

    static final List<Map> CASES = [

        // Before: `Possible IndexOutOfBoundsException`, `it = -1`.
        [group: "P380 closure range", name: "an every over the indices",
         ok: true,
         src: tc('''class A {
                        @Requires({ j != null })
                        static boolean f(int[] j) {
                            boolean all = (0..<j.length).every { j[it] >= 0 }
                            all
                        }
                    }''')],

        // An inclusive range one past the end still warns (now with its real counterexample, `it = 0`, not `-1`).
        [group: "P380 closure range", name: "… one past the end still warns",
         expect: OOB,
         src: tc('''class A {
                        @Requires({ j != null })
                        static boolean f(int[] j) {
                            boolean all = (0..j.length).every { j[it] >= 0 }
                            all
                        }
                    }''')],

        // Before: warned.
        [group: "P380 closure range", name: "an array's indices",
         ok: true,
         src: tc('''class A {
                        @Requires({ j != null })
                        static boolean f(int[] j) { j.indices.any { k -> j[k] == 3 } }
                    }''')],

        // Before: warned.
        [group: "P380 closure range", name: "a list's indices",
         ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        static boolean f(List<Integer> xs) { xs.indices.any { int k -> xs[k] == 3 } }
                    }''')],

        // Before: warned.
        [group: "P380 closure range", name: "times",
         ok: true,
         src: tc('''class A {
                        @Requires({ j != null })
                        static int f(int[] j) {
                            int s = 0
                            j.length.times { k -> s += j[k] }
                            s
                        }
                    }''')],

        // `k + 1` reaches past the end.
        [group: "P380 closure range", name: "… one past it still warns",
         expect: OOB,
         src: tc('''class A {
                        @Requires({ j != null })
                        static int f(int[] j) {
                            int s = 0
                            j.length.times { k -> s += j[k + 1] }
                            s
                        }
                    }''')],

        // Before: warned. An inner closure over values keeps the outer index's range.
        [group: "P380 closure range", name: "a nested closure keeps the outer range",
         ok: true,
         src: tc('''class A {
                        @Requires({ j != null })
                        static boolean f(int[] j) {
                            (0..<j.length).every { i -> [1, 2].every { v -> j[i] >= v } }
                        }
                    }''')],

        // The inner closure's implicit `it` is its own, over 0..<5: not the outer index.
        [group: "P380 closure range", name: "… and an inner `it` shadows it",
         expect: OOB,
         src: tc('''class A {
                        @Requires({ j != null && j.length > 0 })
                        static boolean f(int[] j) {
                            (0..<j.length).every { (0..<5).every { j[it] >= 0 } }
                        }
                    }''')],

        // Before: `Possible ArithmeticException` (k free).
        [group: "P380 closure range", name: "upto and downto",
         ok: true,
         src: tc('''class A {
                        @Requires({ j != null && j.length > 0 })
                        static int f(int[] j) {
                            int s = 0
                            0.upto(j.length) { k -> s += 100.intdiv((int) k + 1) }
                            j.length.downto(0) { k -> s += 100.intdiv((int) k + 1) }
                            s
                        }
                    }''')],

        // Starting at -1, the divisor reaches 0.
        [group: "P380 closure range", name: "… from -1 still warns",
         expect: "Possible ArithmeticException: Division by zero",
         src: tc('''class A {
                        @Requires({ j != null })
                        static int f(int[] j) {
                            int s = 0
                            (-1).upto(j.length) { k -> s += 100.intdiv((int) k + 1) }
                            s
                        }
                    }''')],

        // Before: warned. Two closures, each its own range, read at its call (the second's `j.length.times` must not
        // cost the first its range).
        [group: "P380 closure range", name: "two range closures in a row",
         ok: true,
         src: tc('''class A {
                        @Requires({ j != null })
                        static int f(int[] j) {
                            int s = 0
                            j.length.times { k -> s += j[k] }
                            j.length.times { k -> s += j[k] }
                            s
                        }
                    }''')],

        // The range is the list's size at the call; the closure shrinks it, so the index can pass its end.
        [group: "P380 closure range", name: "a closure that shrinks what it iterates over",
         expect: ["List index may be outside [0, size)", "xs.size() (when the closure runs) = 0"],
         src: tc('''class A {
                        @Requires({ xs != null })
                        static boolean f(List<Integer> xs) {
                            (0..<xs.size()).every { xs.remove(0); xs[it] > 0 }
                        }
                    }''')],

        // Before: warned.
        [group: "P380 closure range", name: "collect over a range",
         ok: true,
         src: tc('''class A {
                        @Requires({ j != null })
                        static List<Integer> f(int[] j) { (0..<j.length).collect { j[it] * 2 } }
                    }''')],
    ]
}
