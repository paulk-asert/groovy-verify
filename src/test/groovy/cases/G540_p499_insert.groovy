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
 * 'P499 insertions' — {@code xs.add(i, v)} puts {@code v} at {@code i} and shifts the elements from {@code i} on up one
 * (measured on Groovy 6.0.0: {@code [1, 2, 3].add(1, 9)} leaves {@code [1, 9, 2, 3]}), the mirror of Phase 494's
 * {@code removeAt(i)}. Its index may be the end, {@code xs.size()}, which appends; outside {@code [0, size]}, a negative
 * one included, it throws IndexOutOfBoundsException.
 */
class G540_p499_insert {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 499: `xs.add(i, v)` inserts — `v` at `i`, the rest shifted up, the size one more — and needs `0 <= i <= xs.size()`."

    static final List<Map> CASES = [

        // ---------- what an insertion leaves ----------
        [group: "P499 insertions", name: "an insertion shifts the rest up", ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() == 3 })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == 4 && xs[0] == old.xs[0] && xs[1] == 9 && xs[2] == old.xs[1] && xs[3] == old.xs[2] })
                        void f() { xs.add(1, 9) }
                    }''')],
        [group: "P499 insertions", name: "… not keeping the old element there", expect: ['Cannot prove postcondition'],
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() == 3 })
                        @Modifies({ this.xs })
                        @Ensures({ xs[1] == old.xs[1] })
                        void f() { xs.add(1, 9) }
                    }''')],
        [group: "P499 insertions", name: "at the front", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == 4 && xs[1] == 5 })
                        @Ensures({ result == 8 })
                        static int f(List<Integer> xs) { xs.add(0, 3); xs[0] + xs[2] + xs.size() - 3 }
                    }''')],
        [group: "P499 insertions", name: "at the end, an append", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 })
                        @Ensures({ result == 7 })
                        static int f(List<Integer> xs) { xs.add(xs.size(), 7); xs[2] }
                    }''')],
        [group: "P499 insertions", name: "its count", ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && 0 <= i && i <= xs.size() })
                        @Modifies({ this.xs })
                        @Ensures({ xs.count(v) == old.xs.count(v) + (w == v ? 1 : 0) })
                        void f(int i, int w, int v) { xs.add(i, w) }
                    }''')],
        [group: "P499 insertions", name: "an inserted null", expect: ['Possible GroovyCastException'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 && xs[0] != null })
                        static int f(List<Integer> xs) { xs.add(0, null); int r = xs[0]; r }
                    }''')],
        [group: "P499 insertions", name: "… shifts the others' nullity up", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 && xs[0] != null })
                        static int f(List<Integer> xs) { xs.add(0, null); int r = xs[1]; r }
                    }''')],
        [group: "P499 insertions", name: "into a list of strings", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 && xs[0] == 'a' })
                        @Ensures({ result })
                        static boolean f(List<String> xs) { xs.add(0, 'b'); xs[0] == 'b' && xs[1] == 'a' && xs.size() == 2 }
                    }''')],
        [group: "P499 insertions", name: "… a null one", expect: ['Cannot prove postcondition'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 })
                        @Ensures({ result })
                        static boolean f(List<String> xs) { xs.add(0, null); xs[0] != null }
                    }''')],
        [group: "P499 insertions", name: "a callee sees it", expect: ['Cannot prove precondition of g'],
         src: tc('''class C {
                        @Requires({ ys != null && ys.size() == 2 })
                        static boolean g(List<Integer> ys) { true }
                        @Requires({ xs != null && xs.size() == 2 })
                        static boolean f(List<Integer> xs) { xs.add(1, 5); g(xs) }
                    }''')],

        // ---------- the index ----------
        [group: "P499 insertions", name: "the index needs bounds", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= i && i <= xs.size()'],
         src: tc('''class C {
                        @Requires({ xs != null })
                        static void f(List<Integer> xs, int i) { xs.add(i, 5) }
                    }''')],
        [group: "P499 insertions", name: "… and the end is in them", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && 0 <= i && i <= xs.size() })
                        static void f(List<Integer> xs, int i) { xs.add(i, 5) }
                    }''')],
        [group: "P499 insertions", name: "… but not past it", expect: ['Possible IndexOutOfBoundsException', 'fails on: f([], 1)'],
         src: tc('''class C {
                        @Requires({ xs != null && 0 <= i && i <= xs.size() + 1 })
                        static void f(List<Integer> xs, int i) { xs.add(i, 5) }
                    }''')],
        [group: "P499 insertions", name: "a negative index throws", expect: ['obligation: 0 <= -1 && -1 <= xs.size()'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 })
                        static void f(List<Integer> xs) { xs.add(-1, 5) }
                    }''')],

        // ---------- in a loop ----------
        [group: "P499 insertions", name: "a loop's insertion at the front", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 && xs[0] == 7 })
                        static void f(List<Integer> xs) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= 3 && xs.size() == 1 + i && xs[xs.size() - 1] == 7 })
                            @Decreases({ 3 - i })
                            while (i < 3) { xs.add(0, i); i++ }
                        }
                    }''')],
        [group: "P499 insertions", name: "… not appending", expect: ['Cannot prove loop invariant is preserved'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 && xs[0] == 7 })
                        static void f(List<Integer> xs) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= 3 && xs.size() == 1 + i && xs[0] == 7 })
                            @Decreases({ 3 - i })
                            while (i < 3) { xs.add(0, i); i++ }
                        }
                    }''')],
    ]
}
