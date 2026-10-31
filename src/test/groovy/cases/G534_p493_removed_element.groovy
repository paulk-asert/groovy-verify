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
 * 'P493 removed elements' — {@code xs.pop()} takes the FIRST element (Groovy 2.5+; measured on 6.0.0:
 * {@code [1, 2, 3].pop()} is 1, leaving {@code [2, 3]}), and was modelled as {@code removeLast()}. The element a
 * {@code pop()}, {@code removeLast()}, {@code removeAt(i)} or {@code remove(int)} returns is unboxed where it's used,
 * and throws for a null one. {@code removeAt(i)} / {@code remove(int i)} need {@code i} in bounds, and a call's
 * negative index doesn't count from the end ({@code xs.get(-1)} throws). A callee's precondition sees a removal in a
 * declaration's initialiser, or under an {@code if}.
 */
class G534_p493_removed_element {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 493: `xs.pop()` takes the first element, not the last; a removed element unboxed throws for a null; `removeAt(i)` and `remove(int)` need `i` in bounds, and `xs.get(-1)` throws."

    static final List<Map> CASES = [

        // ---------- pop takes the first ----------
        [group: "P493 removed elements", name: "pop takes the first", expect: ['Cannot prove postcondition'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 })
                        @Ensures({ xs[0] == old.xs[0] })
                        static void f(List<Integer> xs) { xs.pop() }
                    }''')],
        [group: "P493 removed elements", name: "… and the rest shift down", ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() == 3 })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == 2 && xs[0] == old.xs[1] && xs[1] == old.xs[2] })
                        void f() { xs.pop() }
                    }''')],
        [group: "P493 removed elements", name: "… with their nullity", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[1] != null })
                        static int f(List<Integer> xs) { xs.pop(); int r = xs.pop(); r }
                    }''')],
        [group: "P493 removed elements", name: "… and their count", ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() > 0 })
                        @Modifies({ this.xs })
                        @Ensures({ xs.count(v) == old.xs.count(v) - (old.xs[0] == v ? 1 : 0) })
                        void f(int v) { xs.pop() }
                    }''')],
        [group: "P493 removed elements", name: "a loop's pop takes the first", expect: ['Cannot prove loop invariant is preserved'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 3 && xs[0] == 5 && xs[1] == 6 })
                        static void f(List<Integer> xs) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= 1 && xs.size() == 3 - i && xs[0] == 5 })
                            @Decreases({ 1 - i })
                            while (i < 1) { xs.pop(); i++ }
                        }
                    }''')],
        [group: "P493 removed elements", name: "… leaving the second", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 3 && xs[0] == 5 && xs[1] == 6 })
                        static void f(List<Integer> xs) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= 1 && xs.size() == 3 - i && (i == 0 ? xs[1] == 6 : xs[0] == 6) })
                            @Decreases({ 1 - i })
                            while (i < 1) { xs.pop(); i++ }
                        }
                    }''')],

        // ---------- a removed element unboxed ----------
        [group: "P493 removed elements", name: "a popped null unboxed", expect: ['Possible GroovyCastException: xs.pop() is null for a null element'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<Integer> xs) { int r = xs.pop(); r }
                    }''')],
        [group: "P493 removed elements", name: "… none when the first isn't", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] != null })
                        static int f(List<Integer> xs) { int r = xs.pop(); r }
                    }''')],
        [group: "P493 removed elements", name: "the last's, removed", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[1] != null })
                        static int f(List<Integer> xs) { int r = xs.removeLast(); r }
                    }''')],
        [group: "P493 removed elements", name: "… a null one", expect: ['Possible GroovyCastException: xs.removeLast() is null'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] != null })
                        static int f(List<Integer> xs) { int r = xs.removeLast(); r }
                    }''')],
        [group: "P493 removed elements", name: "one removed at an index, in arithmetic", expect: ['Possible NullPointerException: xs.removeAt(i) is null'],
         src: tc('''class C {
                        @Requires({ xs != null && 0 <= i && i < xs.size() })
                        static int f(List<Integer> xs, int i) { xs.removeAt(i) + 1 }
                    }''')],
        [group: "P493 removed elements", name: "… and by remove(int)", expect: ['Possible GroovyCastException: xs.remove(i) is null'],
         src: tc('''class C {
                        @Requires({ xs != null && 0 <= i && i < xs.size() })
                        static int f(List<Integer> xs, int i) { int r = xs.remove(i); r }
                    }''')],

        // ---------- what a callee sees ----------
        [group: "P493 removed elements", name: "a callee sees a declaration's pop", expect: ['Cannot prove precondition of g'],
         src: tc('''class C {
                        @Requires({ ys != null && ys.size() > 0 && ys[0] == null })
                        static boolean g(List<Integer> ys) { true }
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == null && xs[1] != null })
                        static boolean f(List<Integer> xs) { Integer r = xs.pop(); g(xs) }
                    }''')],
        [group: "P493 removed elements", name: "… and an assignment's", expect: ['Cannot prove precondition of g'],
         src: tc('''class C {
                        @Requires({ ys != null && ys.size() > 0 && ys[0] == null })
                        static boolean g(List<Integer> ys) { true }
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == null && xs[1] != null })
                        static boolean f(List<Integer> xs) { Integer r = 0; r = xs.pop(); g(xs) }
                    }''')],
        [group: "P493 removed elements", name: "… and an if's", expect: ['Cannot prove precondition of g'],
         src: tc('''class C {
                        @Requires({ ys != null && ys.size() == 2 })
                        static boolean g(List<Integer> ys) { true }
                        @Requires({ xs != null && xs.size() == 2 })
                        static boolean f(List<Integer> xs, boolean b) { if (b) xs.pop(); g(xs) }
                    }''')],
        // skipped until Phase 494 gave the removal its value; refuted since, as it's false
        [group: "P493 removed elements", name: "a returned pop still writes", expect: ['Cannot prove postcondition'],
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() == 2 })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == 2 })
                        Integer f() { xs.pop() }
                    }''')],

        // ---------- an index a call is given ----------
        [group: "P493 removed elements", name: "removeAt needs its index in bounds", expect: ['Possible IndexOutOfBoundsException'],
         src: tc('''class C {
                        @Requires({ xs != null })
                        static Integer f(List<Integer> xs, int i) { xs.removeAt(i) }
                    }''')],
        [group: "P493 removed elements", name: "… as remove(int) does", expect: ['Possible IndexOutOfBoundsException'],
         src: tc('''class C {
                        @Requires({ xs != null })
                        static Integer f(List<Integer> xs, int i) { xs.remove(i) }
                    }''')],
        [group: "P493 removed elements", name: "… and has it", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && 0 <= i && i < xs.size() })
                        static void f(List<Integer> xs, int i) { xs.removeAt(i) }
                    }''')],
        [group: "P493 removed elements", name: "a call's negative index throws", expect: ['obligation: 0 <= -1 && -1 < xs.size()'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 })
                        static Integer f(List<Integer> xs) { xs.get(-1) }
                    }''')],
        [group: "P493 removed elements", name: "… a subscript's counts from the end", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 })
                        static Integer f(List<Integer> xs) { xs[-1] }
                    }''')],
    ]
}
