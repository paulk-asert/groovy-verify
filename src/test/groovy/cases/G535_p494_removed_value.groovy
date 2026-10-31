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
 * 'P494 removed values' — the element a {@code pop()}, {@code removeLast()}, {@code removeAt(i)} or
 * {@code remove(int i)} returns is the one it removes, read before the call, with its nullity: a returned or assigned
 * removal was outside the fragment (Phase 493). And {@code removeAt(i)} / {@code remove(int i)} write: the elements
 * after {@code i} shift down one.
 */
class G535_p494_removed_value {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 494: a removal's value is the element it removes — `return xs.pop()` is `old.xs[0]`, `Integer r = xs.removeLast()` the last — and `removeAt(i)` shifts the rest down."

    static final List<Map> CASES = [

        // ---------- a returned removal ----------
        [group: "P494 removed values", name: "a returned pop is the first", ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() > 0 })
                        @Modifies({ this.xs })
                        @Ensures({ result == old.xs[0] && xs.size() == old.xs.size() - 1 })
                        Integer f() { xs.pop() }
                    }''')],
        [group: "P494 removed values", name: "… not the last", expect: ['Cannot prove postcondition'],
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() == 2 })
                        @Modifies({ this.xs })
                        @Ensures({ result == old.xs[1] })
                        Integer f() { xs.pop() }
                    }''')],
        [group: "P494 removed values", name: "… and its count", ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() > 0 })
                        @Modifies({ this.xs })
                        @Ensures({ xs.count(v) == old.xs.count(v) - (result == v ? 1 : 0) })
                        Integer f(int v) { xs.pop() }
                    }''')],
        [group: "P494 removed values", name: "a returned removeLast is the last", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[1] == 7 })
                        @Ensures({ result == 7 })
                        static Integer f(List<Integer> xs) { xs.removeLast() }
                    }''')],
        [group: "P494 removed values", name: "a returned null pop", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] == null })
                        @Ensures({ result == null })
                        static Integer f(List<Integer> xs) { xs.pop() }
                    }''')],
        [group: "P494 removed values", name: "… isn't known not null", expect: ['Cannot prove postcondition'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result != null })
                        static Integer f(List<Integer> xs) { xs.pop() }
                    }''')],

        // ---------- an assigned removal ----------
        [group: "P494 removed values", name: "two pops, in order", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 3 && xs[0] == 1 && xs[1] == 2 && xs[2] == 3 })
                        @Ensures({ result == 3 })
                        static int f(List<Integer> xs) { Integer a = xs.pop(); Integer b = xs.pop(); a + b }
                    }''')],
        [group: "P494 removed values", name: "… in one expression", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 3 && xs[0] == 1 && xs[1] == 2 && xs[2] == 3 })
                        @Ensures({ result == 5 })
                        static int f(List<Integer> xs) { xs.pop() + 2 * xs.pop() }
                    }''')],
        [group: "P494 removed values", name: "an assigned removeLast, then the size", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == 4 && xs[1] == 5 })
                        @Ensures({ result == 6 })
                        static int f(List<Integer> xs) { int r = xs.removeLast(); r + xs.size() }
                    }''')],
        [group: "P494 removed values", name: "an assigned pop's nullity", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == null && xs[1] != null })
                        @Ensures({ result })
                        static boolean f(List<Integer> xs) { Integer r = xs.pop(); r == null }
                    }''')],
        [group: "P494 removed values", name: "… read before the pop", expect: ['Cannot prove postcondition'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == null && xs[1] != null })
                        @Ensures({ result })
                        static boolean f(List<Integer> xs) { Integer r = xs.pop(); r != null }
                    }''')],

        // ---------- removeAt ----------
        [group: "P494 removed values", name: "removeAt returns the element there", ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && 0 <= i && i < xs.size() })
                        @Modifies({ this.xs })
                        @Ensures({ result == old.xs[i] })
                        Integer f(int i) { xs.removeAt(i) }
                    }''')],
        [group: "P494 removed values", name: "… and shifts the rest down", ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() == 3 })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == 2 && xs[0] == old.xs[0] && xs[1] == old.xs[2] })
                        void f() { xs.removeAt(1) }
                    }''')],
        [group: "P494 removed values", name: "… not keeping it", expect: ['Cannot prove postcondition'],
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() == 3 })
                        @Modifies({ this.xs })
                        @Ensures({ xs[1] == old.xs[1] })
                        void f() { xs.removeAt(1) }
                    }''')],
        [group: "P494 removed values", name: "remove(int) by index", ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == 8 && xs[1] == 9 })
                        @Modifies({ this.xs })
                        @Ensures({ result == 9 && xs.size() == 1 && xs[0] == 8 })
                        Integer f() { int i = 1; xs.remove(i) }
                    }''')],
        [group: "P494 removed values", name: "removeAt's count", ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && 0 <= i && i < xs.size() })
                        @Modifies({ this.xs })
                        @Ensures({ xs.count(v) == old.xs.count(v) - (old.xs[i] == v ? 1 : 0) })
                        void f(int i, int v) { xs.removeAt(i) }
                    }''')],
        [group: "P494 removed values", name: "a loop's removeAt", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 3 && xs[2] == 7 })
                        static void f(List<Integer> xs) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= 2 && xs.size() == 3 - i && xs[xs.size() - 1] == 7 })
                            @Decreases({ 2 - i })
                            while (i < 2) { xs.removeAt(0); i++ }
                        }
                    }''')],
        [group: "P494 removed values", name: "… removing the last", expect: ['Cannot prove loop invariant is preserved'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 3 && xs[2] == 7 })
                        static void f(List<Integer> xs) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= 2 && xs.size() == 3 - i && xs[xs.size() - 1] == 7 })
                            @Decreases({ 2 - i })
                            while (i < 2) { xs.removeAt(xs.size() - 1); i++ }
                        }
                    }''')],
    ]
}
