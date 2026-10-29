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
 * 'P470 a helper whose call may vary' — Phase 469's second slice. A contract-free, write-free helper is a function of
 * its arguments and the state it reads; Phase 347's write analysis already refuses one calling a library static off its
 * write-free classes (`System.nanoTime()`), but two calls slipped through: `Math.random()` (a write-free class's one
 * nondeterministic static) and an own method that is no function (a contracted one: its value only what its @Ensures
 * allows). A helper making either was one term per argument list, so `h(n) != h(n)` was false and a `g` refusing 1
 * behind it passed. Its value is now a new one at each call (still defined by its body).
 */
class G511_p470_helper_varying_call {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 470 (soundness): a helper calling `Math.random()`, or an own method that is no function (a contracted one), is a new value at each call, where two calls with one argument list were taken as equal; a helper over deterministic statics (`Math.abs`) and other functions is still one."

    static final List<Map> CASES = [

        // ---------- two calls taken equal: passed before ----------
        [group: "P470 a helper whose call may vary", name: "Math.random", expect: ['Cannot prove precondition of g'],
         src: tc('''class A {
                        static void f(int n) {
                            if (h(n) > 0 && h(n) <= 0) g(1)
                        }
                        static int h(int i) { (int) (Math.random() * 100) - 50 }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P470 a helper whose call may vary", name: "an own contracted call", expect: ['Cannot prove precondition of g'],
         src: tc('''class A {
                        static void f(int n) {
                            if (h(n) != h(n)) g(1)
                        }
                        static int h(int i) { k() }
                        @Ensures({ result >= 0 })
                        static int k() { (int) (Math.random() * 100) }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P470 a helper whose call may vary", name: "… an instance one", expect: ['Cannot prove precondition of g'],
         src: tc('''final class A {
                        void f(int n) {
                            if (h(n) != h(n)) g(1)
                        }
                        int h(int i) { k() }
                        @Ensures({ result >= 0 })
                        int k() { (int) (Math.random() * 100) }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P470 a helper whose call may vary", name: "a helper calling one that does", expect: ['Cannot prove precondition of g'],
         src: tc('''class A {
                        static void f(int n) {
                            if (outer(n) != outer(n)) g(1)
                        }
                        static int outer(int i) { h(i) + 1 }
                        static int h(int i) { (int) (Math.random() * 100) }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        // ---------- deterministic: still one term ----------
        [group: "P470 a helper whose call may vary", name: "Math.abs and Math.max", ok: true,
         src: tc('''class A {
                        static void f(int n) {
                            if (h(n) != h(n)) g(1)
                        }
                        static int h(int i) { Math.abs(i) + Math.max(i, 3) }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P470 a helper whose call may vary", name: "a recursive one over Math.abs, past its unfolding", ok: true,
         src: tc('''class A {
                        static void f(int n) {
                            int x = s(n)
                            if (x != s(n)) g(1)
                        }
                        static int s(int k) { k <= 0 ? 0 : Math.abs(k) + s(k - 1) }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],
    ]
}
