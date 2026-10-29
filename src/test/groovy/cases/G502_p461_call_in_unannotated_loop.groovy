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
 * 'P461 a call inside a loop with no invariant' — a call's @Requires inside a loop without an @Invariant was checked
 * in the state before the loop, its body's siblings up to the call replayed as if no iteration had run. A `while`'s
 * `int i = 0` pinned `i` (so `g(i)` was checked at i == 0 only, and `g` needing `i == 0` passed, though `f(2)` calls
 * `g(1)`); a `for`'s header `int i = 0` wasn't replayed at all, so `i` was free and the guard unassumed (a false
 * alarm, with a "fails on" call that never enters the loop). The call is checked at an arbitrary iteration now, as
 * Phase 371 checks the loop's other obligations: its init, everything it writes havocked, its guard holding.
 */
class G502_p461_call_in_unannotated_loop {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 461 (soundness): a call's @Requires inside a loop with no @Invariant is checked at an arbitrary iteration — the loop's init, its writes unknown, its guard holding — where it was checked before the loop (a `while`'s counter pinned to its first value, so a precondition broken on a later iteration passed); a refutation there names the failing call found along a run of the loop's first eight iterations (Phase 464), or none."

    static final String NOTE = 'no failing call: the call is inside a loop with no @Invariant'

    static final List<Map> CASES = [

        // ---------- broken on a later iteration: passed before ----------
        [group: "P461 a call inside a loop with no invariant", name: "a while's call broken on its second iteration",
         expect: ['Cannot prove precondition of g', 'fails on: f(2)'],
         src: tc('''class A {
                        @Requires({ n >= 2 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            while (i < n) { s += g(i); i++ }
                            return s
                        }
                        @Requires({ i == 0 })
                        static int g(int i) { i }
                    }''')],

        [group: "P461 a call inside a loop with no invariant", name: "… a standalone call", expect: ['Cannot prove precondition of g', 'fails on: f(2)'],
         src: tc('''class A {
                        @Requires({ n >= 2 })
                        static void f(int n) {
                            int i = 0
                            while (i < n) { g(i); i = i + 1 }
                        }
                        @Requires({ i == 0 })
                        static void g(int i) { }
                    }''')],

        [group: "P461 a call inside a loop with no invariant", name: "… in the loop's guard", expect: ['Cannot prove precondition of g', NOTE], refute: 'fails on',
         src: tc('''class A {
                        @Requires({ n >= 2 })
                        static int f(int n) {
                            int i = 0
                            while (g(i) < n) { i++ }
                            return i
                        }
                        @Requires({ i == 0 })
                        static int g(int i) { i }
                    }''')],

        [group: "P461 a call inside a loop with no invariant", name: "… a do-while's", expect: ['Cannot prove precondition of g', 'fails on: f(2)'],
         src: tc('''class A {
                        @Requires({ n >= 2 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            do { s += g(i); i++ } while (i < n)
                            return s
                        }
                        @Requires({ i == 0 })
                        static int g(int i) { i }
                    }''')],

        // a refutation before too, with a call that never enters the loop: `fails on: f(0)`
        [group: "P461 a call inside a loop with no invariant", name: "… a for's", expect: ['Cannot prove precondition of g', 'fails on: f(2)'],
         src: tc('''class A {
                        @Requires({ n >= 2 })
                        static int f(int n) {
                            int s = 0
                            for (int i = 0; i < n; i++) { s += g(i) }
                            return s
                        }
                        @Requires({ i == 0 })
                        static int g(int i) { i }
                    }''')],

        // ---------- what an arbitrary iteration knows ----------
        [group: "P461 a call inside a loop with no invariant", name: "its guard holds at the call", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            while (i < n) { s += g(i, n); i++ }
                            return s
                        }
                        @Requires({ i < n })
                        static int g(int i, int n) { i }
                    }''')],

        [group: "P461 a call inside a loop with no invariant", name: "what the loop doesn't write keeps its value", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 && k > 0 })
                        static int f(int n, int k) {
                            int s = 0
                            for (int i = 0; i < n; i++) { s += g(k) }
                            return s
                        }
                        @Requires({ k > 0 })
                        static int g(int k) { k }
                    }''')],

        // the counter's lower bound is the loop's invariant to state: without one it's unknown
        [group: "P461 a call inside a loop with no invariant", name: "a counter's bound needs an invariant", expect: ['Cannot prove precondition of g', NOTE], refute: 'fails on',
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            while (i < n) { s += g(i); i++ }
                            return s
                        }
                        @Requires({ i >= 0 })
                        static int g(int i) { i }
                    }''')],

        [group: "P461 a call inside a loop with no invariant", name: "… which proves it", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            while (i < n) { s += g(i); i++ }
                            return s
                        }
                        @Requires({ i >= 0 })
                        static int g(int i) { i }
                    }''')],

        // the shape that raised it: a recursive call in a loop, @Decreases on the method, @Invariant on the loop
        [group: "P461 a call inside a loop with no invariant", name: "a recursive call in a loop with an invariant", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        @Decreases({ n })
                        static int f(int n) {
                            int s = 0
                            @Invariant({ s >= 0 && 0 <= i && i <= n })
                            for (int i = 0; i < n; i++) { s += f(i) }
                            return s
                        }
                    }''')],
    ]
}
