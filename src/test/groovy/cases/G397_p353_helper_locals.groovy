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
 * 'P353 a helper with locals unfolds' — a contract-free helper was defined to the solver only when its body was a
 * single expression (Phase 8a's bounded unfolding); a body that bound a local first, reassigned a parameter, or
 * returned from an `if` left the call an uninterpreted function, so claims over its result refuted. The body is now
 * folded into one expression: declarations and reassignments become substitutions, `return e` (or a trailing
 * expression) the value, and an `if` a ternary over its two continuations. A loop, a `switch`, a `throw` or a
 * compound assignment still refuses. A sibling class's helper reading its own fields is no longer inlined.
 */
class G397_p353_helper_locals {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 353 a helper with locals unfolds: a contract-free helper body that declares or reassigns locals or parameters, returns from an if chain, or assigns a local in if/else branches is folded into one expression (substitutions, and a ternary per if), so `int n = x; n = n + 1; return n` and the statement form of factorial define their calls; a loop or switch still leaves the call opaque. Fixed (unsound before): a sibling class helper reading its own static was inlined in the caller scope, where the name meant the caller field.'

    static final List<Map> CASES = [

        // Before: only a single-expression body was inlined; anything else left `inc(k)` an opaque function, so this refuted.
        [group: 'P353 a helper with locals unfolds', name: 'a local copy unfolds', ok: true,
         src: tc('''class A {
                        static int inc(int x) { int n = x; return n + 1 }
                        @Requires({ k >= 0 })
                        @Ensures({ result == k + 1 })
                        static int f(int k) { inc(k) }
                    }''')],
        [group: 'P353 a helper with locals unfolds', name: 'a reassigned local unfolds', ok: true,
         src: tc('''class A {
                        static int inc(int x) { int n = x; n = n + 1; return n }
                        @Requires({ k >= 0 })
                        @Ensures({ result == k + 1 })
                        static int f(int k) { inc(k) }
                    }''')],
        [group: 'P353 a helper with locals unfolds', name: 'a reassigned parameter unfolds', ok: true,
         src: tc('''class A {
                        static int inc(int x) { x = x + 1; return x }
                        @Requires({ k >= 0 })
                        @Ensures({ result == k + 1 })
                        static int f(int k) { inc(k) }
                    }''')],
        [group: 'P353 a helper with locals unfolds', name: 'a wrong claim over a folded body still refutes', expect: ["Cannot prove postcondition of f", "fails on: f("],
         src: tc('''class A {
                        static int inc(int x) { int n = x; n = n + 1; return n }
                        @Requires({ k >= 0 })
                        @Ensures({ result == k + 2 })
                        static int f(int k) { inc(k) }
                    }''')],
        [group: 'P353 a helper with locals unfolds', name: 'an if/return chain folds to a ternary', ok: true,
         src: tc('''class A {
                        static int clamp(int x) { if (x < 0) return 0; if (x > 9) return 9; return x }
                        @Requires({ k >= 0 && k <= 9 })
                        @Ensures({ result == k })
                        static int f(int k) { clamp(k) }
                    }''')],
        [group: 'P353 a helper with locals unfolds', name: '… and its counterexample is the branch the claim misses', expect: ["Cannot prove postcondition of f", "fails on: f(10)"],
         src: tc('''class A {
                        static int clamp(int x) { if (x < 0) return 0; if (x > 9) return 9; return x }
                        @Requires({ k >= 0 })
                        @Ensures({ result == k })
                        static int f(int k) { clamp(k) }
                    }''')],
        // `int r;` used to make the write collector give up (an empty initialiser), so sgn wasn't even a function.
        [group: 'P353 a helper with locals unfolds', name: 'an if/else that assigns a local, declared with no initialiser', ok: true,
         src: tc('''class A {
                        static int sgn(int x) { int r; if (x > 0) { r = 1 } else if (x < 0) { r = -1 } else { r = 0 }; return r }
                        @Requires({ k > 0 })
                        @Ensures({ result == 1 })
                        static int f(int k) { sgn(k) }
                    }''')],
        [group: 'P353 a helper with locals unfolds', name: 'the statement form of factorial unfolds by fuel', ok: true,
         src: tc('''class A {
                        static int fact(int n) { if (n <= 0) return 1; return n * fact(n - 1) }
                        @Ensures({ result == 6 })
                        static int f() { fact(3) }
                    }''')],
        [group: 'P353 a helper with locals unfolds', name: '… and its recursive step holds symbolically', ok: true,
         src: tc('''class A {
                        static int fact(int n) { if (n <= 0) return 1; return n * fact(n - 1) }
                        @Requires({ k > 0 })
                        @Ensures({ result == k * fact(k - 1) })
                        static int f(int k) { fact(k) }
                    }''')],
        [group: 'P353 a helper with locals unfolds', name: 'a folded helper in a caller\'s contract', ok: true,
         src: tc('''class A {
                        static int dbl(int x) { int y = x + x; return y }
                        @Requires({ k >= 0 })
                        @Ensures({ result == dbl(k) })
                        static int f(int k) { 2 * k }
                    }''')],
        [group: 'P353 a helper with locals unfolds', name: 'a loop in the body still refuses: the call stays opaque', expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        static int sum(int x) { int s = 0; for (int i = 0; i < x; i++) { s = s + i }; return s }
                        @Requires({ k >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int k) { sum(k) }
                    }''')],
        // Fixed (unsound before, since Phase 350): the inlined `x + base` was translated in A's scope, where `base` is A's
        // field (0), so `result == k` verified — the truth is `k + 5`.
        [group: 'P353 a helper with locals unfolds', name: 'a sibling helper reading its own static is not inlined', expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        static int base = 0
                        @Requires({ base == 0 })
                        @Ensures({ result == k })
                        static int f(int k) { Util.tweak(k) }
                    }
                    class Util { static int base = 5; static int tweak(int x) { x + base } }''')],
        [group: 'P353 a helper with locals unfolds', name: '… and a sibling helper over its parameters still is', ok: true,
         src: tc('''class A {
                        static int base = 0
                        @Requires({ k >= 0 })
                        @Ensures({ result == k + 1 })
                        static int f(int k) { Util.tweak(k) }
                    }
                    class Util { static int tweak(int x) { int y = x; return y + 1 } }''')],
    ]
}
