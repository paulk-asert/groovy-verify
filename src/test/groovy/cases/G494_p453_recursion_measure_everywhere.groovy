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
 * 'P453 a recursive call's measure, wherever it is' — a @Decreases measure was checked only at a recursive call that was
 * a whole assignment's right-hand side or a statement, while Phase 92 assumes the @Ensures of one in a return
 * (`return f(n)`, `n == 0 ? 7 : f(n + 1)`, `n * f(n)`): a method that never ends compiled clean under the measure that
 * claimed it does. Every recursive call on a path is checked now, under the `&&`, `||` and ternary operands guarding it.
 * And Phase 452's advice to add a @Decreases is given only where one would help.
 */
class G494_p453_recursion_measure_everywhere {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 453: a @Decreases measure is checked at every recursive call, not only one assigned to a local — `n == 0 ? 7 : f(n + 1)` and `n * f(n)` compiled clean under `@Decreases({ n })` — each under the `&&`, `||` or ternary operand guarding it; and a recursion a measure wouldn't help isn't told to add one."

    static final String MEASURE = "Cannot prove recursion measure decreases and stays >= 0 at this recursive call in f"

    static final List<Map> CASES = [

        // Unsound before: each compiled clean, never ending
        [group: "P453 a recursive call's measure, wherever it is", name: "a returned recursive call is checked against the measure",
         expect: MEASURE,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result == 7 })
                        @Decreases({ n })
                        static int f(int n) { return f(n) }
                    }''')],

        [group: "P453 a recursive call's measure, wherever it is", name: "… one in a ternary's arm",
         expect: MEASURE,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result == 7 })
                        @Decreases({ n })
                        static int f(int n) { n == 0 ? 7 : f(n + 1) }
                    }''')],

        [group: "P453 a recursive call's measure, wherever it is", name: "… one inside a larger expression",
         expect: MEASURE,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 1 })
                        @Decreases({ n })
                        static int f(int n) { n == 0 ? 1 : n * f(n) }
                    }''')],

        [group: "P453 a recursive call's measure, wherever it is", name: "… a predicate's",
         expect: MEASURE,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result })
                        @Decreases({ n })
                        static boolean f(int n) { n == 0 ? true : f(n + 1) }
                    }''')],

        [group: "P453 a recursive call's measure, wherever it is", name: "a local's was already checked",
         expect: MEASURE,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result == 7 })
                        @Decreases({ n })
                        static int f(int n) {
                            int r = f(n)
                            return r
                        }
                    }''')],

        // Each guard is what keeps the measure at or above zero
        [group: "P453 a recursive call's measure, wherever it is", name: "under a ternary's test the measure holds", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 1 })
                        @Decreases({ n })
                        static int f(int n) { n == 0 ? 1 : n * f(n - 1) }
                    }''')],

        [group: "P453 a recursive call's measure, wherever it is", name: "… gcd's", ok: true,
         src: tc('''class A {
                        @Requires({ a >= 0 && b >= 0 })
                        @Ensures({ result >= 0 })
                        @Decreases({ b })
                        static int gcd(int a, int b) { b == 0 ? a : gcd(b, a % b) }
                    }''')],

        [group: "P453 a recursive call's measure, wherever it is", name: "… under an &&", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ !result || n % 2 == 0 })
                        @Decreases({ n })
                        static boolean f(int n) { n == 0 || (n >= 2 && f(n - 2)) }
                    }''')],

        [group: "P453 a recursive call's measure, wherever it is", name: "… under an ||", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result })
                        @Decreases({ n })
                        static boolean f(int n) { n == 0 || f(n - 1) }
                    }''')],

        // Told to add a @Decreases before, which wouldn't have helped: a repetition (`* 2`) has no list value with one
        // either (the shape moved three times as list values grew: a ternary of lists binds since Phase 456, an append
        // since 457, a removal since 458)
        [group: "P453 a recursive call's measure, wherever it is", name: "a list-returning recursion isn't told to add a measure",
         expect: "return expression '(A.f((n - 1)) * 2)' is outside fragment",
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result != null && result.size() <= n })
                        static List<Integer> f(int n) { n == 0 ? [] : f(n - 1) * 2 }
                    }''')],
    ]
}
