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
 * 'P452 a recursive call without @Decreases' — a self-call's @Ensures is assumed (the inductive hypothesis) only under a
 * @Decreases measure, and without one the postcondition was skipped as "return expression '…' is outside fragment":
 * the expression was fine, the measure was missing. The skip now says so, and how to add one.
 */
class G493_p452_recursion_needs_decreases {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 452: a recursive method's postcondition skipped for want of a @Decreases says so (`gcd(b, a % b)` without one), where it blamed the return expression as outside the fragment — and with the measure added it proves."

    static final String NEEDS = "a recursive call's @Ensures is assumed only when a @Decreases measure shows the recursion ends"

    static final List<Map> CASES = [

        // Each was "return expression '…' is outside fragment" (or the assignment's)
        [group: "P452 a recursive call without @Decreases", name: "a ternary returning its recursive call names the missing measure",
         expect: NEEDS,
         src: tc('''class A {
                        @Requires({ a >= 0 && b >= 0 })
                        @Ensures({ result >= 0 })
                        static int gcd(int a, int b) { b == 0 ? a : gcd(b, a % b) }
                    }''')],

        [group: "P452 a recursive call without @Decreases", name: "… a return of one",
         expect: NEEDS,
         src: tc('''class A {
                        @Requires({ a >= 0 && b >= 0 })
                        @Ensures({ result >= 0 })
                        static int gcd(int a, int b) {
                            if (b == 0) return a
                            return gcd(b, a % b)
                        }
                    }''')],

        [group: "P452 a recursive call without @Decreases", name: "… a local bound to one",
         expect: NEEDS,
         src: tc('''class A {
                        @Requires({ a >= 0 && b >= 0 })
                        @Ensures({ result >= 0 })
                        static int gcd(int a, int b) {
                            if (b == 0) return a
                            int r = gcd(b, a % b)
                            return r
                        }
                    }''')],

        [group: "P452 a recursive call without @Decreases", name: "… one inside a larger expression",
         expect: NEEDS,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 1 })
                        static int fact(int n) { n == 0 ? 1 : n * fact(n - 1) }
                    }''')],

        [group: "P452 a recursive call without @Decreases", name: "with the measure it proves", ok: true,
         src: tc('''class A {
                        @Requires({ a >= 0 && b >= 0 })
                        @Ensures({ result >= 0 })
                        @Decreases({ b })
                        static int gcd(int a, int b) { b == 0 ? a : gcd(b, a % b) }
                    }''')],

        [group: "P452 a recursive call without @Decreases", name: "… and a false @Ensures is refuted",
         expect: "Cannot prove postcondition of gcd",
         src: tc('''class A {
                        @Requires({ a >= 0 && b >= 0 })
                        @Ensures({ result > 0 })
                        @Decreases({ b })
                        static int gcd(int a, int b) { b == 0 ? a : gcd(b, a % b) }
                    }''')],

        // Only a call to itself is asked for a measure: another method's call without an @Ensures is any value
        [group: "P452 a recursive call without @Decreases", name: "a call to another method isn't asked for one",
         expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Ensures({ result >= 0 })
                        static int f(int n) { g(n) }
                        static int g(int n) {
                            int s = 0
                            for (int i = 0; i < n; i++) { s++ }
                            return s
                        }
                    }''')],
    ]
}
