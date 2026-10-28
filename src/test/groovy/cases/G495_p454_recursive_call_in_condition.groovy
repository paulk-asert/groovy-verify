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
 * 'P454 a recursive call in its own condition' — Phase 450 gave a condition's contracted call its @Ensures, but not the
 * method's call to itself: `if (f(n - 1) > 5)` skipped the postcondition, with a @Decreases or without one. Under a
 * measure it's the inductive hypothesis now, as in an assignment or a return (Phase 92) — the measure checked at it
 * (Phase 453); without one the skip says a measure is what's missing (Phase 452).
 */
class G495_p454_recursive_call_in_condition {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 454: a recursive method's call to itself in an `if` condition (`if (f(n - 1) < 0)`) carries its @Ensures under a @Decreases, as in an assignment or a return, where its postcondition was skipped; without a @Decreases the skip says one is missing."

    static final List<Map> CASES = [

        // A skip before: guard '…' is outside fragment
        [group: "P454 a recursive call in its own condition", name: "an if on the method's own call proves under its measure", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        @Decreases({ n })
                        static int f(int n) {
                            if (n == 0) return 0
                            if (f(n - 1) < 0) return -1
                            return n
                        }
                    }''')],

        // Already proved: a return's self-call is hoisted (Phase 92), its ternary's test included
        [group: "P454 a recursive call in its own condition", name: "… as a returned ternary's test already did", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        @Decreases({ n })
                        static int f(int n) { n == 0 ? 0 : (f(n - 1) >= 0 ? n : -1) }
                    }''')],

        [group: "P454 a recursive call in its own condition", name: "a postcondition the hypothesis doesn't give is refuted",
         expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        @Decreases({ n })
                        static int f(int n) {
                            if (n == 0) return 0
                            if (f(n - 1) < 1) return -1
                            return n
                        }
                    }''')],

        [group: "P454 a recursive call in its own condition", name: "the measure is checked at the condition's call",
         expect: "Cannot prove recursion measure decreases and stays >= 0 at this recursive call in f",
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        @Decreases({ n })
                        static int f(int n) {
                            if (n == 0) return 0
                            if (f(n) >= 0) return n
                            return 0
                        }
                    }''')],

        [group: "P454 a recursive call in its own condition", name: "without a measure the skip asks for one",
         expect: "a recursive call's @Ensures is assumed only when a @Decreases measure shows the recursion ends",
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 && result <= n })
                        static int f(int n) {
                            if (n == 0) return 0
                            if (f(n - 1) >= 0) return n
                            return 0
                        }
                    }''')],

        // Its @Requires still guards the hypothesis: assumed only where it holds, and checked at the call
        [group: "P454 a recursive call in its own condition", name: "its own precondition is still checked there",
         expect: "Cannot prove precondition of f",
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        @Decreases({ n })
                        static int f(int n) {
                            if (n == 0) return 0
                            if (f(n - 2) >= 0) return n
                            return 0
                        }
                    }''')],
    ]
}
