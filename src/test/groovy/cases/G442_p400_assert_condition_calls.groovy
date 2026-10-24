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
 * 'P400 assert-condition calls' — an inline `assert` is an obligation (since 273345b), but one whose condition calls a
 * method was skipped whatever the callee's contract said: `assert inc(41) == 42` with `@Ensures({ result == x + 1 })`
 * read "condition is outside fragment". The call is now hoisted to a local bound by the callee's @Ensures, as a return
 * value or an assignment's is (Phase 347). A refutation then rests on a result the solver chose within the contract,
 * which is no run's, so its call is withheld with a note to strengthen the contract.
 */
class G442_p400_assert_condition_calls {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 400: an assert whose condition calls a contracted method is checked against the callee's @Ensures (it was skipped as outside the fragment); a refutation withholds its call, the result being only what the contract allows."

    static final String NOTE = "no failing call: the assertion rests on what a call returns"

    static final List<Map> CASES = [

        // Before: `Skipped assertion safety check (condition '(MinMax.inc(41) == 42)' is outside fragment)` — and at every commit since asserts were checked (273345b); the groovy6-functional demos traded their asserts for a helper because of it.
        [group: "P400 assert-condition calls", name: "an assert over a call its contract settles proves",
         ok: true,
         src: tc('''class MinMax {
                            @Ensures({ result == x + 1 })
                            static int inc(int x) {
                                int y = x + 1
                                y
                            }
                            static void main(String[] args) {
                                assert inc(41) == 42
                            }
                        }''')],

        // max promises only result >= a && result >= b: the solver's 6 for max(3, 5) is no run's, so no call is shown.
        [group: "P400 assert-condition calls", name: "… one a weaker contract can't settle may not hold, with no call",
         expect: ["Assertion may not hold: (MinMax.max(3, 5) == 5)", NOTE, "Assertion may not hold: (MinMax.abs(-7) == 7)"], refute: "Assertion may not hold: (MinMax.inc(41) == 42)",
         src: tc('''class MinMax {
                            @Ensures({ result >= a && result >= b })
                            static int max(int a, int b) {
                                if (a > b) a else b
                            }
                            @Ensures({ result >= 0 })
                            static int abs(int x) {
                                if (x < 0) -x else x
                            }
                            @Ensures({ result == x + 1 })
                            static int inc(int x) {
                                int y = x + 1
                                y
                            }
                            static void main(String[] args) {
                                assert max(3, 5) == 5
                                assert max(9, 2) == 9
                                assert abs(-7) == 7
                                assert abs(4) == 4
                                assert inc(41) == 42
                                println "done"
                            }
                        }''')],

        // isqrt(9) == 3 follows from r*r <= 9 < (r+1)*(r+1); Phase 401 — and viaLiteral() == 2 too, through the isqrt(5)
        // in its body (it had no @Ensures, so its claim stayed open)
        [group: "P400 assert-condition calls", name: "… a nonlinear contract settles it too",
         ok: true,
         src: tc('''class G {
                            @Requires({ n >= 0 })
                            @Ensures({ result >= 0 && result * result <= n && n < (result + 1) * (result + 1) })
                            static int isqrt(int n) {
                                int r = 0
                                @Invariant({ 0 <= r && r * r <= n })
                                @Decreases({ n - r * r })
                                while ((r + 1) * (r + 1) <= n) { r = r + 1 }
                                return r
                            }
                            static int viaLiteral() {
                                isqrt(5)
                            }
                            static void main(String[] args) {
                                assert viaLiteral() == 2
                                assert isqrt(9) == 3
                            }
                        }''')],

        [group: "P400 assert-condition calls", name: "… a claim the contract contradicts refutes, the call withheld",
         expect: ["Assertion may not hold: (A.inc(41) == 43)", NOTE],
         src: tc('''class A {
                            @Ensures({ result == x + 1 })
                            static int inc(int x) { x + 1 }
                            static void main(String[] args) {
                                assert inc(41) == 43
                            }
                        }''')],

        [group: "P400 assert-condition calls", name: "… the call's own precondition is still checked",
         expect: ["Cannot prove precondition of inc at this call site"],
         src: tc('''class A {
                            @Requires({ x > 0 })
                            @Ensures({ result == x + 1 })
                            static int inc(int x) { x + 1 }
                            static void main(String[] args) {
                                assert inc(-1) == 0
                            }
                        }''')],

        [group: "P400 assert-condition calls", name: "… inside a loop body",
         ok: true,
         src: tc('''class A {
                            @Ensures({ result == x + 1 })
                            static int inc(int x) { x + 1 }
                            @Requires({ n >= 0 })
                            static int f(int n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    assert inc(i) == i + 1
                                    i = i + 1
                                }
                                return i
                            }
                        }''')],

        [group: "P400 assert-condition calls", name: "… and before a postcondition",
         ok: true,
         src: tc('''class A {
                            @Ensures({ result == x + 1 })
                            static int inc(int x) { x + 1 }
                            @Ensures({ result == 42 })
                            static int f() {
                                assert inc(41) == 42
                                return 42
                            }
                        }''')],
    ]
}
