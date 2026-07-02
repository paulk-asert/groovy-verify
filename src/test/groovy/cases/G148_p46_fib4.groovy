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

/** 'P46 fib4' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G148_p46_fib4 {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'HumanEval 046 — tetranacci (fib4) via the Tetra.of(i) recurrence helper; the iterative version proves equal to the spec.'

    static final List<Map> CASES = [

        // ---------- HumanEval 046 (fib4): tetranacci via the Tetra.of(i) helper ----------
        // The FOUR-term sibling of 063 — the recurrence machinery extends one term wider. `Tetra.of` indexing
        // matches HumanEval's fib4 (base 0,0,2,0 → 0,0,2,0,2,4,8,14,28,54); a literal index unfolds via the step.
        [group: 'P46 fib4', name: 'Tetra.of(8) == 28', ok: true,
         src: tc('''class C {
                        @Ensures({ Tetra.of(8) == 28 })
                        static void f() { }
                    }''')],
        [group: 'P46 fib4', name: 'Tetra step law at 7 holds', ok: true,
         src: tc('''class C {
                        @Ensures({ Tetra.of(7) == Tetra.of(6) + Tetra.of(5) + Tetra.of(4) + Tetra.of(3) })
                        static void f() { }
                    }''')],
        // The textbook proof, one term wider: an iterative fib4 provably equals the recursive definition. A
        // 4-wide rolling window (a==tetra(i) … d==tetra(i+3)); the step axiom re-establishes it across
        // `e = a + b + c + d` (e-matching tetra(i+4) == tetra(i+3)+…+tetra(i)). Terminates (`n - i`).
        [group: 'P46 fib4', name: 'iterative fib4 equals Tetra.of(n)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == Tetra.of(n) })
                        static int fib4(int n) {
                            int a = 0
                            int b = 0
                            int c = 2
                            int d = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n &&
                                         a == Tetra.of(i) &&
                                         b == Tetra.of(i + 1) &&
                                         c == Tetra.of(i + 2) &&
                                         d == Tetra.of(i + 3) })
                            @Decreases({ n - i })
                            while (i < n) {
                                int t = a + b + c + d
                                a = b
                                b = c
                                c = d
                                d = t
                                i = i + 1
                            }
                            return a
                        }
                    }''')],
    ]
}
