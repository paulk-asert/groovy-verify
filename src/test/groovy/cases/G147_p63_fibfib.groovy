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

/** 'P63 fibfib' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G147_p63_fibfib {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'HumanEval 063 — tribonacci (fibfib) via the Trib.of(i) recurrence helper; the iterative version proves equal to the spec.'

    static final List<Map> CASES = [

        // ---------- HumanEval 063 (fibfib): tribonacci via the Trib.of(i) helper ----------
        // The three-term sibling of 055. `Trib.of` indexing matches HumanEval's fibfib (Trib.of(5)==4,
        // Trib.of(8)==24); a literal index unfolds through the step axiom (0,0,1,1,2,4,7,13,24).
        [group: 'P63 fibfib', name: 'Trib.of(8) == 24', ok: true,
         src: tc('''class C {
                        @Ensures({ Trib.of(8) == 24 })
                        static void f() { }
                    }''')],
        // Step law at a literal index (positive non-vacuousness anchor; refuting a false claim is the weak direction).
        [group: 'P63 fibfib', name: 'Trib step law at 7 holds', ok: true,
         src: tc('''class C {
                        @Ensures({ Trib.of(7) == Trib.of(6) + Trib.of(5) + Trib.of(4) })
                        static void f() { }
                    }''')],
        // The textbook proof: an iterative fibfib provably equals the recursive definition. A 3-wide
        // rolling window (a==trib(i), b==trib(i+1), c==trib(i+2)); the step axiom re-establishes it across
        // `c = a + b + c` (e-matching trib(i+3) == trib(i+2)+trib(i+1)+trib(i)). Terminates (`n - i`).
        [group: 'P63 fibfib', name: 'iterative fibfib equals Trib.of(n)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == Trib.of(n) })
                        static int fibfib(int n) {
                            int a = 0
                            int b = 0
                            int c = 1
                            int i = 0
                            @Invariant({ 0 <= i && i <= n &&
                                         a == Trib.of(i) &&
                                         b == Trib.of(i + 1) &&
                                         c == Trib.of(i + 2) })
                            @Decreases({ n - i })
                            while (i < n) {
                                int t = a + b + c
                                a = b
                                b = c
                                c = t
                                i = i + 1
                            }
                            return a
                        }
                    }''')],
    ]
}
