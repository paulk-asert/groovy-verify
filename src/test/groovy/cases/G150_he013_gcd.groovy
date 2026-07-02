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

/** 'HE013 gcd' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G150_he013_gcd {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'HumanEval 013 — Euclid\'s gcd via the Gcd.of(a,b) recurrence helper; the iterative loop proves equal to the spec.'

    static final List<Map> CASES = [

        // ---------- HumanEval 013 (greatest_common_divisor): Euclid via the Gcd.of(a, b) helper ----------
        // The two-argument sibling of 055/063. `Gcd.of` is Euclid; a literal pair unfolds through the step
        // axiom down to the base (gcd(12,8) → gcd(8,4) → gcd(4,0) → 4).
        [group: 'HE013 gcd', name: 'Gcd.of(12, 8) == 4', ok: true,
         src: tc('''class C {
                        @Ensures({ Gcd.of(12, 8) == 4 })
                        static int g() { 4 }
                    }''')],
        // The Euclid recurrence itself — the step axiom restated as a postcondition (proves directly).
        [group: 'HE013 gcd', name: 'Gcd.of(a, b) == Gcd.of(b, a % b) when b != 0', ok: true,
         src: tc('''class C {
                        @Requires({ b != 0 })
                        @Ensures({ Gcd.of(a, b) == Gcd.of(b, a % b) })
                        static void rel(int a, int b) { }
                    }''')],
        // Iterative Euclid equals Gcd.of(a, b): the invariant `Gcd.of(x, y) == Gcd.of(a, b)` is preserved by
        // `t = x % y; x = y; y = t` (step axiom, b != 0 from the guard), and at exit (y == 0) the base axiom
        // gives x == Gcd.of(a, b). Terminates: `y` strictly decreases (x % y ∈ [0, y) for x >= 0, y > 0).
        [group: 'HE013 gcd', name: 'iterative Euclid equals Gcd.of(a, b)', ok: true,
         src: tc('''class C {
                        @Requires({ a >= 0 && b >= 0 })
                        @Ensures({ result == Gcd.of(a, b) })
                        static int gcd(int a, int b) {
                            int x = a
                            int y = b
                            @Invariant({ x >= 0 && y >= 0 &&
                                         Gcd.of(x, y) == Gcd.of(a, b) })
                            @Decreases({ y })
                            while (y != 0) {
                                int t = x % y
                                x = y
                                y = t
                            }
                            return x
                        }
                    }''')],
        // Without a non-negativity precondition the Euclid loop's bounds invariant `x >= 0 && y >= 0`
        // (the part that drives @Decreases via `x % y ∈ [0, y)`) can't be established on entry — a negative
        // input is a crisp counterexample. (A *value* refutation like `Gcd.of(12,8)==5` instead soft-fails
        // with "could not decide / timeout": the recursive step axiom is prove-friendly via e-matching but
        // refute-hostile — finding a SAT model under an infinitely-instantiable axiom defeats MBQI. The
        // verifier still rejects it; it just can't produce a counterexample. Same trade-off as fib/trib.)
        [group: 'HE013 gcd', name: 'Euclid loop bounds need a non-negativity precondition',
         src: tc('''class C {
                        static int gcd(int a, int b) {
                            int x = a
                            int y = b
                            @Invariant({ x >= 0 && y >= 0 })
                            @Decreases({ y })
                            while (y != 0) {
                                int t = x % y
                                x = y
                                y = t
                            }
                            return x
                        }
                    }'''),
         expect: 'Cannot prove loop invariant holds on entry'],
    ]
}
