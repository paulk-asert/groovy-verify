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

/** 'HE071 triangle_area' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G248_he071_triangle_area {

    static final List<Map> CASES = [

        // ---------- Triangle area (HumanEval/71) — the triangle inequality makes the half-perimeter terms safe ----------
        // The Verus rendering returns the *squared* area (s·(s−a)·(s−b)·(s−c)) to dodge floating-point sqrt — which keeps
        // it in exact integer arithmetic. The validity guard (triangle inequality) is what makes each factor non-negative.
        // The linear fact the whole thing rests on: under the triangle inequality, the half-perimeter s = (a+b+c)/2 is
        // ≥ each side, so `s - a` is non-negative. Pure linear + floor-division (intdiv) reasoning.
        [group: 'HE071 triangle_area', name: 'triangle inequality makes s - a non-negative', ok: true,
         src: tc('''class C {
                        @Requires({ a >= 0 && b >= 0 && c >= 0 && a + b > c && a + c > b && b + c > a })
                        @Ensures({ result >= 0 })
                        static int sMinusA(int a, int b, int c) {
                            int s = (a + b + c).intdiv(2)
                            return s - a
                        }
                    }''')],
        // The full HumanEval spec: a valid triangle yields a non-negative squared area, an invalid one yields -1. The
        // valid branch is a product of four guard-non-negative factors — exercises the nonlinear "product of
        // non-negatives is non-negative" reasoning end-to-end.
        [group: 'HE071 triangle_area', name: 'squared area is non-negative or -1', ok: true,
         src: tc('''class C {
                        @Requires({ a >= 0 && b >= 0 && c >= 0 })
                        @Ensures({ result == -1 || result >= 0 })
                        static int triangleAreaSquared(int a, int b, int c) {
                            if (a + b > c && a + c > b && b + c > a) {
                                int s = (a + b + c).intdiv(2)
                                return s * (s - a) * (s - b) * (s - c)
                            }
                            return -1
                        }
                    }''')],
        // An invalid triangle returns -1 — straight branch reasoning (the guard forces the else path).
        [group: 'HE071 triangle_area', name: 'degenerate triangle returns -1', ok: true,
         src: tc('''class C {
                        @Requires({ a + b <= c })
                        @Ensures({ result == -1 })
                        static int triangleAreaSquared(int a, int b, int c) {
                            if (a + b > c && a + c > b && b + c > a) {
                                int s = (a + b + c).intdiv(2)
                                return s * (s - a) * (s - b) * (s - c)
                            }
                            return -1
                        }
                    }''')],
        // The bug an incomplete validity check hides: drop two of the three inequalities and a "valid" triangle can have
        // a NEGATIVE squared area (e.g. a=10,b=1,c=1 → 6·(−4)·5·5 = −600), so the postcondition refutes.
        [group: 'HE071 triangle_area', name: 'incomplete validity check refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ a >= 0 && b >= 0 && c >= 0 })
                        @Ensures({ result == -1 || result >= 0 })
                        static int triangleAreaSquared(int a, int b, int c) {
                            if (a + b > c) {
                                int s = (a + b + c).intdiv(2)
                                return s * (s - a) * (s - b) * (s - c)
                            }
                            return -1
                        }
                    }''')],
        // The latent bug the Verus task glosses: with @CheckOverflow on, even modestly-bounded sides make the squared-area
        // product overflow 32-bit int — the value property holds in math, but the machine-int width is a real, separate bug.
        [group: 'HE071 triangle_area', name: 'squared-area product overflows int (@CheckOverflow)', expect: 'overflows 32-bit',
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ a >= 0 && a < 1000 && b >= 0 && b < 1000 && c >= 0 && c < 1000 })
                        static int triangleAreaSquared(int a, int b, int c) {
                            if (a + b > c && a + c > b && b + c > a) {
                                int s = (a + b + c).intdiv(2)
                                return s * (s - a) * (s - b) * (s - c)
                            }
                            return -1
                        }
                    }''')],
    ]
}
