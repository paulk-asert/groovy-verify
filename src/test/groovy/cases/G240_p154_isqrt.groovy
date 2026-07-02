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

/** 'P154 isqrt' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G240_p154_isqrt {

    static final List<Map> CASES = [

        // ---------- P154 isqrt — integer square root by the sum-of-odd-numbers trick (Toccata/Why3) ----------
        // The floor integer square root: result with result*result <= x < (result+1)*(result+1). The clever
        // algorithm never multiplies — it walks the odd numbers (1, 3, 5, …), whose running sum is the
        // successive perfect squares (sum of the first n odds == n*n). The load-bearing invariant is *quadratic*
        // and an equality: `sum == (count+1)*(count+1)`, preserved across `count += 1; sum += 2*count + 1`
        // because (c+1)^2 + 2(c+1) + 1 == (c+2)^2 — a degree-2 polynomial identity Z3's NIA closes. That, with
        // `x >= count*count`, ties the loop guard (`sum <= x`) to the floor bound: at exit sum > x and
        // sum == (count+1)^2 give the strict upper bound, x >= count^2 the lower. First port coupling a
        // quadratic *equality* invariant with the odd-number recurrence. (Contrast Math.sqrt, which is the FP
        // theory's approximate sqrt — this is the *exact* integer floor, pure number theory, no FP.)
        [group: 'P154 isqrt', name: 'isqrt: floor square root via the odd-number sum', ok: true,
         src: tc('''class C {
                        @Requires({ x >= 0 })
                        @Ensures({ result >= 0 && result * result <= x && x < (result + 1) * (result + 1) })
                        static int isqrt(int x) {
                            int count = 0
                            int sum = 1
                            @Invariant({ count >= 0 && x >= count * count && sum == (count + 1) * (count + 1) })
                            @Decreases({ x - count })
                            while (sum <= x) {
                                count = count + 1
                                sum = sum + 2 * count + 1
                            }
                            return count
                        }
                    }''')],
        // Soundness control: drop the quadratic invariant `sum == (count+1)*(count+1)`. Without it the running
        // `sum` is unmoored from `count`, so neither `x >= count*count` (which needs the guard `sum <= x` tied to
        // `count`) nor the floor postcondition can be re-established — the proof fails. (The odd-number sum is
        // the whole trick: the quadratic invariant is what makes a multiply-free loop prove a square-root bound.)
        [group: 'P154 isqrt', name: 'isqrt: dropping the quadratic invariant refutes', expect: 'Cannot prove loop invariant',
         src: tc('''class C {
                        @Requires({ x >= 0 })
                        @Ensures({ result >= 0 && result * result <= x && x < (result + 1) * (result + 1) })
                        static int isqrt(int x) {
                            int count = 0
                            int sum = 1
                            @Invariant({ count >= 0 && x >= count * count })
                            @Decreases({ x - count })
                            while (sum <= x) {
                                count = count + 1
                                sum = sum + 2 * count + 1
                            }
                            return count
                        }
                    }''')],
    ]
}
