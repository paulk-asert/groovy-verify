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

/** 'P143 decimal div' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G010_p143_decimal_div {

    static final List<Map> CASES = [

        // ---------- Phase 143: BigDecimal division modelled soundly (terminating divisors only) ----------
        // A terminating divisor (`/1000` — only the prime factors 2 and 5) is EXACT in Groovy, so exact Real
        // division is sound: `2000 / 1000 == 2` verifies (and the div-by-zero check discharges in the Real sort).
        [group: 'P143 decimal div', name: 'terminating divisor verifies exactly', ok: true,
         src: tc('''class C {
                        @Requires({ x == 2000.0 })
                        @Ensures({ result == 2.0 })
                        static BigDecimal f(BigDecimal x) { x / 1000.0 }
                    }''')],
        // A NON-terminating divisor (`/3`) rounds in Groovy (0.333…), so exact Real division would prove false
        // facts — it now SKIPS loudly instead. (Before the fix, `(x/3)*3 == 1.0` "verified", a runtime-false claim.)
        [group: 'P143 decimal div', name: 'non-terminating divisor skips (sound)', expect: 'Skipped verification of postcondition',
         src: tc('''class C {
                        @Requires({ x == 1.0 })
                        @Ensures({ result == 1.0 })
                        static BigDecimal f(BigDecimal x) { BigDecimal y = x / 3.0; y * 3.0 }
                    }''')],
        // The unit-conversion read-out now verifies for a terminating factor: a length's value in km is
        // metres / 1000, and a wrong factor refutes. (The record carries its own @TypeChecked so inKm is checked.)
        [group: 'P143 decimal div', name: 'conversion read-out (/1000) verifies', ok: true,
         src: HDR + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'record Length(BigDecimal metres) { @Ensures({ result == metres / 1000.0 }) BigDecimal inKm() { metres / 1000.0 } }'],
        [group: 'P143 decimal div', name: 'wrong conversion factor refutes', expect: 'Cannot prove postcondition',
         src: HDR + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'record Length(BigDecimal metres) { @Ensures({ result == metres / 100.0 }) BigDecimal inKm() { metres / 1000.0 } }'],
    ]
}
