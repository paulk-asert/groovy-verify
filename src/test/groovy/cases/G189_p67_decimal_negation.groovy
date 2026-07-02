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

/** 'P67 decimal negation' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G189_p67_decimal_negation {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'BigDecimal unary minus / negative literals verify.'

    static final List<Map> CASES = [

        // ---------- Phase 67: decimal negation (unary minus, negative literal) ----------
        // Unary minus on a BigDecimal is Real negation — previously it fell to the int path (int
        // shadow) and refuted a true postcondition.
        [group: 'P67 decimal negation', name: 'decimal unary minus verified', ok: true,
         src: tc('class C { @Requires({ a == 2.5 }) @Ensures({ result == -2.5 }) static BigDecimal f(BigDecimal a) { -a } }')],
        // Negating a negative is positive — composes with the comparison path.
        [group: 'P67 decimal negation', name: 'negate a negative is positive', ok: true,
         src: tc('class C { @Requires({ a < 0.0 }) @Ensures({ result > 0.0 }) static BigDecimal f(BigDecimal a) { -a } }')],
        // A negative decimal literal as the return value (was skipped — translate left it unmodelled).
        [group: 'P67 decimal negation', name: 'negative decimal literal verified', ok: true,
         src: tc('class C { @Ensures({ result < 0.0 }) static BigDecimal f() { -2.5 } }')],
        // Soundness anchor: a wrong negation refutes.
        [group: 'P67 decimal negation', name: 'wrong decimal negation refuted',
         expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ a == 2.5 }) @Ensures({ result == 2.5 }) static BigDecimal f(BigDecimal a) { -a } }')],
    ]
}
