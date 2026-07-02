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

/** 'P61 decimal' — 8 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G188_p61_decimal {

    static final List<Map> CASES = [

        // ---------- Phase 61: Groovy-faithful BigDecimal division (Z3 Real sort) ----------
        // The headline Groovy surprise, now provable: `/` on integers is BigDecimal division, so
        // 5 / 2 is 2.5 — not 2. (A variable defeats the constant-folder so the `/` path is exercised.)
        [group: 'P61 decimal', name: 'a / 2 == 2.5 verified (BigDecimal division)', ok: true,
         src: tc('class C { @Requires({ a == 5 }) @Ensures({ a / 2 == 2.5 }) static int f(int a) { 0 } }')],
        // The lock-in that `/` is NOT integer division: 5 / 2 == 2 is false (it is 2.5).
        [group: 'P61 decimal', name: 'a / 2 == 2 refuted (/ is not intdiv)',
         expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ a == 5 }) @Ensures({ a / 2 == 2 }) static int f(int a) { 0 } }')],
        // Contrast: intdiv still truncates toward zero, so 5.intdiv(2) == 2 verifies — the two
        // operators are modelled distinctly (Real division vs Euclidean intdiv).
        [group: 'P61 decimal', name: 'a.intdiv(2) == 2 verified (contrast)', ok: true,
         src: tc('class C { @Requires({ a == 5 }) @Ensures({ a.intdiv(2) == 2 }) static int f(int a) { 0 } }')],
        // The compelling example: a BigDecimal average is *exactly* (a + b) / 2 — int operands
        // coerced to Real, the result a decimal name, the spec proven (not just asserted).
        [group: 'P61 decimal', name: 'BigDecimal avg == (a+b)/2 verified', ok: true,
         src: tc('''class C {
                        @Ensures({ result == (a + b) / 2 })
                        static BigDecimal avg(int a, int b) { (a + b) / 2 }
                    }''')],
        // Soundness anchor: claiming the average is (a + b) / 3 refutes.
        // (A terminating wrong divisor /4 — `/3` is non-terminating, so it soundly *skips* rather than refutes; see P143.)
        [group: 'P61 decimal', name: 'BigDecimal avg wrong divisor refuted',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == (a + b) / 4 })
                        static BigDecimal avg(int a, int b) { (a + b) / 2 }
                    }''')],
        // A BigDecimal-typed parameter compared against a decimal literal: price >= 10.0 ⇒ price > 9.99.
        [group: 'P61 decimal', name: 'BigDecimal param decimal comparison verified', ok: true,
         src: tc('class C { @Requires({ price >= 10.0 }) @Ensures({ price > 9.99 }) static int f(BigDecimal price) { 0 } }')],
        // The divide-by-zero obligation still fires for `/` — guarded it verifies...
        [group: 'P61 decimal', name: 'decimal division guarded by b != 0 verified', ok: true,
         src: tc('class C { @Requires({ b != 0 }) static BigDecimal f(int a, int b) { a / b } }')],
        // ...and unguarded it refutes with the ArithmeticException diagnostic.
        [group: 'P61 decimal', name: 'unguarded decimal division refuted',
         expect: 'ArithmeticException: Division by zero',
         src: tc('class C { static BigDecimal f(int a, int b) { a / b } }')],
    ]
}
