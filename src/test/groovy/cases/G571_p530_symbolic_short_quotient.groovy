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
 * 'P530 symbolic short quotient' — Phase 529's open boundary closed. For integral operands Groovy's rounded
 * {@code a / b} is within {@code 0.55e-10} of the exact quotient (an integer's precision is at least the quotient's
 * integer digits, so the first rounding keeps at least 10 places) and sits on the {@code 1e-10} grid unless the exact
 * divide succeeded; a quotient on the grid is then the only candidate, so a symbolic divisor's short quotient is exact,
 * and a non-terminating one is pinned to Groovy's HALF_UP digits. Linear in the rounded value: no division in the fact
 * (measured, Groovy 6.0.0: worst error 5.4945e-11 over ~970,000 int, long and BigInteger pairs, no off-grid inexact
 * result).
 */
class G571_p530_symbolic_short_quotient {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 530: an integer division's short quotient is exact over a symbolic divisor (10 / n is 2.5 at n == 4), and a non-terminating one has Groovy's HALF_UP digits, from a division-free grid fact."

    static final String G = "P530 symbolic short quotient"

    static final List<Map> CASES = [
        [group: G, name: "10 / n is 2.5 at n == 4 (Phase 529's boundary)", ok: true,
         src: tc('class C { @Requires({ n == 4 }) @Ensures({ result == 2.5 }) static BigDecimal f(int n) { 10 / n } }')],
        [group: G, name: "1 / n is 0.125 at n == 8", ok: true,
         src: tc('class C { @Requires({ n == 8 }) @Ensures({ result == 0.125 }) static BigDecimal f(int n) { 1 / n } }')],
        [group: G, name: "ten places is still the grid: 1 / n is 0.0009765625 at n == 1024", ok: true,
         src: tc('class C { @Requires({ n == 1024 }) @Ensures({ result == 0.0009765625 }) static BigDecimal f(int n) { 1 / n } }')],
        [group: G, name: "a short quotient over a divisor in a set: 10 / n * n == 10 for n of 2 or 4", ok: true,
         src: tc('class C { @Requires({ n == 2 || n == 4 }) @Ensures({ result * n == 10 }) static BigDecimal f(int n) { 10 / n } }')],
        [group: G, name: "a symbolic dividend too: a / b is 0.5 where b == 2 * a", ok: true,
         src: tc('class C { @Requires({ a > 0 && b == 2 * a }) @Ensures({ result == 0.5 }) static BigDecimal f(int a, int b) { a / b } }')],
        [group: G, name: "a non-terminating quotient has Groovy's digits: 10 / n is 3.3333333333 at n == 3", ok: true,
         src: tc('class C { @Requires({ n == 3 }) @Ensures({ result == 3.3333333333 }) static BigDecimal f(int n) { 10 / n } }')],
        [group: G, name: "it rounds HALF_UP: 2 / n is 0.6666666667 at n == 3", ok: true,
         src: tc('class C { @Requires({ n == 3 }) @Ensures({ result == 0.6666666667 }) static BigDecimal f(int n) { 2 / n } }')],
        [group: G, name: "the wrong short quotient is refuted: 10 / n == 2.4 at n == 4", expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ n == 4 }) @Ensures({ result == 2.4 }) static BigDecimal f(int n) { 10 / n } }')],
        [group: G, name: "a non-terminating quotient isn't exact: (1 / n) * n == 1 at n == 3 is refuted", expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ n == 3 }) @Ensures({ result * n == 1 }) static BigDecimal f(int n) { 1 / n } }')],
        [group: G, name: "the truncated digit is refuted: 2 / n == 0.6666666666 at n == 3", expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ n == 3 }) @Ensures({ result == 0.6666666666 }) static BigDecimal f(int n) { 2 / n } }')],
        [group: G, name: "an exact quotient of 11 places stays reachable: 1 / n != 0.00048828125 at n == 2048 is refuted", expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ n == 2048 }) @Ensures({ result != 0.00048828125 }) static BigDecimal f(int n) { 1 / n } }')],
        // double rounding: 16 / 11 is 1.45454545455 at 12 digits, then 1.4545454546 (a single HALF_UP gives ...545)
        [group: G, name: "double rounding stays reachable: 16 / n != 1.4545454546 at n == 11 is refuted", expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ n == 11 }) @Ensures({ result != 1.4545454546 }) static BigDecimal f(int n) { 16 / n } }')],
        // boundary: a terminating quotient of more than 10 places is exact in Groovy (1 / 2048 is 0.00048828125), but
        // off the grid two neighbours are as close as the band allows: over-strict, never unsound
        [group: G, name: "boundary: 1 / n == 0.00048828125 at n == 2048 isn't derivable", expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ n == 2048 }) @Ensures({ result == 0.00048828125 }) static BigDecimal f(int n) { 1 / n } }')],
    ]
}
