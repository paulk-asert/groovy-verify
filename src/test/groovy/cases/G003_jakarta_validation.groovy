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

/** 'jakarta validation' — 11 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G003_jakarta_validation {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Jakarta/javax Bean Validation numeric constraints (@Positive/@Min/@Max/…) read as method-entry preconditions; contradictory ones are flagged vacuous.'

    static final List<Map> CASES = [

        // ---------- Jakarta Bean Validation constraints — read as method-entry preconditions ----------
        [group: 'jakarta validation', name: '@Positive divisor verifies', ok: true,
         src: tc('class C { static int f(@Positive int x) { 100 % x } }')],
        [group: 'jakarta validation', name: 'unannotated divisor refuted', expect: 'ArithmeticException: Division by zero',
         src: tc('class C { static int f(int x) { 100 % x } }')],
        [group: 'jakarta validation', name: '@Min(1) divisor verifies', ok: true,
         src: tc('class C { static int f(@Min(1L) int x) { 100 % x } }')],
        [group: 'jakarta validation', name: '@PositiveOrZero entails non-negative result', ok: true,
         src: tc('class C { @Ensures({ result >= 0 }) static int f(@PositiveOrZero int n) { n } }')],
        [group: 'jakarta validation', name: 'contradictory constraints are vacuous', expect: 'Vacuous precondition',
         src: tc('class C { static int f(@Positive @Negative int x) { x } }')],
        [group: 'jakarta validation', name: '@Size(min=1) array index verifies', ok: true,
         src: tc('class C { static int g(@Size(min = 1) int[] a) { a[0] } }')],
        // Out-of-grid jakarta bounds: the fixed input grid (ints ≤ 10, arrays ≤ length 3) can't satisfy these by
        // filtering, so the runtime rung *seeds* a witness from the constraint (jakarta → synthetic @Requires →
        // seedForParam) — the unification of the filter and seed paths. They verify trivially and lock that path.
        [group: 'jakarta validation', name: '@Min(1000000) large bound verifies (rung seeds it)', ok: true,
         src: tc('class C { @Ensures({ result >= 1000000 }) static int f(@Min(1000000) int n) { n } }')],
        [group: 'jakarta validation', name: '@Size(min=20) large length verifies (rung seeds it)', ok: true,
         src: tc('class C { @Ensures({ result >= 20 }) static int g(@Size(min = 20) int[] a) { a.length } }')],
        [group: 'jakarta validation', name: 'unbounded array index refuted', expect: 'IndexOutOfBoundsException',
         src: tc('class C { static int g(int[] a) { a[0] } }')],
        [group: 'jakarta validation', name: '@NotEmpty list index verifies', ok: true,
         src: tc('class C { static int h(@NotEmpty List<Integer> xs) { xs[0] } }')],
        [group: 'jakarta validation', name: '@NotEmpty string charAt verifies', ok: true,
         src: tc('class C { static char c(@NotEmpty String s) { s.charAt(0) } }')],
    ]
}
