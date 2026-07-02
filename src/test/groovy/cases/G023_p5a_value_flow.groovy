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

/** 'P5a value-flow' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G023_p5a_value_flow {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'An index constrained by a prior assignment (or an aliased index under a guard) is verified; an unconstrained one refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 5a: value-flow (safety implied by an assignment) ----------
        // j == 3 is threaded, so 0 <= 3 < a.length follows from a.length > 5.
        [group: 'P5a value-flow', name: 'assignment-implied index verified', ok: true,
         src: tc('class C { @Requires({ a.length > 5 }) static int f(int[] a) { int j = 3; return a[j] } }')],
        // Same body without the precondition: a may be empty → refuted.
        [group: 'P5a value-flow', name: 'unconstrained assignment index refuted', expect: 'IndexOutOfBoundsException',
         src: tc('class C { static int f(int[] a) { int j = 3; return a[j] } }')],
        // Aliased counter: j == i, guard bounds i, precondition bounds a — needs value-flow + guard together.
        [group: 'P5a value-flow', name: 'aliased index under guard verified', ok: true,
         src: tc('class C { @Requires({ a.length > 10 }) static int f(int[] a, int i) { int j = i; if (i >= 0 && i < 5) return a[j]; return 0 } }')],
        // Modulo by an assigned value known non-zero.
        [group: 'P5a value-flow', name: 'assignment-implied divisor verified', ok: true,
         src: tc('class C { static int f(int x) { int d = 2; x % d } }')],
    ]
}
