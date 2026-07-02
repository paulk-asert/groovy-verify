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

/** 'P5a short-circuit' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G048_p5a_short_circuit {

    static final List<Map> CASES = [

        // ---------- Phase 5a: short-circuit guard path conditions (&& / ||) ----------
        // The `&&` left operands (`i > 0 && i <= a.length`) protect `a[i-1]` in the right operand.
        [group: 'P5a short-circuit', name: 'and-guard protects right operand', ok: true,
         src: tc('class C { static int g(int[] a, int i) { (i > 0 && i <= a.length && a[i - 1] > 0) ? 1 : 0 } }')],
        // `||`: entering the right operand means the left disjuncts are false → `0 < i <= a.length`.
        [group: 'P5a short-circuit', name: 'or-guard protects right operand', ok: true,
         src: tc('class C { static int g(int[] a, int i) { (i <= 0 || i > a.length || a[i - 1] > 0) ? 1 : 0 } }')],
        // Still sound: with the guard removed, the access is genuinely unprotected → refuted.
        [group: 'P5a short-circuit', name: 'unguarded access still refuted', expect: 'IndexOutOfBoundsException',
         src: tc('class C { static int g(int[] a, int i) { (a[i - 1] > 0) ? 1 : 0 } }')],
        // The natural (single-&&) recursive insert now verifies — no nested-if workaround needed.
        [group: 'P5a short-circuit', name: 'natural insert guard verifies', ok: true,
         src: tc('''class C {
                       @Requires({ 0 <= i && i < a.length && (0..<i - 1).every { a[it] <= a[it + 1] } })
                       @Ensures({ (0..<i).every { a[it] <= a[it + 1] } })
                       @Decreases({ i })
                       static void insert(int[] a, int i) {
                           if (i > 0 && a[i] < a[i - 1]) {
                               int t = a[i]; a[i] = a[i - 1]; a[i - 1] = t
                               insert(a, i - 1)
                           }
                       }
                   }''')],
    ]
}
