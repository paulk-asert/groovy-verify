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

/** 'P6 in-loop store' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G051_p6_in_loop_store {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'An in-loop array store (zero-fill) preserves a quantified invariant; a store that breaks it refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 6: in-loop store (array update threaded through a loop) ----------
        // Fill a[0..n) with 0; the content invariant is preserved across the store and
        // proves the postcondition that the whole range is zeroed.
        [group: 'P6 in-loop store', name: 'zero-fill verified', ok: true,
         src: tc('''class C {
                       @Requires({ 0 <= n && n <= a.length })
                       @Ensures({ Forall.range(0, n) { i -> a[i] == 0 } })
                       static int zero(int[] a, int n) {
                           int i = 0
                           @Invariant({ 0 <= i && i <= n && Forall.range(0, i, { int j -> a[j] == 0 }) })
                           @Decreases({ n - i })
                           while (i < n) { a[i] = 0; i = i + 1 }
                           return 0
                       }
                   }''')],
        // The body stores 1 but the invariant claims the range is 0 → preservation refuted.
        [group: 'P6 in-loop store', name: 'store breaks invariant refuted', expect: 'invariant is preserved',
         src: tc('''class C {
                       @Requires({ 0 <= n && n <= a.length })
                       static int fill(int[] a, int n) {
                           int i = 0
                           @Invariant({ 0 <= i && i <= n && Forall.range(0, i, { int j -> a[j] == 0 }) })
                           @Decreases({ n - i })
                           while (i < n) { a[i] = 1; i = i + 1 }
                           return 0
                       }
                   }''')],
    ]
}
