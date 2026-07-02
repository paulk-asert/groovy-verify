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

/** 'P5b loop-fused' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G024_p5b_loop_fused {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'An in-loop array index is verified from the invariant (and refuted when unbounded); the post-loop index too.'

    static final List<Map> CASES = [

        // ---------- Phase 5b: loop-fused bounds (obligation under the invariant) ----------
        // a[i] inside the loop: i < n (guard) and n <= a.length (req) ⇒ i < a.size.
        [group: 'P5b loop-fused', name: 'in-loop index verified', ok: true,
         src: tc('''class C {
                       @Requires({ 0 <= n && n <= a.length })
                       static int sum(int[] a, int n) {
                           int s = 0
                           int i = 0
                           @Invariant({ 0 <= i && i <= n })
                           while (i < n) { s = s + a[i]; i = i + 1 }
                           return s
                       }
                   }''')],
        // Same loop without n <= a.length: the array may be shorter than n → refuted.
        [group: 'P5b loop-fused', name: 'in-loop index unbounded refuted', expect: 'IndexOutOfBoundsException',
         src: tc('''class C {
                       @Requires({ 0 <= n })
                       static int sum(int[] a, int n) {
                           int s = 0
                           int i = 0
                           @Invariant({ 0 <= i && i <= n })
                           while (i < n) { s = s + a[i]; i = i + 1 }
                           return s
                       }
                   }''')],
        // a[i] AFTER the loop: invariant i <= n and ¬guard i >= n pin i == n; n < a.length ⇒ safe.
        [group: 'P5b loop-fused', name: 'post-loop index verified', ok: true,
         src: tc('''class C {
                       @Requires({ 0 <= n && n < a.length })
                       static int at(int[] a, int n) {
                           int i = 0
                           @Invariant({ 0 <= i && i <= n })
                           while (i < n) { i = i + 1 }
                           return a[i]
                       }
                   }''')],
    ]
}
