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

/** 'P14 sort' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G039_p14_sort {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Insertion sort proven sorted AND a permutation at once; a no-op sort cannot claim sorted.'

    static final List<Map> CASES = [
        // ---------- Phase 14: the verified sort — sorted AND a permutation ----------
        // insert threads a ghost upper bound `hi` (the recursion passes the pivot a[m] as the new,
        // tight bound), a ghost count value `v` (permutation), and frames the suffix it doesn't touch.
        // Under sound call-site checking (Phase 24) the recursive precondition `insert(m-1, a[m], v)` needs
        // the *transitive* bound `a[it] <= a[m-1]` for all it<m-1 (the new pivot bound), which Z3 cannot get
        // from *adjacent* sortedness by e-matching (it times out). A monotone-bound LEMMA (`maxBound`, proved
        // by induction) supplies it: called before the swap, its @Ensures threads through the swap (Phase 24)
        // to the recursive call — and the sort is fully verified again.
        [group: 'P14 sort', name: 'insertion sort: sorted AND permutation', ok: true,
         src: tc('''class C {
                       int[] a
                       // lemma: every element of an adjacent-sorted prefix [0,k] is <= a[k], by induction on k.
                       @Requires({ 0 <= k && k < a.length && (0..<k).every { a[it] <= a[it + 1] } })
                       @Ensures({ (0..<k + 1).every { a[it] <= a[k] } })
                       @Decreases({ k })
                       void maxBound(int k) {
                           if (k > 0) maxBound(k - 1)
                       }
                       @Requires({ 0 <= m && m < a.length &&
                                   (0..<m - 1).every { a[it] <= a[it + 1] } &&
                                   (0..<m + 1).every { a[it] <= hi } })
                       @Modifies({ this.a })
                       @Ensures({ (0..<m).every { a[it] <= a[it + 1] } &&
                                  (0..<m + 1).every { a[it] <= hi } &&
                                  (m + 1..<a.length).every { a[it] == old.a[it] } &&
                                  a.count(v) == old.a.count(v) })
                       @Decreases({ m })
                       void insert(int m, int hi, int v) {
                           if (m > 0 && a[m] < a[m - 1]) {
                               maxBound(m - 1)
                               int t = a[m]; a[m] = a[m - 1]; a[m - 1] = t
                               insert(m - 1, a[m], v)
                           }
                       }
                       @Requires({ 0 <= n && n <= a.length && (0..<n).every { a[it] <= hi } })
                       @Modifies({ this.a })
                       @Ensures({ (0..<n - 1).every { a[it] <= a[it + 1] } &&
                                  (0..<n).every { a[it] <= hi } &&
                                  (n..<a.length).every { a[it] == old.a[it] } &&
                                  a.count(v) == old.a.count(v) })
                       @Decreases({ n })
                       void sort(int n, int hi, int v) {
                           if (n > 1) { sort(n - 1, hi, v); insert(n - 1, hi, v) }
                       }
                   }''')],
        // Soundness anchor: a sort that does nothing cannot claim its result is sorted → refuted.
        [group: 'P14 sort', name: 'no-op sort cannot claim sorted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= n && n <= a.length })
                       @Modifies({ this.a })
                       @Ensures({ (0..<n - 1).every { a[it] <= a[it + 1] } })
                       void sort(int n) { }
                   }''')],
    ]
}
