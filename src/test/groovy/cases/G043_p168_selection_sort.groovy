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

/** 'P168 selection-sort' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G043_p168_selection_sort {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Iterative selection sort proven sorted AND a permutation (the loop-form twin of the P14 recursive insertion sort): an inner loop finds the minimum of a[i..n), an outer-loop swap helper places it at i (its @Requires discharged from the summarised inner loop\'s `i <= m < n`), and a single nested-quantifier invariant (each placed element <= everything after it) yields global sortedness — no hand-written lemma. Forgetting to place the minimum refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 168: iterative selection sort — sorted AND a permutation (nested loops, helper-in-loop) -----
        // The loop-form sort that pairs with the recursive insertion sort (P14). Outer loop places the minimum of
        // a[i..n) at position i via a SWAP HELPER called inside the loop (Phase 166 discharges its bounds @Requires
        // from the outer invariant + the summarised inner loop's `i <= m < n`); the inner loop finds that minimum.
        // The single nested-quantifier invariant `every k < i: every l > k: a[k] <= a[l]` (each placed element is
        // <= everything after it) yields global sortedness at exit, and the swap's @Ensures carries the permutation.
        // No hand-written lemma needed — Z3 maintains the nested quantifier across the swap on its own.
        [group: 'P168 selection-sort', name: 'selection sort: sorted AND a permutation', ok: true,
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= i && i < a.length && 0 <= j && j < a.length })
                       @Modifies({ this.a })
                       @Ensures({ a[i] == old.a[j] && a[j] == old.a[i] &&
                                  (0..<a.length).every { it == i || it == j || a[it] == old.a[it] } &&
                                  a.count(w) == old.a.count(w) })
                       void swap(int i, int j, int w) { int t = a[i]; a[i] = a[j]; a[j] = t }

                       @Requires({ a.count(v) == c })
                       @Modifies({ this.a })
                       @Ensures({ (0..<a.length - 1).every { a[it] <= a[it + 1] } && a.count(v) == c })
                       int[] sort(int v, int c) {
                           int i = 0
                           @Invariant({ 0 <= i && i <= a.length &&
                                        (0..<i).every { int k -> (k + 1..<a.length).every { int l -> a[k] <= a[l] } } &&
                                        a.count(v) == c })
                           @Decreases({ a.length - i })
                           while (i < a.length) {
                               int m = i
                               int j = i + 1
                               @Invariant({ 0 <= i && i <= m && m < a.length && i < j && j <= a.length &&
                                            (i..<j).every { a[m] <= a[it] } })
                               @Decreases({ a.length - j })
                               while (j < a.length) {
                                   if (a[j] < a[m]) m = j
                                   j = j + 1
                               }
                               swap(i, m, v)
                               i = i + 1
                           }
                           return a
                       }
                   }''')],
        // Teeth: a selection sort that finds the minimum but FORGETS to place it (no swap) can't re-establish the
        // "each placed element <= everything after it" invariant — preservation refutes.
        [group: 'P168 selection-sort', name: 'selection sort that forgets to place the min refutes', expect: 'Cannot prove loop invariant',
         src: tc('''class C {
                       int[] a
                       @Modifies({ this.a })
                       @Ensures({ (0..<a.length - 1).every { a[it] <= a[it + 1] } })
                       int[] sort() {
                           int i = 0
                           @Invariant({ 0 <= i && i <= a.length &&
                                        (0..<i).every { int k -> (k + 1..<a.length).every { int l -> a[k] <= a[l] } } })
                           @Decreases({ a.length - i })
                           while (i < a.length) {
                               int m = i
                               int j = i + 1
                               @Invariant({ 0 <= i && i <= m && m < a.length && i < j && j <= a.length &&
                                            (i..<j).every { a[m] <= a[it] } })
                               @Decreases({ a.length - j })
                               while (j < a.length) {
                                   if (a[j] < a[m]) m = j
                                   j = j + 1
                               }
                               i = i + 1     // BUG: never swaps the found minimum into position i
                           }
                           return a
                       }
                   }''')],
    ]
}
