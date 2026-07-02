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

/** 'P164 dutch-flag' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G040_p164_dutch_flag {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Dijkstra\'s Dutch National Flag — the in-place three-way partition proven sorted AND a permutation from a four-region loop @Invariant (reds | whites | unknown | blues) over three moving indices with @Decreases (hi - mid); permutation rides the per-store count law now threaded through loop-body preservation (Phase 165). The classic off-by-one (mid++ after the blue swap) refutes the sorted invariant, and a clobbering loop refutes the permutation invariant.'

    static final List<Map> CASES = [

        // ---------- Phase 164: Dijkstra's Dutch National Flag — in-place three-way partition ----------
        // The iconic loop-invariant exercise. Values in {0,1,2}; partition in place to all 0s, then 1s, then 2s.
        // The proof rests on a four-region @Invariant (reds [0,lo) | whites [lo,mid) | unknown [mid,hi) |
        // blues [hi,n)) with three moving indices, in-place swaps, and @Decreases (hi - mid). Z3 derives the
        // GLOBAL adjacent-sortedness postcondition from the three region facts at loop exit (mid == hi). The
        // method returns the array so the loop carries a post-loop value (the loop-checker's anchor).
        [group: 'P164 dutch-flag', name: 'three-way partition is sorted AND a permutation', ok: true,
         src: tc('''class C {
                       int[] a
                       @Requires({ (0..<a.length).every { 0 <= a[it] && a[it] <= 2 } && a.count(v) == c })
                       @Modifies({ this.a })
                       @Ensures({ (0..<a.length - 1).every { a[it] <= a[it + 1] } && a.count(v) == c })
                       int[] flag(int v, int c) {
                           int lo = 0
                           int mid = 0
                           int hi = a.length
                           @Invariant({ 0 <= lo && lo <= mid && mid <= hi && hi <= a.length &&
                                        (0..<lo).every { a[it] == 0 } &&
                                        (lo..<mid).every { a[it] == 1 } &&
                                        (hi..<a.length).every { a[it] == 2 } &&
                                        (mid..<hi).every { 0 <= a[it] && a[it] <= 2 } &&
                                        a.count(v) == c })
                           @Decreases({ hi - mid })
                           while (mid < hi) {
                               if (a[mid] == 0) {
                                   int t = a[lo]; a[lo] = a[mid]; a[mid] = t
                                   lo = lo + 1
                                   mid = mid + 1
                               } else if (a[mid] == 1) {
                                   mid = mid + 1
                               } else {
                                   hi = hi - 1
                                   int t = a[mid]; a[mid] = a[hi]; a[hi] = t
                               }
                           }
                           return a
                       }
                   }''')],
        // The classic off-by-one: advancing `mid` after the BLUE swap. The value swapped down from `hi` is
        // unexamined, so `mid++` can pull a 2 into the white region — the region invariant no longer holds.
        [group: 'P164 dutch-flag', name: 'mid++ after the blue swap refutes', expect: 'Cannot prove loop invariant',
         src: tc('''class C {
                       int[] a
                       @Requires({ (0..<a.length).every { 0 <= a[it] && a[it] <= 2 } })
                       @Modifies({ this.a })
                       @Ensures({ (0..<a.length - 1).every { a[it] <= a[it + 1] } })
                       int[] flag() {
                           int lo = 0
                           int mid = 0
                           int hi = a.length
                           @Invariant({ 0 <= lo && lo <= mid && mid <= hi && hi <= a.length &&
                                        (0..<lo).every { a[it] == 0 } &&
                                        (lo..<mid).every { a[it] == 1 } &&
                                        (hi..<a.length).every { a[it] == 2 } &&
                                        (mid..<hi).every { 0 <= a[it] && a[it] <= 2 } })
                           @Decreases({ hi - mid })
                           while (mid < hi) {
                               if (a[mid] == 0) {
                                   int t = a[lo]; a[lo] = a[mid]; a[mid] = t
                                   lo = lo + 1
                                   mid = mid + 1
                               } else if (a[mid] == 1) {
                                   mid = mid + 1
                               } else {
                                   hi = hi - 1
                                   int t = a[mid]; a[mid] = a[hi]; a[hi] = t
                                   mid = mid + 1
                               }
                           }
                           return a
                       }
                   }''')],
        // Permutation has teeth in the loop body too: a CLOBBERING loop (overwrite each slot with 0, dropping the
        // old value) is not a permutation, so the in-loop per-store count law correctly refutes the `a.count(v) == c`
        // invariant — the loop-body analogue of the Phase-12 "copy is not a permutation" soundness anchor.
        [group: 'P164 dutch-flag', name: 'clobbering loop is not a permutation', expect: 'Cannot prove loop invariant',
         src: tc('''class C {
                       int[] a
                       @Requires({ (0..<a.length).every { 0 <= a[it] && a[it] <= 2 } && a.count(v) == c })
                       @Modifies({ this.a })
                       @Ensures({ a.count(v) == c })
                       int[] flag(int v, int c) {
                           int i = 0
                           @Invariant({ 0 <= i && i <= a.length && a.count(v) == c })
                           @Decreases({ a.length - i })
                           while (i < a.length) {
                               a[i] = 0          // clobbers a[i] — drops its old value, so count(v) is not preserved
                               i = i + 1
                           }
                           return a
                       }
                   }''')],
    ]
}
