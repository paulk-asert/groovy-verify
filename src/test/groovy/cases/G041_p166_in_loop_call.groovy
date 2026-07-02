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

/** 'P166 in-loop-call' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G041_p166_in_loop_call {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A contracted method called inside an annotated loop body has its precondition discharged under the loop invariant + guard (the loop variables symbolic, the in-loop preceding statements replayed from the clean body), not the loop-entry / havoc\'d state — so a swap-helper-based Dutch National Flag verifies, and an in-loop call whose precondition the invariant doesn\'t establish refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 166: a contracted call inside a loop body, precondition under the loop invariant ----------
        // The Dutch National Flag built from a SWAP HELPER (a contracted method) instead of inline stores: each
        // `swap(...)` call's @Requires (the indices are in bounds) is discharged against an ARBITRARY iteration —
        // the loop invariant + guard, with the loop variables symbolic and the in-loop preceding statements
        // (`hi = hi - 1`) replayed — not the loop-entry / havoc'd state. Proves both that the precondition holds and
        // (via the loop's use of the swap @Ensures) that the partition is sorted. Companion refute below.
        [group: 'P166 in-loop-call', name: 'in-loop swap helper: precondition from the invariant', ok: true,
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= i && i < a.length && 0 <= j && j < a.length })
                       @Modifies({ this.a })
                       @Ensures({ a[i] == old.a[j] && a[j] == old.a[i] &&
                                  (0..<a.length).every { it == i || it == j || a[it] == old.a[it] } })
                       void swap(int i, int j) { int t = a[i]; a[i] = a[j]; a[j] = t }

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
                                   swap(lo, mid)
                                   lo = lo + 1
                                   mid = mid + 1
                               } else if (a[mid] == 1) {
                                   mid = mid + 1
                               } else {
                                   hi = hi - 1
                                   swap(mid, hi)
                               }
                           }
                           return a
                       }
                   }''')],
        // Teeth: the discharge is real, not vacuous. Calling `swap(mid, hi)` WITHOUT first decrementing `hi` passes
        // `hi` as an index, but the invariant only gives `hi <= a.length` — so `hi` can equal `a.length`, out of
        // bounds. The in-loop precondition check (now seeing the invariant) correctly refutes.
        [group: 'P166 in-loop-call', name: 'in-loop call with an unmet precondition refutes', expect: 'Cannot prove precondition',
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= i && i < a.length && 0 <= j && j < a.length })
                       @Modifies({ this.a })
                       @Ensures({ a[i] == old.a[j] && a[j] == old.a[i] &&
                                  (0..<a.length).every { it == i || it == j || a[it] == old.a[it] } })
                       void swap(int i, int j) { int t = a[i]; a[i] = a[j]; a[j] = t }

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
                                   swap(lo, mid)
                                   lo = lo + 1
                                   mid = mid + 1
                               } else if (a[mid] == 1) {
                                   mid = mid + 1
                               } else {
                                   swap(mid, hi)    // BUG: hi not decremented — hi can equal a.length (out of bounds)
                                   hi = hi - 1
                               }
                           }
                           return a
                       }
                   }''')],
    ]
}
