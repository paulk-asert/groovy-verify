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

/** 'P167 reverse' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G042_p167_reverse {

    static final List<Map> CASES = [

        // ---------- Phase 167: in-place array reverse via a swap helper (helper-in-loop + permutation) ----------
        // A single loop, swapping a[lo] with a[hi] and walking the two indices inward. Each swap is a CONTRACTED
        // helper call inside the loop (Phase 166 discharges its bounds @Requires from the invariant), and its
        // @Ensures supplies both the element exchange (proving the reversal a[k] == orig[n-1-k]) and count
        // preservation (the permutation). `orig` is a ghost capturing the entry array (a == orig at entry) so the
        // spec avoids `old.a` in the loop invariant, which isn't bound there. Companion refute below.
        [group: 'P167 reverse', name: 'in-place reverse: reversal AND permutation', ok: true,
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= i && i < a.length && 0 <= j && j < a.length })
                       @Modifies({ this.a })
                       @Ensures({ a[i] == old.a[j] && a[j] == old.a[i] &&
                                  (0..<a.length).every { it == i || it == j || a[it] == old.a[it] } &&
                                  a.count(w) == old.a.count(w) })
                       void swap(int i, int j, int w) { int t = a[i]; a[i] = a[j]; a[j] = t }

                       @Requires({ orig.length == a.length && (0..<a.length).every { a[it] == orig[it] } && a.count(v) == c })
                       @Modifies({ this.a })
                       @Ensures({ (0..<a.length).every { a[it] == orig[a.length - 1 - it] } && a.count(v) == c })
                       int[] reverse(int[] orig, int v, int c) {
                           int lo = 0
                           int hi = a.length - 1
                           @Invariant({ 0 <= lo && lo + hi == a.length - 1 && lo <= hi + 1 &&
                                        (0..<lo).every { a[it] == orig[a.length - 1 - it] } &&
                                        (0..<lo).every { a[a.length - 1 - it] == orig[it] } &&
                                        (lo..<a.length - lo).every { a[it] == orig[it] } &&
                                        a.count(v) == c })
                           @Decreases({ hi - lo + 1 })
                           while (lo < hi) {
                               swap(lo, hi, v)
                               lo = lo + 1
                               hi = hi - 1
                           }
                           return a
                       }
                   }''')],
        // Teeth: a "reverse" that walks the indices inward but FORGETS to swap leaves the array unchanged, so the
        // swapped-prefix invariant (a[k] == orig[n-1-k]) can't be re-established — preservation refutes.
        [group: 'P167 reverse', name: 'reverse that forgets to swap refutes', expect: 'Cannot prove loop invariant',
         src: tc('''class C {
                       int[] a
                       @Requires({ orig.length == a.length && (0..<a.length).every { a[it] == orig[it] } })
                       @Modifies({ this.a })
                       @Ensures({ (0..<a.length).every { a[it] == orig[a.length - 1 - it] } })
                       int[] reverse(int[] orig) {
                           int lo = 0
                           int hi = a.length - 1
                           @Invariant({ 0 <= lo && lo + hi == a.length - 1 && lo <= hi + 1 &&
                                        (0..<lo).every { a[it] == orig[a.length - 1 - it] } &&
                                        (0..<lo).every { a[a.length - 1 - it] == orig[it] } &&
                                        (lo..<a.length - lo).every { a[it] == orig[it] } })
                           @Decreases({ hi - lo + 1 })
                           while (lo < hi) {
                               lo = lo + 1     // BUG: never swaps a[lo] with a[hi]
                               hi = hi - 1
                           }
                           return a
                       }
                   }''')],
    ]
}
