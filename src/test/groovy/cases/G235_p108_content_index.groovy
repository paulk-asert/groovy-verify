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

/** 'P108 content-index' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G235_p108_content_index {

    static final List<Map> CASES = [
        // ---------- P108 content-dependent array index bounds inside loops ----------
        // A data-dependent index `b[a[k]]` (the index is itself an array read) is bounded by the value-range
        // quantifier `∀q. 0 ≤ a[q] < b.length`, not by index arithmetic. Phase 108 keeps that quantifier in
        // scope for the loop-body bounds discharge (the Phase-91b strip now applies only to arithmetic
        // indices), so gather / scatter / histogram loops verify. The same discharge already worked outside a
        // loop; this closes the in-loop case. (Motivated by the FoVeOOS Duplets example.)
        [group: 'P108 content-index', name: 'gather read b[a[k]] in a loop', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && b != null && (0..<a.length).every { int q -> 0 <= a[q] && a[q] < b.length } })
                        static int gather(int[] a, int[] b) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= a.length && (0..<a.length).every { int q -> 0 <= a[q] && a[q] < b.length } })
                            @Decreases({ a.length - k })
                            while (k < a.length) { s = b[a[k]]; k = k + 1 }
                            return s
                        }
                    }''')],
        // Scatter / histogram: the *write* index is content-dependent too — `count[a[k]] = count[a[k]] + 1`.
        [group: 'P108 content-index', name: 'histogram store count[a[k]] in a loop', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && count != null && (0..<a.length).every { int q -> 0 <= a[q] && a[q] < count.length } })
                        static int[] hist(int[] a, int[] count) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= a.length && (0..<a.length).every { int q -> 0 <= a[q] && a[q] < count.length } })
                            @Decreases({ a.length - k })
                            while (k < a.length) { count[a[k]] = count[a[k]] + 1; k = k + 1 }
                            return count
                        }
                    }''')],
        // Refute control: drop the value-range and the data-dependent index bound genuinely can't be proven.
        [group: 'P108 content-index', name: 'missing value-range refuted', expect: 'IndexOutOfBounds',
         src: tc('''class C {
                        @Requires({ a != null && b != null })
                        static int gather(int[] a, int[] b) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= a.length })
                            @Decreases({ a.length - k })
                            while (k < a.length) { s = b[a[k]]; k = k + 1 }
                            return s
                        }
                    }''')],
    ]
}
