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

/** 'P-incdec' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G130_p_incdec {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A side-effecting array index a[i] = ++i / a[i] = i++ snapshots the index and proves bounds; a wrong claim refutes.'

    static final List<Map> CASES = [
        // Phase 127 — a pre-increment in an array-store RHS whose variable also indexes the store (`a[i] = ++i`)
        // snapshots the index before the increment, so the store lands at the old slot. Verifies the fill where
        // a[k] == k + 1 (each slot gets the post-increment value, written at the pre-increment index).
        [group: 'P-incdec', name: 'a[i] = ++i snapshots the index and proves', ok: true,
         src: tc('''class T {
                        @Requires({ n >= 1 })
                        @Ensures({ (0..<n).every { int k -> result[k] == k + 1 } })
                        static int[] fill(int n) {
                            int[] a = new int[n]
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && a.length == n && (0..<i).every { int k -> a[k] == k + 1 } })
                            @Decreases({ n - i })
                            while (i < n) { a[i] = ++i }
                            return a
                        }
                    }''')],
        // The post-increment form (handled by the existing route, value uses the old i) still proves.
        [group: 'P-incdec', name: 'a[i] = i++ still proves', ok: true,
         src: tc('''class T {
                        @Requires({ n >= 1 })
                        @Ensures({ (0..<n).every { int k -> result[k] == k } })
                        static int[] fill(int n) {
                            int[] a = new int[n]
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && a.length == n && (0..<i).every { int k -> a[k] == k } })
                            @Decreases({ n - i })
                            while (i < n) { a[i] = i++ }
                            return a
                        }
                    }''')],
        // Soundness: the snapshot rewrite is faithful, not a free pass — a wrong claim over a[i] = ++i refutes.
        [group: 'P-incdec', name: 'a[i] = ++i with a wrong claim refutes', ok: false, expect: 'Cannot prove',
         src: tc('''class T {
                        @Requires({ n >= 1 })
                        @Ensures({ (0..<n).every { int k -> result[k] == k } })
                        static int[] fill(int n) {
                            int[] a = new int[n]
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && a.length == n && (0..<i).every { int k -> a[k] == k } })
                            @Decreases({ n - i })
                            while (i < n) { a[i] = ++i }
                            return a
                        }
                    }''')],
    ]
}
