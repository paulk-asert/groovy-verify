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

/** 'P7 recursive sort' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G047_p7_recursive_sort {

    static final List<Map> CASES = [

        // ---------- Phase 7: recursive insertion sort (sortedness, end-to-end) ----------
        // insert places a[i] into the sorted prefix; sort composes it under induction. The driver
        // relies on the @Ensures of the `sort(a, n-1)` call immediately before `insert(a, n-1)`.
        [group: 'P7 recursive sort', name: 'recursive insertion sort (sortedness)', ok: true,
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
                       @Requires({ 0 <= n && n <= a.length })
                       @Ensures({ (0..<n - 1).every { a[it] <= a[it + 1] } })
                       @Decreases({ n })
                       static void sort(int[] a, int n) {
                           if (n > 1) {
                               sort(a, n - 1)
                               insert(a, n - 1)
                           }
                       }
                   }''')],
        // Soundness A: an intervening store invalidates the prefix → insert's precondition must NOT
        // be assumable from the earlier sort (the immediately-preceding statement is the store).
        [group: 'P7 recursive sort', name: 'intervening store breaks precondition', expect: 'Cannot prove precondition',
         src: tc('''class C {
                       @Requires({ 0 <= i && i < a.length && (0..<i - 1).every { a[it] <= a[it + 1] } })
                       @Ensures({ (0..<i).every { a[it] <= a[it + 1] } })
                       @Decreases({ i })
                       static void insert(int[] a, int i) {
                           if (i > 0 && a[i] < a[i - 1]) { int t = a[i]; a[i] = a[i - 1]; a[i - 1] = t; insert(a, i - 1) }
                       }
                       @Requires({ 2 <= n && n <= a.length })
                       @Ensures({ (0..<n - 1).every { a[it] <= a[it + 1] } })
                       @Decreases({ n })
                       static void sort(int[] a, int n) {
                           sort(a, n - 1)
                           a[0] = 999
                           insert(a, n - 1)
                       }
                   }''')],
        // Soundness B: forget to insert → the suffix isn't placed → postcondition must refute.
        [group: 'P7 recursive sort', name: 'missing insert refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ 0 <= n && n <= a.length })
                       @Ensures({ (0..<n - 1).every { a[it] <= a[it + 1] } })
                       @Decreases({ n })
                       static void sort(int[] a, int n) {
                           if (n > 1) { sort(a, n - 1) }
                       }
                   }''')],
    ]
}
