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

/** 'P7 lemmas' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G053_p7_lemmas {

    static final List<Map> CASES = [

        // ---------- Phase 7 (standalone lemmas): void methods + self-IH + standalone calls ----------
        // Machinery: a void, self-recursive method verifies (void paths + standalone self-call IH + termination).
        [group: 'P7 lemmas', name: 'void recursive method verified', ok: true,
         src: tc('''class C {
                       @Requires({ n >= 0 })
                       @Ensures({ n >= 0 })
                       @Decreases({ n })
                       static void countDown(int n) {
                           if (n > 0) countDown(n - 1)
                       }
                   }''')],
        // Load-bearing lemma: sortedness transitivity, proved by induction on j - i.
        [group: 'P7 lemmas', name: 'sortedness transitivity lemma verified', ok: true,
         src: tc('''class C {
                       @Requires({ Forall.range(0, a.length - 1, { k -> a[k] <= a[k + 1] }) && 0 <= i && i <= j && j < a.length })
                       @Ensures({ a[i] <= a[j] })
                       @Decreases({ j - i })
                       static void leSorted(int[] a, int i, int j) {
                           if (i < j) leSorted(a, i + 1, j)
                       }
                   }''')],
        // Using the lemma: a standalone call injects a[p] <= a[q], proving the postcondition.
        [group: 'P7 lemmas', name: 'standalone lemma call used', ok: true,
         src: tc('''class C {
                       @Requires({ Forall.range(0, a.length - 1, { k -> a[k] <= a[k + 1] }) && 0 <= i && i <= j && j < a.length })
                       @Ensures({ a[i] <= a[j] })
                       @Decreases({ j - i })
                       static void leSorted(int[] a, int i, int j) {
                           if (i < j) leSorted(a, i + 1, j)
                       }
                       @Requires({ Forall.range(0, a.length - 1, { k -> a[k] <= a[k + 1] }) && 0 <= p && p <= q && q < a.length })
                       @Ensures({ result <= 0 })
                       static int diff(int[] a, int p, int q) {
                           leSorted(a, p, q)
                           return a[p] - a[q]
                       }
                   }''')],
        // A void lemma whose measure does not decrease → termination refuted.
        [group: 'P7 lemmas', name: 'void lemma non-decreasing refuted', expect: 'recursion measure',
         src: tc('''class C {
                       @Decreases({ j - i })
                       static void bad(int[] a, int i, int j) {
                           if (i < j) bad(a, i, j)
                       }
                   }''')],
    ]
}
