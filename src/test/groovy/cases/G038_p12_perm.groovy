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

/** 'P12 perm' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G038_p12_perm {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Permutation reasoning via element multiplicity: a swap preserves the multiset, a copy is not a permutation, insertion sort permutes.'

    static final List<Map> CASES = [

        // ---------- Phase 12: permutation — multiset preserved via per-store count law ----------
        // Building block: a swap preserves a.count(v) for an arbitrary value v (the ghost param) →
        // the array stays a permutation. The two stores' count updates cancel.
        [group: 'P12 perm', name: 'swap preserves count', ok: true,
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= i && i < a.length && 0 <= j && j < a.length })
                       @Ensures({ a.count(v) == old.a.count(v) })
                       void swap(int i, int j, int v) { int t = a[i]; a[i] = a[j]; a[j] = t }
                   }''')],
        // Soundness: a plain copy (not a swap) drops an element → some count changes → refuted.
        [group: 'P12 perm', name: 'copy is not a permutation', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= i && i < a.length && 0 <= j && j < a.length })
                       @Ensures({ a.count(v) == old.a.count(v) })
                       void copy(int i, int j, int v) { a[i] = a[j] }
                   }''')],

        // Composition (now sound, via @Modifies caller-side framing): a recursive insertion sort
        // preserves the multiset — `a.count(v) == old.a.count(v)` for arbitrary v — across the swaps
        // *and* the recursive calls (each call havocs a, then reframes count from the callee's @Ensures
        // with `old.a` bound to the array at the call). Permutation only; sound sortedness-under-havoc
        // additionally needs a prefix bound (see ROADMAP Phase 13).
        [group: 'P12 perm', name: 'recursive insertion sort permutes', ok: true,
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= i && i < a.length })
                       @Modifies({ this.a })
                       @Ensures({ a.count(v) == old.a.count(v) })
                       @Decreases({ i })
                       void insert(int i, int v) {
                           if (i > 0 && a[i] < a[i - 1]) {
                               int t = a[i]; a[i] = a[i - 1]; a[i - 1] = t
                               insert(i - 1, v)
                           }
                       }
                       @Requires({ 0 <= n && n <= a.length })
                       @Modifies({ this.a })
                       @Ensures({ a.count(v) == old.a.count(v) })
                       @Decreases({ n })
                       void sort(int n, int v) {
                           if (n > 1) { sort(n - 1, v); insert(n - 1, v) }
                       }
                   }''')],
        // Soundness (no longer vacuous, now that `old` is bound at the call): an overwriting insert
        // drops an element → permutation refuted.
        [group: 'P12 perm', name: 'overwrite insert breaks permutation', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= i && i < a.length })
                       @Modifies({ this.a })
                       @Ensures({ a.count(v) == old.a.count(v) })
                       @Decreases({ i })
                       void insert(int i, int v) {
                           if (i > 0 && a[i] < a[i - 1]) {
                               a[i - 1] = a[i]
                               insert(i - 1, v)
                           }
                       }
                   }''')],
    ]
}
