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

/** 'P208 merge' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G283_p208_merge {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Merge of two sorted arrays (math-comp path.v\'s merge, mergesort\'s heart): the classic three-sequential-loop implementation proven SORTED (two-var prefix invariants + frontier bounds, input sortedness restated per loop) AND COUNT-PRESERVING for a symbolic value (the new prefix-count oracle r[0..<k].count(v), with base/step axioms and a quantified range-store law). Facts crossing loop boundaries ride the invariants — a later loop restates what it needs, including guarded frontier facts that are vacuous while it runs but carry the no-op path. Teeth: picking the larger element first breaks the sorted invariant; storing a wrong value breaks the count invariant; the prefix-count oracle is pinned in isolation with its own refute twin.'

    static final List<Map> CASES = [

        // ---------- Phase 208: merge — sortedness + permutation over three sequential loops ----------
        [group: 'P208 merge', name: 'merge: sorted and count-preserving (full spec)', ok: true,
         src: tc('''class C {
                       @Requires({ a != null && b != null && r != null && r.length == a.length + b.length &&
                                   (0..<a.length).every { int x -> (x + 1..<a.length).every { int y -> a[x] <= a[y] } } &&
                                   (0..<b.length).every { int x -> (x + 1..<b.length).every { int y -> b[x] <= b[y] } } })
                       @Ensures({ (0..<r.length - 1).every { r[it] <= r[it + 1] } &&
                                  r[0..<r.length].count(v) == a[0..<a.length].count(v) + b[0..<b.length].count(v) })
                       static int[] merge(int[] a, int[] b, int[] r, int v) {
                           int i = 0
                           int j = 0
                           int k = 0
                           @Invariant({ 0 <= i && i <= a.length && 0 <= j && j <= b.length && k == i + j &&
                                        r.length == a.length + b.length &&
                                        (0..<a.length).every { int x -> (x + 1..<a.length).every { int y -> a[x] <= a[y] } } &&
                                        (0..<b.length).every { int x -> (x + 1..<b.length).every { int y -> b[x] <= b[y] } } &&
                                        (0..<k).every { int x -> (x + 1..<k).every { int y -> r[x] <= r[y] } } &&
                                        (i < a.length ==> (0..<k).every { int x -> r[x] <= a[i] }) &&
                                        (j < b.length ==> (0..<k).every { int x -> r[x] <= b[j] }) &&
                                        r[0..<k].count(v) == a[0..<i].count(v) + b[0..<j].count(v) })
                           @Decreases({ a.length + b.length - k })
                           while (i < a.length && j < b.length) {
                               if (a[i] <= b[j]) { r[k] = a[i]; i = i + 1 } else { r[k] = b[j]; j = j + 1 }
                               k = k + 1
                           }
                           @Invariant({ 0 <= i && i <= a.length && 0 <= j && j <= b.length && k == i + j &&
                                        r.length == a.length + b.length &&
                                        (i < a.length ==> j == b.length) &&
                                        (0..<a.length).every { int x -> (x + 1..<a.length).every { int y -> a[x] <= a[y] } } &&
                                        (0..<k).every { int x -> (x + 1..<k).every { int y -> r[x] <= r[y] } } &&
                                        (i < a.length ==> (0..<k).every { int x -> r[x] <= a[i] }) &&
                                        (j < b.length ==> (0..<k).every { int x -> r[x] <= b[j] }) &&
                                        r[0..<k].count(v) == a[0..<i].count(v) + b[0..<j].count(v) })
                           @Decreases({ a.length - i })
                           while (i < a.length) {
                               r[k] = a[i]
                               i = i + 1
                               k = k + 1
                           }
                           @Invariant({ 0 <= j && j <= b.length && i == a.length && k == i + j &&
                                        r.length == a.length + b.length &&
                                        (0..<b.length).every { int x -> (x + 1..<b.length).every { int y -> b[x] <= b[y] } } &&
                                        (0..<k).every { int x -> (x + 1..<k).every { int y -> r[x] <= r[y] } } &&
                                        (j < b.length ==> (0..<k).every { int x -> r[x] <= b[j] }) &&
                                        r[0..<k].count(v) == a[0..<i].count(v) + b[0..<j].count(v) })
                           @Decreases({ b.length - j })
                           while (j < b.length) {
                               r[k] = b[j]
                               j = j + 1
                               k = k + 1
                           }
                           return r
                       }
                   }''')],
        // Teeth (sortedness): picking the LARGER element first — the sorted-prefix invariant refutes
        // (count layer stripped so the VC is quantifier-light and the refutation is crisp).
        [group: 'P208 merge', name: 'picking the larger element first refutes', expect: 'Cannot prove loop invariant',
         src: tc('''class C {
                       @Requires({ a != null && b != null && r != null && r.length == a.length + b.length &&
                                   (0..<a.length).every { int x -> (x + 1..<a.length).every { int y -> a[x] <= a[y] } } &&
                                   (0..<b.length).every { int x -> (x + 1..<b.length).every { int y -> b[x] <= b[y] } } })
                       @Ensures({ (0..<r.length - 1).every { r[it] <= r[it + 1] } })
                       static int[] merge(int[] a, int[] b, int[] r) {
                           int i = 0
                           int j = 0
                           int k = 0
                           @Invariant({ 0 <= i && i <= a.length && 0 <= j && j <= b.length && k == i + j &&
                                        r.length == a.length + b.length &&
                                        (0..<a.length).every { int x -> (x + 1..<a.length).every { int y -> a[x] <= a[y] } } &&
                                        (0..<b.length).every { int x -> (x + 1..<b.length).every { int y -> b[x] <= b[y] } } &&
                                        (0..<k).every { int x -> (x + 1..<k).every { int y -> r[x] <= r[y] } } &&
                                        (i < a.length ==> (0..<k).every { int x -> r[x] <= a[i] }) &&
                                        (j < b.length ==> (0..<k).every { int x -> r[x] <= b[j] }) })
                           @Decreases({ a.length + b.length - k })
                           while (i < a.length && j < b.length) {
                               if (a[i] >= b[j]) { r[k] = a[i]; i = i + 1 } else { r[k] = b[j]; j = j + 1 }
                               k = k + 1
                           }
                           @Invariant({ 0 <= i && i <= a.length && 0 <= j && j <= b.length && k == i + j &&
                                        r.length == a.length + b.length &&
                                        (i < a.length ==> j == b.length) &&
                                        (0..<a.length).every { int x -> (x + 1..<a.length).every { int y -> a[x] <= a[y] } } &&
                                        (0..<k).every { int x -> (x + 1..<k).every { int y -> r[x] <= r[y] } } &&
                                        (i < a.length ==> (0..<k).every { int x -> r[x] <= a[i] }) &&
                                        (j < b.length ==> (0..<k).every { int x -> r[x] <= b[j] }) })
                           @Decreases({ a.length - i })
                           while (i < a.length) {
                               r[k] = a[i]
                               i = i + 1
                               k = k + 1
                           }
                           @Invariant({ 0 <= j && j <= b.length && i == a.length && k == i + j &&
                                        r.length == a.length + b.length &&
                                        (0..<b.length).every { int x -> (x + 1..<b.length).every { int y -> b[x] <= b[y] } } &&
                                        (0..<k).every { int x -> (x + 1..<k).every { int y -> r[x] <= r[y] } } &&
                                        (j < b.length ==> (0..<k).every { int x -> r[x] <= b[j] }) })
                           @Decreases({ b.length - j })
                           while (j < b.length) {
                               r[k] = b[j]
                               j = j + 1
                               k = k + 1
                           }
                           return r
                       }
                   }''')],
        // Teeth (permutation): storing a corrupted value — the count invariant refutes.
        // (Canary form: refuting under the quantified count axioms needs an MBQI model and can time
        // out — 'invariant' matches both honest outcomes; a clean verify fails the case loudly.)
        [group: 'P208 merge', name: 'storing a corrupted value never preserves the count (canary)', expect: 'invariant',
         src: tc('''class C {
                       @Requires({ a != null && b != null && r != null && r.length == a.length + b.length &&
                                   (0..<a.length).every { int x -> (x + 1..<a.length).every { int y -> a[x] <= a[y] } } &&
                                   (0..<b.length).every { int x -> (x + 1..<b.length).every { int y -> b[x] <= b[y] } } })
                       @Ensures({ (0..<r.length - 1).every { r[it] <= r[it + 1] } &&
                                  r[0..<r.length].count(v) == a[0..<a.length].count(v) + b[0..<b.length].count(v) })
                       static int[] merge(int[] a, int[] b, int[] r, int v) {
                           int i = 0
                           int j = 0
                           int k = 0
                           @Invariant({ 0 <= i && i <= a.length && 0 <= j && j <= b.length && k == i + j &&
                                        r.length == a.length + b.length &&
                                        (0..<a.length).every { int x -> (x + 1..<a.length).every { int y -> a[x] <= a[y] } } &&
                                        (0..<b.length).every { int x -> (x + 1..<b.length).every { int y -> b[x] <= b[y] } } &&
                                        (0..<k).every { int x -> (x + 1..<k).every { int y -> r[x] <= r[y] } } &&
                                        (i < a.length ==> (0..<k).every { int x -> r[x] <= a[i] }) &&
                                        (j < b.length ==> (0..<k).every { int x -> r[x] <= b[j] }) &&
                                        r[0..<k].count(v) == a[0..<i].count(v) + b[0..<j].count(v) })
                           @Decreases({ a.length + b.length - k })
                           while (i < a.length && j < b.length) {
                               if (a[i] <= b[j]) { r[k] = a[i] + 1; i = i + 1 } else { r[k] = b[j]; j = j + 1 }
                               k = k + 1
                           }
                           @Invariant({ 0 <= i && i <= a.length && 0 <= j && j <= b.length && k == i + j &&
                                        r.length == a.length + b.length &&
                                        (i < a.length ==> j == b.length) &&
                                        (0..<a.length).every { int x -> (x + 1..<a.length).every { int y -> a[x] <= a[y] } } &&
                                        (0..<k).every { int x -> (x + 1..<k).every { int y -> r[x] <= r[y] } } &&
                                        (i < a.length ==> (0..<k).every { int x -> r[x] <= a[i] }) &&
                                        (j < b.length ==> (0..<k).every { int x -> r[x] <= b[j] }) &&
                                        r[0..<k].count(v) == a[0..<i].count(v) + b[0..<j].count(v) })
                           @Decreases({ a.length - i })
                           while (i < a.length) {
                               r[k] = a[i]
                               i = i + 1
                               k = k + 1
                           }
                           @Invariant({ 0 <= j && j <= b.length && i == a.length && k == i + j &&
                                        r.length == a.length + b.length &&
                                        (0..<b.length).every { int x -> (x + 1..<b.length).every { int y -> b[x] <= b[y] } } &&
                                        (0..<k).every { int x -> (x + 1..<k).every { int y -> r[x] <= r[y] } } &&
                                        (j < b.length ==> (0..<k).every { int x -> r[x] <= b[j] }) &&
                                        r[0..<k].count(v) == a[0..<i].count(v) + b[0..<j].count(v) })
                           @Decreases({ b.length - j })
                           while (j < b.length) {
                               r[k] = b[j]
                               j = j + 1
                               k = k + 1
                           }
                           return r
                       }
                   }''')],
        // The prefix-count oracle in isolation: a fill loop carries r[0..<k].count(v).
        [group: 'P208 merge', name: 'prefix-count oracle: fill loop carries the count', ok: true,
         src: tc('''class C {
                       @Requires({ r != null })
                       @Ensures({ r[0..<r.length].count(v) == (v == c ? r.length : 0) })
                       static int[] fill(int[] r, int c, int v) {
                           int k = 0
                           @Invariant({ 0 <= k && k <= r.length &&
                                        r[0..<k].count(v) == (v == c ? k : 0) })
                           @Decreases({ r.length - k })
                           while (k < r.length) {
                               r[k] = c
                               k = k + 1
                           }
                           return r
                       }
                   }''')],
        [group: 'P208 merge', name: 'off-by-one count claim never proves (canary)', expect: 'postcondition of fill',
         src: tc('''class C {
                       @Requires({ r != null })
                       @Ensures({ r[0..<r.length].count(v) == (v == c ? r.length + 1 : 0) })
                       static int[] fill(int[] r, int c, int v) {
                           int k = 0
                           @Invariant({ 0 <= k && k <= r.length &&
                                        r[0..<k].count(v) == (v == c ? k : 0) })
                           @Decreases({ r.length - k })
                           while (k < r.length) {
                               r[k] = c
                               k = k + 1
                           }
                           return r
                       }
                   }''')],
    ]
}
