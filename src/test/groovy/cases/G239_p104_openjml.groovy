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

/** 'P104 OpenJML' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G239_p104_openjml {

    static final List<Map> CASES = [
        // ---------- P104 OpenJML examples (ported from openjml.org/examples, CC BY-NC) ----------
        // "Max by elimination" — find the index of a maximum by shrinking the window [x, y] from
        // both ends, dropping whichever endpoint is no larger. The loop invariant is *disjunctive*:
        // the running maximum is pinned to whichever of x or y currently holds it.
        [group: 'P104 OpenJML', name: 'max-by-elimination: result indexes a maximum', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ 0 <= result && result < a.length && Forall.range(0, a.length) { int i -> a[i] <= a[result] } })
                        static int max(int[] a) {
                            int x = 0
                            int y = a.length - 1
                            @Invariant({ 0 <= x && x <= y && y < a.length &&
                                ((Forall.range(0, x) { int i -> a[i] <= a[y] } && Forall.range(y + 1, a.length) { int i -> a[i] <= a[y] }) ||
                                 (Forall.range(0, x) { int i -> a[i] <= a[x] } && Forall.range(y + 1, a.length) { int i -> a[i] <= a[x] })) })
                            @Decreases({ y - x })
                            while (x != y) { if (a[x] <= a[y]) x = x + 1 else y = y - 1 }
                            return x
                        }
                    }''')],
        // Soundness control: same proof, but claim `result` indexes a *minimum*. The invariant
        // establishes a[i] <= a[result] (a maximum), so the flipped postcondition must not prove.
        [group: 'P104 OpenJML', name: 'max-by-elimination: false min-claim refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ 0 <= result && result < a.length && Forall.range(0, a.length) { int i -> a[result] <= a[i] } })
                        static int max(int[] a) {
                            int x = 0
                            int y = a.length - 1
                            @Invariant({ 0 <= x && x <= y && y < a.length &&
                                ((Forall.range(0, x) { int i -> a[i] <= a[y] } && Forall.range(y + 1, a.length) { int i -> a[i] <= a[y] }) ||
                                 (Forall.range(0, x) { int i -> a[i] <= a[x] } && Forall.range(y + 1, a.length) { int i -> a[i] <= a[x] })) })
                            @Decreases({ y - x })
                            while (x != y) { if (a[x] <= a[y]) x = x + 1 else y = y - 1 }
                            return x
                        }
                    }''')],
        // "Invert injection" — `a` is an injection of [0,n) into [0,n); build its inverse `b` by the scatter
        // `b[a[k]] = k`, proving the round-trip `∀i. b[a[i]] == i`. The new obligation over Phase 108 (which
        // bounds a content-dependent store) is *functional correctness* of the scatter: preserving
        // `∀i<k. b[a[i]] == i` across `b[a[k]] = k` needs the new write not to clobber an earlier slot — i.e.
        // `a[i] != a[k]` for every i < k — which comes only from instantiating the nested-quantifier injectivity
        // precondition at (i, k). First case where a quantified loop invariant survives a scatter store by
        // e-matching an injectivity hypothesis to defeat aliasing. (OpenJML's full version also carries a `-1`
        // sentinel + biconditional for the M>N case; trimmed here to the square permutation-inverse.)
        [group: 'P104 OpenJML', name: 'invert-injection: scatter builds the inverse under injectivity', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && b != null && n >= 0 && a.length == n && b.length == n &&
                            Forall.range(0, n) { int i -> 0 <= a[i] && a[i] < n } &&
                            Forall.range(0, n) { int i -> Forall.range(i + 1, n) { int j -> a[i] != a[j] } } })
                        @Ensures({ Forall.range(0, n) { int i -> b[a[i]] == i } })
                        static int[] invert(int[] a, int[] b, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n &&
                                Forall.range(0, n) { int q -> 0 <= a[q] && a[q] < n } &&
                                Forall.range(0, k) { int i -> b[a[i]] == i } })
                            @Decreases({ n - k })
                            while (k < n) { b[a[k]] = k; k = k + 1 }
                            return b
                        }
                    }''')],
        // Soundness control: drop the injectivity clause from @Requires. Now two distinct indices i < k may share
        // a[i] == a[k], so the scatter at a[k] can clobber b[a[i]] and the invariant `b[a[i]] == i` is no longer
        // preserved — the proof fails right at invariant preservation. (Injectivity is the load-bearing hypothesis.)
        [group: 'P104 OpenJML', name: 'invert-injection: without injectivity, aliasing refutes', expect: 'Cannot prove loop invariant',
         src: tc('''class C {
                        @Requires({ a != null && b != null && n >= 0 && a.length == n && b.length == n &&
                            Forall.range(0, n) { int i -> 0 <= a[i] && a[i] < n } })
                        @Ensures({ Forall.range(0, n) { int i -> b[a[i]] == i } })
                        static int[] invert(int[] a, int[] b, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n &&
                                Forall.range(0, n) { int q -> 0 <= a[q] && a[q] < n } &&
                                Forall.range(0, k) { int i -> b[a[i]] == i } })
                            @Decreases({ n - k })
                            while (k < n) { b[a[k]] = k; k = k + 1 }
                            return b
                        }
                    }''')],
    ]
}
