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

/** 'P112 dupletExcept' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G225_p112_dupletexcept {

    static final List<Map> CASES = [
        // ---------- P112 Duplets: dupletExcept (exclusion-totality search) ----------
        // The second-pass engine of the full two-pair Duplets: find a duplicate pair whose VALUE differs from
        // an excluded `except`, with totality — P111 plus the `a[i] != except` conjunct threaded through the
        // existential precondition, the nested ∀∀ "no qualifying duplet found yet" invariant, and the exit
        // guard. (The full two-pass `duplets` that composes this with `duplet` needs inter-procedural tuple
        // results — binding a local to a tuple-returning call and using its slots — a separate gap; see
        // ROADMAP Phase 112.)
        [group: 'P112 dupletExcept', name: 'dupletExcept totality verifies', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && (0..<a.length).any { int p -> (p + 1..<a.length).any { int q -> a[p] == a[q] && a[p] != except } } })
                        @Ensures({ 0 <= result.v1 && result.v1 < result.v2 && result.v2 < a.length && a[result.v1] == a[result.v2] && a[result.v1] != except })
                        static Tuple2<Integer, Integer> dupletExcept(int[] a, int except) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length &&
                                (0..<i).every { int p -> (p + 1..<a.length).every { int q -> a[p] != a[q] || a[p] == except } } })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                int j = i + 1
                                @Invariant({ 0 <= i && i < a.length && i + 1 <= j && j <= a.length &&
                                    (0..<i).every { int p -> (p + 1..<a.length).every { int q -> a[p] != a[q] || a[p] == except } } &&
                                    (i + 1..<j).every { int q -> a[i] != a[q] || a[i] == except } })
                                @Decreases({ a.length - j })
                                while (j < a.length) {
                                    if (a[i] == a[j] && a[i] != except) return Tuple.tuple(i, j)
                                    j = j + 1
                                }
                                i = i + 1
                            }
                            return Tuple.tuple(-1, -1)
                        }
                    }''')],
        // Non-vacuity control: drop the existential precondition; the sentinel fall-through is then reachable
        // and violates the sentinel-free postcondition, so it must refute (the existential is load-bearing).
        [group: 'P112 dupletExcept', name: 'without existential refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ 0 <= result.v1 && result.v1 < result.v2 && result.v2 < a.length && a[result.v1] == a[result.v2] && a[result.v1] != except })
                        static Tuple2<Integer, Integer> dupletExcept(int[] a, int except) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length &&
                                (0..<i).every { int p -> (p + 1..<a.length).every { int q -> a[p] != a[q] || a[p] == except } } })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                int j = i + 1
                                @Invariant({ 0 <= i && i < a.length && i + 1 <= j && j <= a.length &&
                                    (0..<i).every { int p -> (p + 1..<a.length).every { int q -> a[p] != a[q] || a[p] == except } } &&
                                    (i + 1..<j).every { int q -> a[i] != a[q] || a[i] == except } })
                                @Decreases({ a.length - j })
                                while (j < a.length) {
                                    if (a[i] == a[j] && a[i] != except) return Tuple.tuple(i, j)
                                    j = j + 1
                                }
                                i = i + 1
                            }
                            return Tuple.tuple(-1, -1)
                        }
                    }''')],
    ]
}
