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

/** 'P111 Duplets-totality' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G232_p111_duplets_totality {

    static final List<Map> CASES = [
        // ---------- P111 Duplets totality (find-given-exists, no engine change) ----------
        // Strengthens the Phase-110 partial-correctness duplet to TOTALITY: with a sentinel-free postcondition
        // and an *existential* precondition (a duplet exists), the verifier must prove the search returns a
        // real duplet — i.e. the sentinel fall-through is infeasible. That rests on nested ∀∀ "no-duplet-found-
        // yet" loop invariants (the outer one extended past the inner loop's completion fact each iteration),
        // and at loop exit the universal "no duplet anywhere" contradicts the existential precondition (Z3
        // instantiates the universal at the existential's witness). All on the existing quantifier + nested-
        // loop machinery — no new engine code; the Phase 108–110 fixes already made the duplet expressible.
        [group: 'P111 Duplets-totality', name: 'duplet totality verifies', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && (0..<a.length).any { int p -> (p + 1..<a.length).any { int q -> a[p] == a[q] } } })
                        @Ensures({ 0 <= result.v1 && result.v1 < result.v2 && result.v2 < a.length && a[result.v1] == a[result.v2] })
                        static Tuple2<Integer, Integer> duplet(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length &&
                                (0..<i).every { int p -> (p + 1..<a.length).every { int q -> a[p] != a[q] } } })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                int j = i + 1
                                @Invariant({ 0 <= i && i < a.length && i + 1 <= j && j <= a.length &&
                                    (0..<i).every { int p -> (p + 1..<a.length).every { int q -> a[p] != a[q] } } &&
                                    (i + 1..<j).every { int q -> a[i] != a[q] } })
                                @Decreases({ a.length - j })
                                while (j < a.length) {
                                    if (a[i] == a[j]) return Tuple.tuple(i, j)
                                    j = j + 1
                                }
                                i = i + 1
                            }
                            return Tuple.tuple(-1, -1)
                        }
                    }''')],
        // Non-vacuity control: DROP the existential precondition. Now the fall-through (empty / no-duplet
        // array → sentinel) is reachable and violates the sentinel-free postcondition, so it MUST refute.
        // If this still passed, the totality proof wouldn't really be using the existential.
        [group: 'P111 Duplets-totality', name: 'totality without existential refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ 0 <= result.v1 && result.v1 < result.v2 && result.v2 < a.length && a[result.v1] == a[result.v2] })
                        static Tuple2<Integer, Integer> duplet(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length &&
                                (0..<i).every { int p -> (p + 1..<a.length).every { int q -> a[p] != a[q] } } })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                int j = i + 1
                                @Invariant({ 0 <= i && i < a.length && i + 1 <= j && j <= a.length &&
                                    (0..<i).every { int p -> (p + 1..<a.length).every { int q -> a[p] != a[q] } } &&
                                    (i + 1..<j).every { int q -> a[i] != a[q] } })
                                @Decreases({ a.length - j })
                                while (j < a.length) {
                                    if (a[i] == a[j]) return Tuple.tuple(i, j)
                                    j = j + 1
                                }
                                i = i + 1
                            }
                            return Tuple.tuple(-1, -1)
                        }
                    }''')],
    ]
}
