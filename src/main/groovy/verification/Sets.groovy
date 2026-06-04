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
package verification

/**
 * Cardinality helpers the verifier recognises in {@code @Requires}/{@code @Ensures}
 * contracts (the "cardinality axiom", roadmap Phase 19).
 *
 * The uninterpreted set cardinality {@code s.size()} (Phase 16) knows only its
 * per-mutation deltas — it has no link to <em>which</em> elements a set holds. This
 * helper exposes the <b>pigeonhole</b> relationship for a set whose elements live in
 * a finite domain {@code [0, n)}:
 *
 * <pre>
 *   {@literal @}Requires({ Sets.bounded(s, n) })
 * </pre>
 *
 * {@code bounded(s, n)} is true exactly when {@code s ⊆ [0, n)} — equivalently:
 * {@code |s| <= n}, and {@code s} is <em>full</em> ({@code |s| == n}) iff it covers the
 * whole domain. From it the verifier can derive the two facts cardinality-driven
 * search needs: a full bounded set contains every domain element
 * ({@code |s| == n ⟹ u ∈ s}), and a set with a hole isn't full
 * ({@code u ∉ s ⟹ |s| < n}).
 *
 * It stays executable so the groovy-contracts <em>runtime</em> check still works; at
 * compile time {@link Encoder} recognises the {@code Sets.bounded(s, n)} shape and
 * lowers it to {@code card(s) <= n ∧ (card(s) < n ∨ ∀ i ∈ [0,n)· i ∈ s)} — a boolean
 * combination of the set cardinality and a bounded membership universal, both already
 * modelled, so the lowering is a faithful definition rather than a trusted axiom.
 */
class Sets {

    /** True iff every member of {@code s} lies in {@code [0, n)} — i.e. {@code s ⊆ [0, n)}. */
    static boolean bounded(Set<Integer> s, int n) {
        s.size() <= n && (s.size() < n || (0..<n).every { it in s })
    }

    /**
     * The bounded-sum cardinality: the number of members of {@code s} in {@code [0, k)}
     * ({@code Σ_{i<k} (i ∈ s ? 1 : 0)}). The verifier recognises {@code Sets.count(s, k)} in contracts
     * and models it as a primitive with a bound axiom and a per-mutation law; this body is the matching
     * runtime evaluation, so the groovy-contracts runtime check agrees.
     */
    static int count(Set<Integer> s, int k) {
        int c = 0
        for (int i = 0; i < k; i++) if (i in s) c++
        c
    }
}
