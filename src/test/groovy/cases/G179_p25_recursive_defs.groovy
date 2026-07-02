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

/** 'P25 recursive-defs' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G179_p25_recursive_defs {

    static final List<Map> CASES = [

        // ---------- Phase 25: recursive definitions in contracts (the defining-equation upgrade) ----------
        // A recursive contract-free function in a contract is now a shared symbol `f#(args)` carrying its
        // DEFINING EQUATION (bounded depth), so its definition is visible across a lemma boundary — where the
        // old inline-the-body unfolding produced unequal terms at different fuel depths and the induction
        // could not close. (1) COMPLETENESS, full: closure ⇒ EVERY node reachable from a visited node is
        // visited — the inductive `propagate` over the chain `chain(u,d)` (d-step successor) that previously
        // failed. This completes the (b) half flagged in Phase 23.
        [group: 'P25 recursive-defs', name: 'closure ⇒ d-step reachable covered (induction)', ok: true,
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        int n
                        int chain(int u, int d) { d <= 0 ? u : chain(next[u], d - 1) }
                        @Requires({ d >= 0 && 0 <= u && u < n && (u in visited) &&
                                    (0..<n).every { 0 <= next[it] && next[it] < n } &&
                                    (0..<n).every { (it in visited) ==> (next[it] in visited) } })
                        @Ensures({ chain(u, d) in visited })
                        @Decreases({ d })
                        void propagate(int u, int d) {
                            if (d > 0) propagate(next[u], d - 1)
                        }
                    }''')],
        // (2) bcount cross-lemma: a single-expression `bcount` referenced in a lemma's contract, whose bound
        // `0 <= bcount <= k` is proved by induction USING the defining equation (the cross-lemma use the
        // statement-form Phase-20 bcount couldn't support).
        [group: 'P25 recursive-defs', name: 'bcount bound via defining equation', ok: true,
         src: tc('''class C {
                        int bcount(Set<Integer> s, int k) { k <= 0 ? 0 : bcount(s, k - 1) + ((k - 1) in s ? 1 : 0) }
                        @Requires({ k >= 0 })
                        @Ensures({ 0 <= bcount(s, k) && bcount(s, k) <= k })
                        @Decreases({ k })
                        void bcountBound(Set<Integer> s, int k) {
                            if (k > 0) bcountBound(s, k - 1)
                        }
                    }''')],
        // Soundness: the definition is faithful, not vacuous — a too-tight bound (<= k-1) refutes.
        [group: 'P25 recursive-defs', name: 'wrong bcount bound refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        int bcount(Set<Integer> s, int k) { k <= 0 ? 0 : bcount(s, k - 1) + ((k - 1) in s ? 1 : 0) }
                        @Requires({ k >= 0 })
                        @Ensures({ bcount(s, k) <= k - 1 })
                        @Decreases({ k })
                        void bcountBound(Set<Integer> s, int k) {
                            if (k > 0) bcountBound(s, k - 1)
                        }
                    }''')],
    ]
}
