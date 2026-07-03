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

/** 'P197 any-N liveness' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G272_p197_anyn_liveness {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Leino\'s ticket lock, the any-N frontier: the trace loop proves. advanceTo walks a SYMBOLIC number of serving-advance rounds by recursion on the round prefix (@Decreases m), instantiating a NESTED bounded quantifier (per-round window stability over witness-function bounds) at each step; anyNLiveness composes it with the frame lemmas and the Phase-174 base case, so a waiter at ANY measure k — hence any process count N — reaches Eating, given the per-round advance witnesses and a final fairness witness. Teeth: one advance short refutes; a broken round window refutes the walk.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — abstract-carrier laws: higher-order/monadic shapes beyond the grid'

    static final List<Map> CASES = [

        // ---------- Phase 197: the any-N trace loop — Leino's Liveness lemma for a symbolic measure ----------
        // The arithmetic spine: a waiter framed across a window in which serving advanced k times (net)
        // lands at measure 0 — for a SYMBOLIC k. What is specific to two processes in Phase 175 (the ≤ 1
        // measure bound making liveness a two-case split) is gone: k is any natural.
        [group: 'P197 any-N liveness', name: 'k-fold measure reduction + base case (symbolic k)', ok: true,
         src: tc('''class AnyN {
                        @Requires({ n <= u && (n..<u).every { int i -> csAF(i + 1) == csAF(i) && tAF(i + 1) == tAF(i) } })
                        @Ensures({ csAF(u) == csAF(n) && tAF(u) == tAF(n) })
                        @Decreases({ u - n })
                        static void frame(Function<Integer,Integer> csAF, Function<Integer,Integer> tAF, int n, int u) {
                            if (n < u) frame(csAF, tAF, n + 1, u)
                        }
                        @Requires({ n <= u && (n..<u).every { int i -> servingF(i + 1) == servingF(i) } })
                        @Ensures({ servingF(u) == servingF(n) })
                        @Decreases({ u - n })
                        static void stableServing(Function<Integer,Integer> servingF, int n, int u) {
                            if (n < u) stableServing(servingF, n + 1, u)
                        }
                        @Requires({ n <= u && k >= 0 &&
                            csAF(n) == 1 && tAF(n) == servingF(n) + k &&
                            (n..<u).every { int i -> csAF(i + 1) == csAF(i) && tAF(i + 1) == tAF(i) } &&
                            servingF(u) == servingF(n) + k })
                        @Ensures({ csAF(u) == 1 && tAF(u) == servingF(u) })
                        static void reduceMeasureK(Function<Integer,Integer> csAF, Function<Integer,Integer> tAF,
                                                   Function<Integer,Integer> servingF, int n, int u, int k) {
                            frame(csAF, tAF, n, u)
                        }
                        @Requires({ n <= u && schedF(u) == 0 &&
                            csAF(n) == 1 && tAF(n) == servingF(n) &&
                            (n..<u).every { int i -> csAF(i + 1) == csAF(i) && tAF(i + 1) == tAF(i) } &&
                            (n..<u).every { int i -> servingF(i + 1) == servingF(i) } &&
                            ((schedF(u) == 0 && csAF(u) == 1 && tAF(u) == servingF(u)) ==> csAF(u + 1) == 2) })
                        @Ensures({ csAF(u + 1) == 2 })
                        static void baseEats(Function<Integer,Integer> csAF, Function<Integer,Integer> tAF,
                                             Function<Integer,Integer> servingF, Function<Integer,Integer> schedF, int n, int u) {
                            frame(csAF, tAF, n, u)
                            stableServing(servingF, n, u)
                        }
                        @Requires({ n <= u && u <= w && k >= 0 && schedF(w) == 0 &&
                            csAF(n) == 1 && tAF(n) == servingF(n) + k &&
                            (n..<u).every { int i -> csAF(i + 1) == csAF(i) && tAF(i + 1) == tAF(i) } &&
                            servingF(u) == servingF(n) + k &&
                            (u..<w).every { int i -> csAF(i + 1) == csAF(i) && tAF(i + 1) == tAF(i) } &&
                            (u..<w).every { int i -> servingF(i + 1) == servingF(i) } &&
                            ((schedF(w) == 0 && csAF(w) == 1 && tAF(w) == servingF(w)) ==> csAF(w + 1) == 2) })
                        @Ensures({ csAF(w + 1) == 2 })
                        static void anyNEats(Function<Integer,Integer> csAF, Function<Integer,Integer> tAF,
                                             Function<Integer,Integer> servingF, Function<Integer,Integer> schedF,
                                             int n, int u, int w, int k) {
                            reduceMeasureK(csAF, tAF, servingF, n, u, k)
                            baseEats(csAF, tAF, servingF, schedF, u, w)
                        }
                    }''')],
        // Teeth: one advance short (serving moved k-1 times) — the waiter never reaches the served
        // ticket, and the reduction's postcondition refutes.
        [group: 'P197 any-N liveness', name: 'reduction refutes when one advance short', expect: 'Cannot prove postcondition',
         src: tc('''class AnyNBroken {
                        @Requires({ n <= u && (n..<u).every { int i -> csAF(i + 1) == csAF(i) && tAF(i + 1) == tAF(i) } })
                        @Ensures({ csAF(u) == csAF(n) && tAF(u) == tAF(n) })
                        @Decreases({ u - n })
                        static void frame(Function<Integer,Integer> csAF, Function<Integer,Integer> tAF, int n, int u) {
                            if (n < u) frame(csAF, tAF, n + 1, u)
                        }
                        @Requires({ n <= u && k >= 1 &&
                            csAF(n) == 1 && tAF(n) == servingF(n) + k &&
                            (n..<u).every { int i -> csAF(i + 1) == csAF(i) && tAF(i + 1) == tAF(i) } &&
                            servingF(u) == servingF(n) + k - 1 })
                        @Ensures({ csAF(u) == 1 && tAF(u) == servingF(u) })
                        static void reduceMeasureK(Function<Integer,Integer> csAF, Function<Integer,Integer> tAF,
                                                   Function<Integer,Integer> servingF, int n, int u, int k) {
                            frame(csAF, tAF, n, u)
                        }
                    }''')],
        // The nested-quantifier ingredient, pinned load-bearing: a per-round window fact — an every over
        // witness-function bounds INSIDE an every over rounds — is instantiated to prove a window equality.
        [group: 'P197 any-N liveness', name: 'nested every over witness-function bounds is load-bearing', ok: true,
         src: tc('''class NestedQ {
                        @Requires({ vF != null && aF != null && k == 1 && vF(0) == 2 && vF(1) == 3 &&
                            (0..<k).every { int j -> (vF(j)..<vF(j + 1)).every { int i -> aF(i + 1) == aF(i) } } })
                        @Ensures({ aF(3) == aF(2) })
                        static void probe(Function<Integer,Integer> vF, Function<Integer,Integer> aF, int k) {
                        }
                    }''')],
        // THE TRACE LOOP: recursion over a symbolic number of rounds. Global hypotheses: round windows are
        // ordered, serving advances by one at each vF(j), and is stable inside each round window — the
        // last as a NESTED bounded quantifier. advanceTo walks the round prefix m (@Decreases m); each
        // step instantiates the nested hypothesis at j = m-1 to discharge stableServing's window. This is
        // the "recursion over a symbolic number of reductions" Phase 175 named as the remaining frontier.
        [group: 'P197 any-N liveness', name: 'advanceTo: the trace loop over symbolic rounds', ok: true,
         src: tc('''class TraceLoop {
                        @Requires({ servingF != null && n <= u && (n..<u).every { int i -> servingF(i + 1) == servingF(i) } })
                        @Ensures({ servingF(u) == servingF(n) })
                        @Decreases({ u - n })
                        static void stableServing(Function<Integer,Integer> servingF, int n, int u) {
                            if (n < u) stableServing(servingF, n + 1, u)
                        }
                        @Requires({ vF != null && servingF != null && 0 <= m && m <= k &&
                            (0..<k).every { int j -> vF(j) + 1 <= vF(j + 1) } &&
                            (0..<k).every { int j -> servingF(vF(j) + 1) == servingF(vF(j)) + 1 } &&
                            (0..<k).every { int j -> (vF(j) + 1..<vF(j + 1)).every { int i -> servingF(i + 1) == servingF(i) } } })
                        @Ensures({ servingF(vF(m)) == servingF(vF(0)) + m })
                        @Decreases({ m })
                        static void advanceTo(Function<Integer,Integer> vF, Function<Integer,Integer> servingF, int k, int m) {
                            if (m > 0) {
                                advanceTo(vF, servingF, k, m - 1)
                                stableServing(servingF, vF(m - 1) + 1, vF(m))
                            }
                        }
                    }''')],
        // Teeth for the trace loop: a round that does NOT advance serving (the j-th holder never leaves)
        // breaks the walk — the postcondition refutes.
        [group: 'P197 any-N liveness', name: 'trace loop refutes when a round does not advance', expect: 'Cannot prove postcondition',
         src: tc('''class TraceLoopBroken {
                        @Requires({ servingF != null && n <= u && (n..<u).every { int i -> servingF(i + 1) == servingF(i) } })
                        @Ensures({ servingF(u) == servingF(n) })
                        @Decreases({ u - n })
                        static void stableServing(Function<Integer,Integer> servingF, int n, int u) {
                            if (n < u) stableServing(servingF, n + 1, u)
                        }
                        @Requires({ vF != null && servingF != null && 0 <= m && m <= k &&
                            (0..<k).every { int j -> vF(j) + 1 <= vF(j + 1) } &&
                            (0..<k).every { int j -> servingF(vF(j) + 1) == servingF(vF(j)) } &&
                            (0..<k).every { int j -> (vF(j) + 1..<vF(j + 1)).every { int i -> servingF(i + 1) == servingF(i) } } })
                        @Ensures({ servingF(vF(m)) == servingF(vF(0)) + m })
                        @Decreases({ m })
                        static void advanceTo(Function<Integer,Integer> vF, Function<Integer,Integer> servingF, int k, int m) {
                            if (m > 0) {
                                advanceTo(vF, servingF, k, m - 1)
                                stableServing(servingF, vF(m - 1) + 1, vF(m))
                            }
                        }
                    }''')],
    ]
}
