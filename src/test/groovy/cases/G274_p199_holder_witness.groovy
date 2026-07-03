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

/** 'P199 holder witness' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G274_p199_holder_witness {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The KRML260 capstone composition: each liveness round\'s serving-advance is DERIVED, not hypothesized — the round holder hF(j) (nameable since the any-N int indexing) is scheduled at vF(j) by per-round fairness, and the scheduled holder\'s Leave advances serving (the step implication); the trace loop chains the modus ponens per round, and the full holderEats composition takes a waiter at any measure k to Eating. Teeth: an unscheduled holder breaks the derivation; a missing final fairness witness breaks the composition. The remaining construction is pinned as a boundary case: the full time-by-process state needs a two-argument function (BiFunction apply), which skips loudly today.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — abstract-carrier laws: higher-order/monadic shapes beyond the grid'

    static final List<Map> CASES = [

        // ---------- Phase 199: the holder-witness capstone — per-round advances DERIVED from fairness ----------
        // The trace loop with one derivation step inside each round: the holder hF(j) is scheduled at
        // vF(j) (per-round fairness), and a scheduled holder's Leave advances serving (the step
        // implication). Instantiating both at j = m-1 turns Phase 197's hypothesized advance into a
        // modus-ponens conclusion, then the window stability carries it to the next round.
        [group: 'P199 holder witness', name: 'advance derived from scheduled holder (trace loop)', ok: true,
         src: tc('''class HolderLoop {
                        @Requires({ servingF != null && n <= u && (n..<u).every { int i -> servingF(i + 1) == servingF(i) } })
                        @Ensures({ servingF(u) == servingF(n) })
                        @Decreases({ u - n })
                        static void stableServing(Function<Integer,Integer> servingF, int n, int u) {
                            if (n < u) stableServing(servingF, n + 1, u)
                        }
                        @Requires({ vF != null && servingF != null && schedF != null && hF != null && 0 <= m && m <= k &&
                            (0..<k).every { int j -> vF(j) + 1 <= vF(j + 1) } &&
                            (0..<k).every { int j -> schedF(vF(j)) == hF(j) } &&
                            (0..<k).every { int j -> schedF(vF(j)) == hF(j) ==> servingF(vF(j) + 1) == servingF(vF(j)) + 1 } &&
                            (0..<k).every { int j -> (vF(j) + 1..<vF(j + 1)).every { int i -> servingF(i + 1) == servingF(i) } } })
                        @Ensures({ servingF(vF(m)) == servingF(vF(0)) + m })
                        @Decreases({ m })
                        static void advanceDerived(Function<Integer,Integer> vF, Function<Integer,Integer> servingF,
                                                   Function<Integer,Integer> schedF, Function<Integer,Integer> hF, int k, int m) {
                            if (m > 0) {
                                advanceDerived(vF, servingF, schedF, hF, k, m - 1)
                                stableServing(servingF, vF(m - 1) + 1, vF(m))
                            }
                        }
                    }''')],
        // Teeth: drop the per-round fairness conjunct (the holder is never scheduled) — the step
        // implication cannot fire and the derivation refutes.
        [group: 'P199 holder witness', name: 'derivation refutes without the fairness witness', expect: 'Cannot prove postcondition',
         src: tc('''class HolderLoopBroken {
                        @Requires({ servingF != null && n <= u && (n..<u).every { int i -> servingF(i + 1) == servingF(i) } })
                        @Ensures({ servingF(u) == servingF(n) })
                        @Decreases({ u - n })
                        static void stableServing(Function<Integer,Integer> servingF, int n, int u) {
                            if (n < u) stableServing(servingF, n + 1, u)
                        }
                        @Requires({ vF != null && servingF != null && schedF != null && hF != null && 0 <= m && m <= k &&
                            (0..<k).every { int j -> vF(j) + 1 <= vF(j + 1) } &&
                            (0..<k).every { int j -> schedF(vF(j)) == hF(j) ==> servingF(vF(j) + 1) == servingF(vF(j)) + 1 } &&
                            (0..<k).every { int j -> (vF(j) + 1..<vF(j + 1)).every { int i -> servingF(i + 1) == servingF(i) } } })
                        @Ensures({ servingF(vF(m)) == servingF(vF(0)) + m })
                        @Decreases({ m })
                        static void advanceDerived(Function<Integer,Integer> vF, Function<Integer,Integer> servingF,
                                                   Function<Integer,Integer> schedF, Function<Integer,Integer> hF, int k, int m) {
                            if (m > 0) {
                                advanceDerived(vF, servingF, schedF, hF, k, m - 1)
                                stableServing(servingF, vF(m - 1) + 1, vF(m))
                            }
                        }
                    }''')],
        // THE CAPSTONE: waiter A at measure k; k rounds of derived advances bring serving to A's ticket;
        // A framed throughout; A's own fairness witness at w fires the Enter. Hungry-to-Eating for ANY
        // measure — every ingredient of Leino's Liveness lemma, each round's progress derived from a
        // named holder's scheduled Leave.
        [group: 'P199 holder witness', name: 'holderEats: any-measure waiter eats via derived advances', ok: true,
         src: tc('''class HolderEats {
                        @Requires({ csAF != null && tAF != null && n <= u && (n..<u).every { int i -> csAF(i + 1) == csAF(i) && tAF(i + 1) == tAF(i) } })
                        @Ensures({ csAF(u) == csAF(n) && tAF(u) == tAF(n) })
                        @Decreases({ u - n })
                        static void frame(Function<Integer,Integer> csAF, Function<Integer,Integer> tAF, int n, int u) {
                            if (n < u) frame(csAF, tAF, n + 1, u)
                        }
                        @Requires({ servingF != null && n <= u && (n..<u).every { int i -> servingF(i + 1) == servingF(i) } })
                        @Ensures({ servingF(u) == servingF(n) })
                        @Decreases({ u - n })
                        static void stableServing(Function<Integer,Integer> servingF, int n, int u) {
                            if (n < u) stableServing(servingF, n + 1, u)
                        }
                        @Requires({ vF != null && servingF != null && schedF != null && hF != null && 0 <= m && m <= k &&
                            (0..<k).every { int j -> vF(j) + 1 <= vF(j + 1) } &&
                            (0..<k).every { int j -> schedF(vF(j)) == hF(j) } &&
                            (0..<k).every { int j -> schedF(vF(j)) == hF(j) ==> servingF(vF(j) + 1) == servingF(vF(j)) + 1 } &&
                            (0..<k).every { int j -> (vF(j) + 1..<vF(j + 1)).every { int i -> servingF(i + 1) == servingF(i) } } })
                        @Ensures({ servingF(vF(m)) == servingF(vF(0)) + m })
                        @Decreases({ m })
                        static void advanceDerived(Function<Integer,Integer> vF, Function<Integer,Integer> servingF,
                                                   Function<Integer,Integer> schedF, Function<Integer,Integer> hF, int k, int m) {
                            if (m > 0) {
                                advanceDerived(vF, servingF, schedF, hF, k, m - 1)
                                stableServing(servingF, vF(m - 1) + 1, vF(m))
                            }
                        }
                        @Requires({ csAF != null && tAF != null && servingF != null && schedF != null && vF != null && hF != null &&
                            k >= 0 && vF(0) <= vF(k) && vF(k) <= w && schedF(w) == 0 &&
                            csAF(vF(0)) == 1 && tAF(vF(0)) == servingF(vF(0)) + k &&
                            (0..<k).every { int j -> vF(j) + 1 <= vF(j + 1) } &&
                            (0..<k).every { int j -> schedF(vF(j)) == hF(j) } &&
                            (0..<k).every { int j -> schedF(vF(j)) == hF(j) ==> servingF(vF(j) + 1) == servingF(vF(j)) + 1 } &&
                            (0..<k).every { int j -> (vF(j) + 1..<vF(j + 1)).every { int i -> servingF(i + 1) == servingF(i) } } &&
                            (vF(0)..<w).every { int i -> csAF(i + 1) == csAF(i) && tAF(i + 1) == tAF(i) } &&
                            (vF(k)..<w).every { int i -> servingF(i + 1) == servingF(i) } &&
                            ((schedF(w) == 0 && csAF(w) == 1 && tAF(w) == servingF(w)) ==> csAF(w + 1) == 2) })
                        @Ensures({ csAF(w + 1) == 2 })
                        static void holderEats(Function<Integer,Integer> csAF, Function<Integer,Integer> tAF,
                                               Function<Integer,Integer> servingF, Function<Integer,Integer> schedF,
                                               Function<Integer,Integer> vF, Function<Integer,Integer> hF, int k, int w) {
                            advanceDerived(vF, servingF, schedF, hF, k, k)
                            frame(csAF, tAF, vF(0), vF(k))
                            stableServing(servingF, vF(k), w)
                            frame(csAF, tAF, vF(k), w)
                        }
                    }''')],
        // Teeth: without A's own fairness witness at w (schedF(w) == 0 dropped from the step implication's
        // trigger side is trivial — instead drop the ENTER implication entirely), A stays Hungry — refute.
        [group: 'P199 holder witness', name: 'composition refutes without the Enter step', expect: 'Cannot prove postcondition',
         src: tc('''class HolderNoEnter {
                        @Requires({ csAF != null && tAF != null && n <= u && (n..<u).every { int i -> csAF(i + 1) == csAF(i) && tAF(i + 1) == tAF(i) } })
                        @Ensures({ csAF(u) == csAF(n) && tAF(u) == tAF(n) })
                        @Decreases({ u - n })
                        static void frame(Function<Integer,Integer> csAF, Function<Integer,Integer> tAF, int n, int u) {
                            if (n < u) frame(csAF, tAF, n + 1, u)
                        }
                        @Requires({ csAF != null && tAF != null && servingF != null && schedF != null &&
                            n <= w && schedF(w) == 0 &&
                            csAF(n) == 1 && tAF(n) == servingF(n) &&
                            (n..<w).every { int i -> csAF(i + 1) == csAF(i) && tAF(i + 1) == tAF(i) } &&
                            (n..<w).every { int i -> servingF(i + 1) == servingF(i) } })
                        @Ensures({ csAF(w + 1) == 2 })
                        static void baseNoEnter(Function<Integer,Integer> csAF, Function<Integer,Integer> tAF,
                                                Function<Integer,Integer> servingF, Function<Integer,Integer> schedF, int n, int w) {
                            frame(csAF, tAF, n, w)
                        }
                    }''')],
        // The boundary, pinned: the construction beyond this — deriving the STEP IMPLICATION itself from
        // the full transition system — needs the time-by-process state cs(i, r), a two-argument function.
        // BiFunction.apply is outside the fragment today; this pins the loud skip.
        [group: 'P199 holder witness', name: 'two-argument trace state skips loudly (the boundary)', expect: 'outside fragment',
         src: HDR + 'import java.util.function.BiFunction\n' +
              "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class TwoArg {
                        @Requires({ csT != null && csT.apply(0, 0) == 1 })
                        @Ensures({ csT.apply(0, 0) == 1 })
                        static void probe(BiFunction<Integer,Integer,Integer> csT) {}
                    }'''],
    ]
}
