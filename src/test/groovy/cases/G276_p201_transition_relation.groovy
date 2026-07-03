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

/** 'P201 transition relation' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G276_p201_transition_relation {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The KRML260 finale: the ticket lock\'s transition relation spelled over the two-argument state cs(i, r)/tk(i, r), and the liveness chain DERIVED from it end to end — oneRound takes a hungry holder through its scheduled Enter and Leave (frame and stability lemmas recursive, the Enter/Leave steps instantiated from the relation), roundsAdvance runs k such rounds (the trace loop, round-indexed nested windows), and hungryEats finishes with the waiter\'s own Enter: Hungry to Eating for any measure, from IsTrace + fairness witnesses + holder identities alone — the Phase-199 step implication is now a theorem. Teeth: a relation whose Leave does not advance serving refutes the round; an interior eater breaks the stability derivation.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — abstract-carrier laws: higher-order/monadic shapes beyond the grid'

    static final String BIFN = 'import java.util.function.BiFunction\n'

    static final List<Map> CASES = [

        // ---------- Phase 201: the transition relation — the liveness chain derived end to end ----------
        // One round: the holder h, hungry-holding-served at n, scheduled exactly at u (its Enter fires,
        // from the relation) and at v (its Leave fires, advancing serving); framing and stability across
        // the interior windows are the recursive lemmas; no interior eater (mutual exclusion, witnessed).
        [group: 'P201 transition relation', name: 'oneRound: the serving advance is a theorem', ok: true,
         src: HDR + BIFN + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class OneRound {
                        @Requires({ cs != null && tk != null && schedF != null && a <= b &&
                            (a..<b).every { int i -> schedF(i) != h ==> (cs.apply(i + 1, h) == cs.apply(i, h) && tk.apply(i + 1, h) == tk.apply(i, h)) } &&
                            (a..<b).every { int i -> schedF(i) != h } })
                        @Ensures({ cs.apply(b, h) == cs.apply(a, h) && tk.apply(b, h) == tk.apply(a, h) })
                        @Decreases({ b - a })
                        static void holderFrame(BiFunction<Integer,Integer,Integer> cs, BiFunction<Integer,Integer,Integer> tk,
                                                Function<Integer,Integer> schedF, int h, int a, int b) {
                            if (a < b) holderFrame(cs, tk, schedF, h, a + 1, b)
                        }
                        @Requires({ cs != null && servingF != null && schedF != null && a <= b &&
                            (a..<b).every { int i -> cs.apply(i, schedF(i)) != 2 ==> servingF(i + 1) == servingF(i) } &&
                            (a..<b).every { int i -> cs.apply(i, schedF(i)) != 2 } })
                        @Ensures({ servingF(b) == servingF(a) })
                        @Decreases({ b - a })
                        static void stableNoEat(BiFunction<Integer,Integer,Integer> cs, Function<Integer,Integer> servingF,
                                                Function<Integer,Integer> schedF, int a, int b) {
                            if (a < b) stableNoEat(cs, servingF, schedF, a + 1, b)
                        }
                        @Requires({ cs != null && tk != null && servingF != null && schedF != null &&
                            n <= u && u + 1 <= v &&
                            schedF(u) == h && schedF(v) == h &&
                            (n..<u).every { int i -> schedF(i) != h } &&
                            (u + 1..<v).every { int i -> schedF(i) != h } &&
                            (n..<u).every { int i -> cs.apply(i, schedF(i)) != 2 } &&
                            (u + 1..<v).every { int i -> cs.apply(i, schedF(i)) != 2 } &&
                            (n..<v + 1).every { int i -> schedF(i) != h ==> (cs.apply(i + 1, h) == cs.apply(i, h) && tk.apply(i + 1, h) == tk.apply(i, h)) } &&
                            (n..<v + 1).every { int i -> cs.apply(i, schedF(i)) != 2 ==> servingF(i + 1) == servingF(i) } &&
                            (n..<v + 1).every { int i -> cs.apply(i, schedF(i)) == 2 ==> servingF(i + 1) == servingF(i) + 1 } &&
                            (n..<v + 1).every { int i -> (cs.apply(i, schedF(i)) == 1 && tk.apply(i, schedF(i)) == servingF(i)) ==> cs.apply(i + 1, schedF(i)) == 2 } &&
                            (n..<v + 1).every { int i -> tk.apply(i + 1, schedF(i)) == tk.apply(i, schedF(i)) } &&
                            cs.apply(n, h) == 1 && tk.apply(n, h) == servingF(n) })
                        @Ensures({ servingF(v + 1) == servingF(n) + 1 })
                        static void oneRound(BiFunction<Integer,Integer,Integer> cs, BiFunction<Integer,Integer,Integer> tk,
                                             Function<Integer,Integer> servingF, Function<Integer,Integer> schedF,
                                             int h, int n, int u, int v) {
                            holderFrame(cs, tk, schedF, h, n, u)
                            stableNoEat(cs, servingF, schedF, n, u)
                            holderFrame(cs, tk, schedF, h, u + 1, v)
                            stableNoEat(cs, servingF, schedF, u + 1, v)
                        }
                    }'''],
        // Teeth: a relation whose scheduled-eater step does NOT advance serving — the round refutes.
        [group: 'P201 transition relation', name: 'round refutes when Leave does not advance', expect: 'Cannot prove postcondition',
         src: HDR + BIFN + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class OneRoundBroken {
                        @Requires({ cs != null && tk != null && schedF != null && a <= b &&
                            (a..<b).every { int i -> schedF(i) != h ==> (cs.apply(i + 1, h) == cs.apply(i, h) && tk.apply(i + 1, h) == tk.apply(i, h)) } &&
                            (a..<b).every { int i -> schedF(i) != h } })
                        @Ensures({ cs.apply(b, h) == cs.apply(a, h) && tk.apply(b, h) == tk.apply(a, h) })
                        @Decreases({ b - a })
                        static void holderFrame(BiFunction<Integer,Integer,Integer> cs, BiFunction<Integer,Integer,Integer> tk,
                                                Function<Integer,Integer> schedF, int h, int a, int b) {
                            if (a < b) holderFrame(cs, tk, schedF, h, a + 1, b)
                        }
                        @Requires({ cs != null && servingF != null && schedF != null && a <= b &&
                            (a..<b).every { int i -> cs.apply(i, schedF(i)) != 2 ==> servingF(i + 1) == servingF(i) } &&
                            (a..<b).every { int i -> cs.apply(i, schedF(i)) != 2 } })
                        @Ensures({ servingF(b) == servingF(a) })
                        @Decreases({ b - a })
                        static void stableNoEat(BiFunction<Integer,Integer,Integer> cs, Function<Integer,Integer> servingF,
                                                Function<Integer,Integer> schedF, int a, int b) {
                            if (a < b) stableNoEat(cs, servingF, schedF, a + 1, b)
                        }
                        @Requires({ cs != null && tk != null && servingF != null && schedF != null &&
                            n <= u && u + 1 <= v &&
                            schedF(u) == h && schedF(v) == h &&
                            (n..<u).every { int i -> schedF(i) != h } &&
                            (u + 1..<v).every { int i -> schedF(i) != h } &&
                            (n..<u).every { int i -> cs.apply(i, schedF(i)) != 2 } &&
                            (u + 1..<v).every { int i -> cs.apply(i, schedF(i)) != 2 } &&
                            (n..<v + 1).every { int i -> schedF(i) != h ==> (cs.apply(i + 1, h) == cs.apply(i, h) && tk.apply(i + 1, h) == tk.apply(i, h)) } &&
                            (n..<v + 1).every { int i -> cs.apply(i, schedF(i)) != 2 ==> servingF(i + 1) == servingF(i) } &&
                            (n..<v + 1).every { int i -> cs.apply(i, schedF(i)) == 2 ==> servingF(i + 1) == servingF(i) } &&
                            (n..<v + 1).every { int i -> (cs.apply(i, schedF(i)) == 1 && tk.apply(i, schedF(i)) == servingF(i)) ==> cs.apply(i + 1, schedF(i)) == 2 } &&
                            (n..<v + 1).every { int i -> tk.apply(i + 1, schedF(i)) == tk.apply(i, schedF(i)) } &&
                            cs.apply(n, h) == 1 && tk.apply(n, h) == servingF(n) })
                        @Ensures({ servingF(v + 1) == servingF(n) + 1 })
                        static void oneRound(BiFunction<Integer,Integer,Integer> cs, BiFunction<Integer,Integer,Integer> tk,
                                             Function<Integer,Integer> servingF, Function<Integer,Integer> schedF,
                                             int h, int n, int u, int v) {
                            holderFrame(cs, tk, schedF, h, n, u)
                            stableNoEat(cs, servingF, schedF, n, u)
                            holderFrame(cs, tk, schedF, h, u + 1, v)
                            stableNoEat(cs, servingF, schedF, u + 1, v)
                        }
                    }'''],
        // Teeth: an interior eater (the no-eat window dropped) — the stability derivation breaks.
        [group: 'P201 transition relation', name: 'interior eater breaks the stability derivation', expect: 'Cannot prove postcondition',
         src: HDR + BIFN + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class NoEatBroken {
                        @Requires({ cs != null && servingF != null && schedF != null && a <= b &&
                            (a..<b).every { int i -> cs.apply(i, schedF(i)) != 2 ==> servingF(i + 1) == servingF(i) } })
                        @Ensures({ servingF(b) == servingF(a) })
                        @Decreases({ b - a })
                        static void stableNoEat(BiFunction<Integer,Integer,Integer> cs, Function<Integer,Integer> servingF,
                                                Function<Integer,Integer> schedF, int a, int b) {
                            if (a < b) stableNoEat(cs, servingF, schedF, a + 1, b)
                        }
                    }'''],
        // The trace loop over oneRound: k rounds, round-indexed nested windows instantiated at j = m-1.
        [group: 'P201 transition relation', name: 'roundsAdvance: k derived rounds (the trace loop)', ok: true,
         src: HDR + BIFN + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class RoundsAdvance {
                        @Requires({ cs != null && tk != null && schedF != null && a <= b &&
                            (a..<b).every { int i -> schedF(i) != h ==> (cs.apply(i + 1, h) == cs.apply(i, h) && tk.apply(i + 1, h) == tk.apply(i, h)) } &&
                            (a..<b).every { int i -> schedF(i) != h } })
                        @Ensures({ cs.apply(b, h) == cs.apply(a, h) && tk.apply(b, h) == tk.apply(a, h) })
                        @Decreases({ b - a })
                        static void holderFrame(BiFunction<Integer,Integer,Integer> cs, BiFunction<Integer,Integer,Integer> tk,
                                                Function<Integer,Integer> schedF, int h, int a, int b) {
                            if (a < b) holderFrame(cs, tk, schedF, h, a + 1, b)
                        }
                        @Requires({ cs != null && servingF != null && schedF != null && a <= b &&
                            (a..<b).every { int i -> cs.apply(i, schedF(i)) != 2 ==> servingF(i + 1) == servingF(i) } &&
                            (a..<b).every { int i -> cs.apply(i, schedF(i)) != 2 } })
                        @Ensures({ servingF(b) == servingF(a) })
                        @Decreases({ b - a })
                        static void stableNoEat(BiFunction<Integer,Integer,Integer> cs, Function<Integer,Integer> servingF,
                                                Function<Integer,Integer> schedF, int a, int b) {
                            if (a < b) stableNoEat(cs, servingF, schedF, a + 1, b)
                        }
                        @Requires({ cs != null && tk != null && servingF != null && schedF != null &&
                            n <= u && u + 1 <= v &&
                            schedF(u) == h && schedF(v) == h &&
                            (n..<u).every { int i -> schedF(i) != h } &&
                            (u + 1..<v).every { int i -> schedF(i) != h } &&
                            (n..<u).every { int i -> cs.apply(i, schedF(i)) != 2 } &&
                            (u + 1..<v).every { int i -> cs.apply(i, schedF(i)) != 2 } &&
                            (n..<v + 1).every { int i -> schedF(i) != h ==> (cs.apply(i + 1, h) == cs.apply(i, h) && tk.apply(i + 1, h) == tk.apply(i, h)) } &&
                            (n..<v + 1).every { int i -> cs.apply(i, schedF(i)) != 2 ==> servingF(i + 1) == servingF(i) } &&
                            (n..<v + 1).every { int i -> cs.apply(i, schedF(i)) == 2 ==> servingF(i + 1) == servingF(i) + 1 } &&
                            (n..<v + 1).every { int i -> (cs.apply(i, schedF(i)) == 1 && tk.apply(i, schedF(i)) == servingF(i)) ==> cs.apply(i + 1, schedF(i)) == 2 } &&
                            (n..<v + 1).every { int i -> tk.apply(i + 1, schedF(i)) == tk.apply(i, schedF(i)) } &&
                            cs.apply(n, h) == 1 && tk.apply(n, h) == servingF(n) })
                        @Ensures({ servingF(v + 1) == servingF(n) + 1 })
                        static void oneRound(BiFunction<Integer,Integer,Integer> cs, BiFunction<Integer,Integer,Integer> tk,
                                             Function<Integer,Integer> servingF, Function<Integer,Integer> schedF,
                                             int h, int n, int u, int v) {
                            holderFrame(cs, tk, schedF, h, n, u)
                            stableNoEat(cs, servingF, schedF, n, u)
                            holderFrame(cs, tk, schedF, h, u + 1, v)
                            stableNoEat(cs, servingF, schedF, u + 1, v)
                        }
                        @Requires({ cs != null && tk != null && servingF != null && schedF != null &&
                            sF != null && uF != null && vF != null && hF != null &&
                            0 <= m && m <= k &&
                            (0..<k).every { int j -> sF(j) <= uF(j) && uF(j) + 1 <= vF(j) && vF(j) + 1 == sF(j + 1) } &&
                            (0..<k).every { int j -> schedF(uF(j)) == hF(j) && schedF(vF(j)) == hF(j) } &&
                            (0..<k).every { int j -> (sF(j)..<uF(j)).every { int i -> schedF(i) != hF(j) } } &&
                            (0..<k).every { int j -> (uF(j) + 1..<vF(j)).every { int i -> schedF(i) != hF(j) } } &&
                            (0..<k).every { int j -> (sF(j)..<uF(j)).every { int i -> cs.apply(i, schedF(i)) != 2 } } &&
                            (0..<k).every { int j -> (uF(j) + 1..<vF(j)).every { int i -> cs.apply(i, schedF(i)) != 2 } } &&
                            (0..<k).every { int j -> (sF(j)..<vF(j) + 1).every { int i -> schedF(i) != hF(j) ==> (cs.apply(i + 1, hF(j)) == cs.apply(i, hF(j)) && tk.apply(i + 1, hF(j)) == tk.apply(i, hF(j))) } } &&
                            (0..<k).every { int j -> (sF(j)..<vF(j) + 1).every { int i -> cs.apply(i, schedF(i)) != 2 ==> servingF(i + 1) == servingF(i) } } &&
                            (0..<k).every { int j -> (sF(j)..<vF(j) + 1).every { int i -> cs.apply(i, schedF(i)) == 2 ==> servingF(i + 1) == servingF(i) + 1 } } &&
                            (0..<k).every { int j -> (sF(j)..<vF(j) + 1).every { int i -> (cs.apply(i, schedF(i)) == 1 && tk.apply(i, schedF(i)) == servingF(i)) ==> cs.apply(i + 1, schedF(i)) == 2 } } &&
                            (0..<k).every { int j -> (sF(j)..<vF(j) + 1).every { int i -> tk.apply(i + 1, schedF(i)) == tk.apply(i, schedF(i)) } } &&
                            (0..<k).every { int j -> cs.apply(sF(j), hF(j)) == 1 && tk.apply(sF(j), hF(j)) == servingF(sF(j)) } })
                        @Ensures({ servingF(sF(m)) == servingF(sF(0)) + m })
                        @Decreases({ m })
                        static void roundsAdvance(BiFunction<Integer,Integer,Integer> cs, BiFunction<Integer,Integer,Integer> tk,
                                                  Function<Integer,Integer> servingF, Function<Integer,Integer> schedF,
                                                  Function<Integer,Integer> sF, Function<Integer,Integer> uF,
                                                  Function<Integer,Integer> vF, Function<Integer,Integer> hF, int k, int m) {
                            if (m > 0) {
                                roundsAdvance(cs, tk, servingF, schedF, sF, uF, vF, hF, k, m - 1)
                                oneRound(cs, tk, servingF, schedF, hF(m - 1), sF(m - 1), uF(m - 1), vF(m - 1))
                            }
                        }
                    }'''],
        // THE FINALE: Hungry -> Eating for any measure k, everything derived — k rounds advance serving
        // to the waiter\'s ticket, the waiter rides framed to its own scheduled time, and its Enter fires
        // from the relation. Leino\'s Liveness lemma, end to end, from IsTrace + fairness + identities.
        [group: 'P201 transition relation', name: 'hungryEats: Hungry to Eating, all derived', ok: true,
         src: HDR + BIFN + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class HungryEats {
                        @Requires({ cs != null && tk != null && schedF != null && a <= b &&
                            (a..<b).every { int i -> schedF(i) != h ==> (cs.apply(i + 1, h) == cs.apply(i, h) && tk.apply(i + 1, h) == tk.apply(i, h)) } &&
                            (a..<b).every { int i -> schedF(i) != h } })
                        @Ensures({ cs.apply(b, h) == cs.apply(a, h) && tk.apply(b, h) == tk.apply(a, h) })
                        @Decreases({ b - a })
                        static void holderFrame(BiFunction<Integer,Integer,Integer> cs, BiFunction<Integer,Integer,Integer> tk,
                                                Function<Integer,Integer> schedF, int h, int a, int b) {
                            if (a < b) holderFrame(cs, tk, schedF, h, a + 1, b)
                        }
                        @Requires({ cs != null && servingF != null && schedF != null && a <= b &&
                            (a..<b).every { int i -> cs.apply(i, schedF(i)) != 2 ==> servingF(i + 1) == servingF(i) } &&
                            (a..<b).every { int i -> cs.apply(i, schedF(i)) != 2 } })
                        @Ensures({ servingF(b) == servingF(a) })
                        @Decreases({ b - a })
                        static void stableNoEat(BiFunction<Integer,Integer,Integer> cs, Function<Integer,Integer> servingF,
                                                Function<Integer,Integer> schedF, int a, int b) {
                            if (a < b) stableNoEat(cs, servingF, schedF, a + 1, b)
                        }
                        @Requires({ cs != null && tk != null && servingF != null && schedF != null &&
                            n <= u && u + 1 <= v &&
                            schedF(u) == h && schedF(v) == h &&
                            (n..<u).every { int i -> schedF(i) != h } &&
                            (u + 1..<v).every { int i -> schedF(i) != h } &&
                            (n..<u).every { int i -> cs.apply(i, schedF(i)) != 2 } &&
                            (u + 1..<v).every { int i -> cs.apply(i, schedF(i)) != 2 } &&
                            (n..<v + 1).every { int i -> schedF(i) != h ==> (cs.apply(i + 1, h) == cs.apply(i, h) && tk.apply(i + 1, h) == tk.apply(i, h)) } &&
                            (n..<v + 1).every { int i -> cs.apply(i, schedF(i)) != 2 ==> servingF(i + 1) == servingF(i) } &&
                            (n..<v + 1).every { int i -> cs.apply(i, schedF(i)) == 2 ==> servingF(i + 1) == servingF(i) + 1 } &&
                            (n..<v + 1).every { int i -> (cs.apply(i, schedF(i)) == 1 && tk.apply(i, schedF(i)) == servingF(i)) ==> cs.apply(i + 1, schedF(i)) == 2 } &&
                            (n..<v + 1).every { int i -> tk.apply(i + 1, schedF(i)) == tk.apply(i, schedF(i)) } &&
                            cs.apply(n, h) == 1 && tk.apply(n, h) == servingF(n) })
                        @Ensures({ servingF(v + 1) == servingF(n) + 1 })
                        static void oneRound(BiFunction<Integer,Integer,Integer> cs, BiFunction<Integer,Integer,Integer> tk,
                                             Function<Integer,Integer> servingF, Function<Integer,Integer> schedF,
                                             int h, int n, int u, int v) {
                            holderFrame(cs, tk, schedF, h, n, u)
                            stableNoEat(cs, servingF, schedF, n, u)
                            holderFrame(cs, tk, schedF, h, u + 1, v)
                            stableNoEat(cs, servingF, schedF, u + 1, v)
                        }
                        @Requires({ cs != null && tk != null && servingF != null && schedF != null &&
                            sF != null && uF != null && vF != null && hF != null &&
                            0 <= m && m <= k &&
                            (0..<k).every { int j -> sF(j) <= uF(j) && uF(j) + 1 <= vF(j) && vF(j) + 1 == sF(j + 1) } &&
                            (0..<k).every { int j -> schedF(uF(j)) == hF(j) && schedF(vF(j)) == hF(j) } &&
                            (0..<k).every { int j -> (sF(j)..<uF(j)).every { int i -> schedF(i) != hF(j) } } &&
                            (0..<k).every { int j -> (uF(j) + 1..<vF(j)).every { int i -> schedF(i) != hF(j) } } &&
                            (0..<k).every { int j -> (sF(j)..<uF(j)).every { int i -> cs.apply(i, schedF(i)) != 2 } } &&
                            (0..<k).every { int j -> (uF(j) + 1..<vF(j)).every { int i -> cs.apply(i, schedF(i)) != 2 } } &&
                            (0..<k).every { int j -> (sF(j)..<vF(j) + 1).every { int i -> schedF(i) != hF(j) ==> (cs.apply(i + 1, hF(j)) == cs.apply(i, hF(j)) && tk.apply(i + 1, hF(j)) == tk.apply(i, hF(j))) } } &&
                            (0..<k).every { int j -> (sF(j)..<vF(j) + 1).every { int i -> cs.apply(i, schedF(i)) != 2 ==> servingF(i + 1) == servingF(i) } } &&
                            (0..<k).every { int j -> (sF(j)..<vF(j) + 1).every { int i -> cs.apply(i, schedF(i)) == 2 ==> servingF(i + 1) == servingF(i) + 1 } } &&
                            (0..<k).every { int j -> (sF(j)..<vF(j) + 1).every { int i -> (cs.apply(i, schedF(i)) == 1 && tk.apply(i, schedF(i)) == servingF(i)) ==> cs.apply(i + 1, schedF(i)) == 2 } } &&
                            (0..<k).every { int j -> (sF(j)..<vF(j) + 1).every { int i -> tk.apply(i + 1, schedF(i)) == tk.apply(i, schedF(i)) } } &&
                            (0..<k).every { int j -> cs.apply(sF(j), hF(j)) == 1 && tk.apply(sF(j), hF(j)) == servingF(sF(j)) } })
                        @Ensures({ servingF(sF(m)) == servingF(sF(0)) + m })
                        @Decreases({ m })
                        static void roundsAdvance(BiFunction<Integer,Integer,Integer> cs, BiFunction<Integer,Integer,Integer> tk,
                                                  Function<Integer,Integer> servingF, Function<Integer,Integer> schedF,
                                                  Function<Integer,Integer> sF, Function<Integer,Integer> uF,
                                                  Function<Integer,Integer> vF, Function<Integer,Integer> hF, int k, int m) {
                            if (m > 0) {
                                roundsAdvance(cs, tk, servingF, schedF, sF, uF, vF, hF, k, m - 1)
                                oneRound(cs, tk, servingF, schedF, hF(m - 1), sF(m - 1), uF(m - 1), vF(m - 1))
                            }
                        }
                        @Requires({ cs != null && tk != null && servingF != null && schedF != null &&
                            sF != null && uF != null && vF != null && hF != null &&
                            k >= 0 && sF(0) <= sF(k) && sF(k) <= w && schedF(w) == A &&
                            (0..<k).every { int j -> sF(j) <= uF(j) && uF(j) + 1 <= vF(j) && vF(j) + 1 == sF(j + 1) } &&
                            (0..<k).every { int j -> schedF(uF(j)) == hF(j) && schedF(vF(j)) == hF(j) } &&
                            (0..<k).every { int j -> (sF(j)..<uF(j)).every { int i -> schedF(i) != hF(j) } } &&
                            (0..<k).every { int j -> (uF(j) + 1..<vF(j)).every { int i -> schedF(i) != hF(j) } } &&
                            (0..<k).every { int j -> (sF(j)..<uF(j)).every { int i -> cs.apply(i, schedF(i)) != 2 } } &&
                            (0..<k).every { int j -> (uF(j) + 1..<vF(j)).every { int i -> cs.apply(i, schedF(i)) != 2 } } &&
                            (0..<k).every { int j -> (sF(j)..<vF(j) + 1).every { int i -> schedF(i) != hF(j) ==> (cs.apply(i + 1, hF(j)) == cs.apply(i, hF(j)) && tk.apply(i + 1, hF(j)) == tk.apply(i, hF(j))) } } &&
                            (0..<k).every { int j -> (sF(j)..<vF(j) + 1).every { int i -> cs.apply(i, schedF(i)) != 2 ==> servingF(i + 1) == servingF(i) } } &&
                            (0..<k).every { int j -> (sF(j)..<vF(j) + 1).every { int i -> cs.apply(i, schedF(i)) == 2 ==> servingF(i + 1) == servingF(i) + 1 } } &&
                            (0..<k).every { int j -> (sF(j)..<vF(j) + 1).every { int i -> (cs.apply(i, schedF(i)) == 1 && tk.apply(i, schedF(i)) == servingF(i)) ==> cs.apply(i + 1, schedF(i)) == 2 } } &&
                            (0..<k).every { int j -> (sF(j)..<vF(j) + 1).every { int i -> tk.apply(i + 1, schedF(i)) == tk.apply(i, schedF(i)) } } &&
                            (0..<k).every { int j -> cs.apply(sF(j), hF(j)) == 1 && tk.apply(sF(j), hF(j)) == servingF(sF(j)) } &&
                            (sF(0)..<w).every { int i -> schedF(i) != A ==> (cs.apply(i + 1, A) == cs.apply(i, A) && tk.apply(i + 1, A) == tk.apply(i, A)) } &&
                            (sF(0)..<w).every { int i -> schedF(i) != A } &&
                            (sF(k)..<w).every { int i -> cs.apply(i, schedF(i)) != 2 } &&
                            (sF(k)..<w).every { int i -> cs.apply(i, schedF(i)) != 2 ==> servingF(i + 1) == servingF(i) } &&
                            ((cs.apply(w, A) == 1 && tk.apply(w, A) == servingF(w)) ==> cs.apply(w + 1, A) == 2) &&
                            cs.apply(sF(0), A) == 1 && tk.apply(sF(0), A) == servingF(sF(0)) + k })
                        @Ensures({ cs.apply(w + 1, A) == 2 })
                        static void hungryEats(BiFunction<Integer,Integer,Integer> cs, BiFunction<Integer,Integer,Integer> tk,
                                               Function<Integer,Integer> servingF, Function<Integer,Integer> schedF,
                                               Function<Integer,Integer> sF, Function<Integer,Integer> uF,
                                               Function<Integer,Integer> vF, Function<Integer,Integer> hF, int A, int k, int w) {
                            roundsAdvance(cs, tk, servingF, schedF, sF, uF, vF, hF, k, k)
                            holderFrame(cs, tk, schedF, A, sF(0), w)
                            stableNoEat(cs, servingF, schedF, sF(k), w)
                        }
                    }'''],
    ]
}
