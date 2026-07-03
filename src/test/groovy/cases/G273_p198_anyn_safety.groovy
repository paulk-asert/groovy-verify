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

/** 'P198 any-N safety' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G273_p198_anyn_safety {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Leino\'s ticket lock over a SYMBOLIC process count: processes are int-indexed 0..<N (the faithful skolemization of the paper\'s finite set<Process>), cs/t are functions, and valid quantifies over the domain — the per-conjunct bound as a bounded every over symbolic N, ticket uniqueness as a NESTED every. Mutual exclusion and all three transition preservations (Request/Enter/Leave) verify for any N; teeth: uniqueness dropped refutes mutual exclusion, and the strict dispenser bound dropped refutes Request preservation (the paper\'s invariant-strengthening story, at any N). CS encoding: 0 Thinking, 1 Hungry, 2 Eating.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — abstract-carrier laws: higher-order/monadic shapes beyond the grid'

    static final List<Map> CASES = [

        // ---------- Phase 198: the ticket lock over a symbolic process count (the set<Process> edge) ----------
        // Leino's own spelling: `valid` quantifies over the process domain. Here the domain is int-indexed
        // 0..<N with N symbolic — bounded quantifiers over a symbolic bound, uniqueness a nested every —
        // and `valid` is a boolean helper (its own null guards short-circuit its deref obligations).
        [group: 'P198 any-N safety', name: 'mutual exclusion for any N (helper valid)', ok: true,
         src: tc('''class TicketN {
                        static boolean valid(int N, int ticket, int serving, Function<Integer,Integer> cs, Function<Integer,Integer> t) {
                            cs != null && t != null && serving <= ticket &&
                            (0..<N).every { int r -> cs(r) != 0 ==> (serving <= t(r) && t(r) < ticket) } &&
                            (0..<N).every { int r1 -> (0..<N).every { int r2 ->
                                (r1 != r2 && cs(r1) != 0 && cs(r2) != 0) ==> t(r1) != t(r2) } } &&
                            (0..<N).every { int r -> cs(r) == 2 ==> t(r) == serving }
                        }
                        @Requires({ 0 <= p && p < N && 0 <= q && q < N &&
                            valid(N, ticket, serving, cs, t) && cs(p) == 2 && cs(q) == 2 })
                        @Ensures({ p == q })
                        static void mutualExclusion(int N, int ticket, int serving,
                                                    Function<Integer,Integer> cs, Function<Integer,Integer> t, int p, int q) {}
                    }''')],
        // Request(p): a thinking process takes the dispenser value and the dispenser advances. Preservation
        // leans on the STRICT bound t(r) < ticket — the new ticket equals the old dispenser value, distinct
        // from every held ticket. The frame over the other N-1 processes is one quantified conjunct.
        [group: 'P198 any-N safety', name: 'Request preserves the invariant for any N', ok: true,
         src: tc('''class TicketNReq {
                        static boolean valid(int N, int ticket, int serving, Function<Integer,Integer> cs, Function<Integer,Integer> t) {
                            cs != null && t != null && serving <= ticket &&
                            (0..<N).every { int r -> cs(r) != 0 ==> (serving <= t(r) && t(r) < ticket) } &&
                            (0..<N).every { int r1 -> (0..<N).every { int r2 ->
                                (r1 != r2 && cs(r1) != 0 && cs(r2) != 0) ==> t(r1) != t(r2) } } &&
                            (0..<N).every { int r -> cs(r) == 2 ==> t(r) == serving }
                        }
                        @Requires({ cs2 != null && t2 != null && 0 <= p && p < N &&
                            valid(N, ticket, serving, cs, t) && cs(p) == 0 &&
                            ticket2 == ticket + 1 && serving2 == serving &&
                            cs2(p) == 1 && t2(p) == ticket &&
                            (0..<N).every { int r -> r != p ==> (cs2(r) == cs(r) && t2(r) == t(r)) } })
                        @Ensures({ valid(N, ticket2, serving2, cs2, t2) })
                        static void requestPreserves(int N, int ticket, int serving, int ticket2, int serving2,
                                                     Function<Integer,Integer> cs, Function<Integer,Integer> t,
                                                     Function<Integer,Integer> cs2, Function<Integer,Integer> t2, int p) {}
                    }''')],
        // Enter(p): the hungry holder of the served ticket starts eating; nothing else moves.
        [group: 'P198 any-N safety', name: 'Enter preserves the invariant for any N', ok: true,
         src: tc('''class TicketNEnter {
                        static boolean valid(int N, int ticket, int serving, Function<Integer,Integer> cs, Function<Integer,Integer> t) {
                            cs != null && t != null && serving <= ticket &&
                            (0..<N).every { int r -> cs(r) != 0 ==> (serving <= t(r) && t(r) < ticket) } &&
                            (0..<N).every { int r1 -> (0..<N).every { int r2 ->
                                (r1 != r2 && cs(r1) != 0 && cs(r2) != 0) ==> t(r1) != t(r2) } } &&
                            (0..<N).every { int r -> cs(r) == 2 ==> t(r) == serving }
                        }
                        @Requires({ cs2 != null && t2 != null && 0 <= p && p < N &&
                            valid(N, ticket, serving, cs, t) && cs(p) == 1 && t(p) == serving &&
                            cs2(p) == 2 && t2(p) == t(p) &&
                            (0..<N).every { int r -> r != p ==> (cs2(r) == cs(r) && t2(r) == t(r)) } })
                        @Ensures({ valid(N, ticket, serving, cs2, t2) })
                        static void enterPreserves(int N, int ticket, int serving,
                                                   Function<Integer,Integer> cs, Function<Integer,Integer> t,
                                                   Function<Integer,Integer> cs2, Function<Integer,Integer> t2, int p) {}
                    }''')],
        // Leave(p): the eater returns to thinking and the serving counter advances — the transition whose
        // preservation leans on uniqueness (every OTHER waiter's ticket exceeds the old serving, so the
        // advanced serving is still a lower bound).
        [group: 'P198 any-N safety', name: 'Leave preserves the invariant for any N', ok: true,
         src: tc('''class TicketNLeave {
                        static boolean valid(int N, int ticket, int serving, Function<Integer,Integer> cs, Function<Integer,Integer> t) {
                            cs != null && t != null && serving <= ticket &&
                            (0..<N).every { int r -> cs(r) != 0 ==> (serving <= t(r) && t(r) < ticket) } &&
                            (0..<N).every { int r1 -> (0..<N).every { int r2 ->
                                (r1 != r2 && cs(r1) != 0 && cs(r2) != 0) ==> t(r1) != t(r2) } } &&
                            (0..<N).every { int r -> cs(r) == 2 ==> t(r) == serving }
                        }
                        @Requires({ cs2 != null && t2 != null && 0 <= p && p < N &&
                            valid(N, ticket, serving, cs, t) && cs(p) == 2 &&
                            serving2 == serving + 1 &&
                            cs2(p) == 0 && t2(p) == t(p) &&
                            (0..<N).every { int r -> r != p ==> (cs2(r) == cs(r) && t2(r) == t(r)) } })
                        @Ensures({ valid(N, ticket, serving2, cs2, t2) })
                        static void leavePreserves(int N, int ticket, int serving, int serving2,
                                                   Function<Integer,Integer> cs, Function<Integer,Integer> t,
                                                   Function<Integer,Integer> cs2, Function<Integer,Integer> t2, int p) {}
                    }''')],
        // Teeth 1: uniqueness dropped — two distinct processes both eating at `serving` is consistent, and
        // mutual exclusion refutes with a concrete N (the strengthening the paper adds last).
        [group: 'P198 any-N safety', name: 'mutual exclusion refutes without uniqueness (any N)', expect: 'Cannot prove postcondition',
         src: tc('''class TicketNWeak {
                        @Requires({ cs != null && t != null && 0 <= p && p < N && 0 <= q && q < N &&
                            serving <= ticket &&
                            (0..<N).every { int r -> cs(r) != 0 ==> (serving <= t(r) && t(r) < ticket) } &&
                            (0..<N).every { int r -> cs(r) == 2 ==> t(r) == serving } &&
                            cs(p) == 2 && cs(q) == 2 })
                        @Ensures({ p == q })
                        static void mutualExclusion(int N, int ticket, int serving,
                                                    Function<Integer,Integer> cs, Function<Integer,Integer> t, int p, int q) {}
                    }''')],
        // Teeth 2: the strict dispenser bound dropped (t(r) <= ticket instead of < ticket) — the fresh
        // ticket Request hands out can collide with a held one, so Request preservation refutes.
        [group: 'P198 any-N safety', name: 'Request refutes without the strict dispenser bound', expect: 'Cannot prove postcondition',
         src: tc('''class TicketNReqWeak {
                        static boolean valid(int N, int ticket, int serving, Function<Integer,Integer> cs, Function<Integer,Integer> t) {
                            cs != null && t != null && serving <= ticket &&
                            (0..<N).every { int r -> cs(r) != 0 ==> (serving <= t(r) && t(r) <= ticket) } &&
                            (0..<N).every { int r1 -> (0..<N).every { int r2 ->
                                (r1 != r2 && cs(r1) != 0 && cs(r2) != 0) ==> t(r1) != t(r2) } } &&
                            (0..<N).every { int r -> cs(r) == 2 ==> t(r) == serving }
                        }
                        @Requires({ cs2 != null && t2 != null && 0 <= p && p < N &&
                            valid(N, ticket, serving, cs, t) && cs(p) == 0 &&
                            ticket2 == ticket + 1 && serving2 == serving &&
                            cs2(p) == 1 && t2(p) == ticket &&
                            (0..<N).every { int r -> r != p ==> (cs2(r) == cs(r) && t2(r) == t(r)) } })
                        @Ensures({ valid(N, ticket2, serving2, cs2, t2) })
                        static void requestPreserves(int N, int ticket, int serving, int ticket2, int serving2,
                                                     Function<Integer,Integer> cs, Function<Integer,Integer> t,
                                                     Function<Integer,Integer> cs2, Function<Integer,Integer> t2, int p) {}
                    }''')],
    ]
}
