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

/** 'P172 ticket-bypass' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G261_p172_ticket_bypass {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Leino\'s ticket lock — BOUNDED BYPASS (bounded overtaking), the liveness result that IS provable in the fragment after the full temporal eventually-eats hits the trace-composition/induction wall. With the counting invariant `ticket - serving == (#non-thinking processes)` — maintained by every event (Request +1 dispensing, Leave -1 advancing serving, Enter unchanged) — a waiting process\'s measure `t[p] - serving` is <= 1 for the two-process lock: a waiter is overtaken AT MOST ONCE before it enters (stronger than mere eventual entry — it bounds the wait). Composed with Phase 171 (each Leave decreases the measure), at most one competitor Leave stands between a Hungry waiter and eating. Dropping the counting invariant refutes the bound (the dispenser could run arbitrarily far ahead). This is a state invariant, so it sidesteps the temporal machinery; the eventually-eats theorem that composes it with fairness over a trace remains out of fragment.'

    static final List<Map> CASES = [

        // ---------- Phase 172: Leino's ticket lock — BOUNDED BYPASS (bounded overtaking) ----------
        // The full temporal liveness ("a hungry process EVENTUALLY eats") needs the trace/schedule/fairness apparatus
        // and induction over an unbounded horizon, which is out of the fragment (the composition wall — see ROADMAP
        // Phase 172). But the finiteness that UNDERWRITES liveness is provable as a state invariant: with the counting
        // invariant `ticket - serving == (#non-thinking processes)`, a waiting process's measure `t[p] - serving`
        // (how many turns of the display stand before it) is <= 1 for the two-process lock. That is BOUNDED BYPASS —
        // a waiter is overtaken AT MOST ONCE before it enters — a liveness property stronger than mere eventual entry
        // (it bounds the wait). Composed with Phase 171 (each Leave decreases the measure): from any Hungry state at
        // most one competitor Leave stands between the waiter and eating. The counting invariant is maintained by
        // every event (Request +1 as it dispenses, Leave -1 as it advances serving, Enter unchanged).
        [group: 'P172 ticket-bypass', name: 'counting invariant preserved by Request', ok: true,
         src: tc('''class BypassRequest {
                        enum Phil { A, B }
                        enum CS { Thinking, Hungry, Eating }
                        static boolean valid(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t) {
                            serving <= ticket &&
                            (cs[Phil.A] != CS.Thinking ==> (serving <= t[Phil.A] && t[Phil.A] < ticket)) &&
                            (cs[Phil.B] != CS.Thinking ==> (serving <= t[Phil.B] && t[Phil.B] < ticket)) &&
                            ((cs[Phil.A] != CS.Thinking && cs[Phil.B] != CS.Thinking) ==> t[Phil.A] != t[Phil.B]) &&
                            (cs[Phil.A] == CS.Eating ==> t[Phil.A] == serving) &&
                            (cs[Phil.B] == CS.Eating ==> t[Phil.B] == serving) &&
                            (ticket - serving == (cs[Phil.A] != CS.Thinking ? 1 : 0) + (cs[Phil.B] != CS.Thinking ? 1 : 0))
                        }
                        @Requires({
                            valid(ticket, serving, cs, t) && cs[p] == CS.Thinking &&
                            ticket2 == ticket + 1 && serving2 == serving && cs2[p] == CS.Hungry && t2[p] == ticket &&
                            (Phil.A != p ==> (cs2[Phil.A] == cs[Phil.A] && t2[Phil.A] == t[Phil.A])) &&
                            (Phil.B != p ==> (cs2[Phil.B] == cs[Phil.B] && t2[Phil.B] == t[Phil.B]))
                        })
                        @Ensures({ valid(ticket2, serving2, cs2, t2) })
                        static void requestPreservesCount(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t, Phil p,
                                                          int ticket2, int serving2, Map<Phil,CS> cs2, Map<Phil,Integer> t2) {}
                    }''')],
        [group: 'P172 ticket-bypass', name: 'counting invariant preserved by Enter', ok: true,
         src: tc('''class BypassEnter {
                        enum Phil { A, B }
                        enum CS { Thinking, Hungry, Eating }
                        static boolean valid(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t) {
                            serving <= ticket &&
                            (cs[Phil.A] != CS.Thinking ==> (serving <= t[Phil.A] && t[Phil.A] < ticket)) &&
                            (cs[Phil.B] != CS.Thinking ==> (serving <= t[Phil.B] && t[Phil.B] < ticket)) &&
                            ((cs[Phil.A] != CS.Thinking && cs[Phil.B] != CS.Thinking) ==> t[Phil.A] != t[Phil.B]) &&
                            (cs[Phil.A] == CS.Eating ==> t[Phil.A] == serving) &&
                            (cs[Phil.B] == CS.Eating ==> t[Phil.B] == serving) &&
                            (ticket - serving == (cs[Phil.A] != CS.Thinking ? 1 : 0) + (cs[Phil.B] != CS.Thinking ? 1 : 0))
                        }
                        @Requires({
                            valid(ticket, serving, cs, t) && cs[p] == CS.Hungry &&
                            ticket2 == ticket && serving2 == serving && t2[p] == t[p] &&
                            ((t[p] == serving && cs2[p] == CS.Eating) || (t[p] != serving && cs2[p] == cs[p])) &&
                            (Phil.A != p ==> (cs2[Phil.A] == cs[Phil.A] && t2[Phil.A] == t[Phil.A])) &&
                            (Phil.B != p ==> (cs2[Phil.B] == cs[Phil.B] && t2[Phil.B] == t[Phil.B]))
                        })
                        @Ensures({ valid(ticket2, serving2, cs2, t2) })
                        static void enterPreservesCount(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t, Phil p,
                                                        int ticket2, int serving2, Map<Phil,CS> cs2, Map<Phil,Integer> t2) {}
                    }''')],
        [group: 'P172 ticket-bypass', name: 'counting invariant preserved by Leave', ok: true,
         src: tc('''class BypassLeave {
                        enum Phil { A, B }
                        enum CS { Thinking, Hungry, Eating }
                        static boolean valid(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t) {
                            serving <= ticket &&
                            (cs[Phil.A] != CS.Thinking ==> (serving <= t[Phil.A] && t[Phil.A] < ticket)) &&
                            (cs[Phil.B] != CS.Thinking ==> (serving <= t[Phil.B] && t[Phil.B] < ticket)) &&
                            ((cs[Phil.A] != CS.Thinking && cs[Phil.B] != CS.Thinking) ==> t[Phil.A] != t[Phil.B]) &&
                            (cs[Phil.A] == CS.Eating ==> t[Phil.A] == serving) &&
                            (cs[Phil.B] == CS.Eating ==> t[Phil.B] == serving) &&
                            (ticket - serving == (cs[Phil.A] != CS.Thinking ? 1 : 0) + (cs[Phil.B] != CS.Thinking ? 1 : 0))
                        }
                        @Requires({
                            valid(ticket, serving, cs, t) && cs[p] == CS.Eating &&
                            ticket2 == ticket && serving2 == serving + 1 && cs2[p] == CS.Thinking && t2[p] == t[p] &&
                            (Phil.A != p ==> (cs2[Phil.A] == cs[Phil.A] && t2[Phil.A] == t[Phil.A])) &&
                            (Phil.B != p ==> (cs2[Phil.B] == cs[Phil.B] && t2[Phil.B] == t[Phil.B]))
                        })
                        @Ensures({ valid(ticket2, serving2, cs2, t2) })
                        static void leavePreservesCount(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t, Phil p,
                                                        int ticket2, int serving2, Map<Phil,CS> cs2, Map<Phil,Integer> t2) {}
                    }''')],
        // The headline: a waiting process is overtaken AT MOST ONCE — its measure t[p] - serving is <= 1.
        [group: 'P172 ticket-bypass', name: 'bounded bypass: a waiter is overtaken at most once', ok: true,
         src: tc('''class BypassBound {
                        enum Phil { A, B }
                        enum CS { Thinking, Hungry, Eating }
                        static boolean valid(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t) {
                            serving <= ticket &&
                            (cs[Phil.A] != CS.Thinking ==> (serving <= t[Phil.A] && t[Phil.A] < ticket)) &&
                            (cs[Phil.B] != CS.Thinking ==> (serving <= t[Phil.B] && t[Phil.B] < ticket)) &&
                            ((cs[Phil.A] != CS.Thinking && cs[Phil.B] != CS.Thinking) ==> t[Phil.A] != t[Phil.B]) &&
                            (cs[Phil.A] == CS.Eating ==> t[Phil.A] == serving) &&
                            (cs[Phil.B] == CS.Eating ==> t[Phil.B] == serving) &&
                            (ticket - serving == (cs[Phil.A] != CS.Thinking ? 1 : 0) + (cs[Phil.B] != CS.Thinking ? 1 : 0))
                        }
                        @Requires({ valid(ticket, serving, cs, t) && cs[p] == CS.Hungry })
                        @Ensures({ t[p] - serving <= 1 })
                        static void boundedBypass(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t, Phil p) {}
                    }''')],
        // Teeth: without the counting invariant the bound is lost — the dispenser could be arbitrarily far ahead of
        // the display, so a waiter's measure is unbounded. (This is why the counting conjunct is the enabler.)
        [group: 'P172 ticket-bypass', name: 'bypass bound refutes without the counting invariant', expect: 'Cannot prove postcondition',
         src: tc('''class BypassNoCount {
                        enum Phil { A, B }
                        enum CS { Thinking, Hungry, Eating }
                        static boolean valid(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t) {
                            serving <= ticket &&
                            (cs[Phil.A] != CS.Thinking ==> (serving <= t[Phil.A] && t[Phil.A] < ticket)) &&
                            (cs[Phil.B] != CS.Thinking ==> (serving <= t[Phil.B] && t[Phil.B] < ticket)) &&
                            ((cs[Phil.A] != CS.Thinking && cs[Phil.B] != CS.Thinking) ==> t[Phil.A] != t[Phil.B]) &&
                            (cs[Phil.A] == CS.Eating ==> t[Phil.A] == serving) &&
                            (cs[Phil.B] == CS.Eating ==> t[Phil.B] == serving)
                        }
                        @Requires({ valid(ticket, serving, cs, t) && cs[p] == CS.Hungry })
                        @Ensures({ t[p] - serving <= 1 })
                        static void boundedBypass(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t, Phil p) {}
                    }''')],
    ]
}
