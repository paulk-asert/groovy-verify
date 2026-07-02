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

/** 'P171 ticket-liveness' — 7 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G260_p171_ticket_liveness {

    static final List<Map> CASES = [

        // ---------- Phase 171: Leino's ticket lock — LIVENESS ranking function (KRML260 §7.6) ----------
        // Leino proves "a hungry process eventually eats" via a well-founded measure `t[p] - serving` that a proof-loop
        // drives to zero. These lemmas establish the measure's properties — the skeleton the eventually-eats argument
        // composes: bounded below, strictly decreased by Leave (unchanged by other events), a served process always
        // exists while someone waits, and measure zero enables the Hungry->Eating transition. Composing them over an
        // infinite trace under a fairness assumption (trace/schedule as nat->... functions) is the next slice.
        [group: 'P171 ticket-liveness', name: 'measure t[p]-serving is bounded below', ok: true,
         src: tc('''class LiveMeasure {
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
                        @Requires({ valid(ticket, serving, cs, t) && cs[p] != CS.Thinking })
                        @Ensures({ t[p] - serving >= 0 })
                        static void measureNonNegative(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t, Phil p) {}
                    }''')],
        // Leave by the served process q advances `serving`, dropping a distinct waiter p's measure by one — and it
        // stays >= 0. The >= 0 part needs uniqueness + eating==>served (a waiter distinct from the eater holds a
        // strictly larger ticket, so t[p] > serving): well-foundedness rests on it.
        [group: 'P171 ticket-liveness', name: 'Leave strictly decreases a waiter measure (stays >= 0)', ok: true,
         src: tc('''class LiveLeave {
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
                        @Requires({
                            valid(ticket, serving, cs, t) && cs[q] == CS.Eating && cs[p] == CS.Hungry && p != q &&
                            serving2 == serving + 1 && t2[p] == t[p]
                        })
                        @Ensures({ (t2[p] - serving2) < (t[p] - serving) && (t2[p] - serving2) >= 0 })
                        static void leaveDecreasesMeasure(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t,
                                                          Phil p, Phil q, int serving2, Map<Phil,Integer> t2) {}
                    }''')],
        // Teeth: without uniqueness a waiter could share the eater's ticket (== serving), so the measure would go
        // negative after the advance — the measure is no longer well-founded.
        [group: 'P171 ticket-liveness', name: 'Leave decrease refutes without unique tickets', expect: 'Cannot prove postcondition',
         src: tc('''class LiveLeaveWeak {
                        enum Phil { A, B }
                        enum CS { Thinking, Hungry, Eating }
                        static boolean valid(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t) {
                            serving <= ticket &&
                            (cs[Phil.A] != CS.Thinking ==> (serving <= t[Phil.A] && t[Phil.A] < ticket)) &&
                            (cs[Phil.B] != CS.Thinking ==> (serving <= t[Phil.B] && t[Phil.B] < ticket)) &&
                            (cs[Phil.A] == CS.Eating ==> t[Phil.A] == serving) &&
                            (cs[Phil.B] == CS.Eating ==> t[Phil.B] == serving)
                        }
                        @Requires({
                            valid(ticket, serving, cs, t) && cs[q] == CS.Eating && cs[p] == CS.Hungry && p != q &&
                            serving2 == serving + 1 && t2[p] == t[p]
                        })
                        @Ensures({ (t2[p] - serving2) < (t[p] - serving) && (t2[p] - serving2) >= 0 })
                        static void leaveDecreasesMeasure(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t,
                                                          Phil p, Phil q, int serving2, Map<Phil,Integer> t2) {}
                    }''')],
        // Any event that freezes `serving` and the waiter's ticket (Enter, and Request for an existing waiter) leaves
        // the measure unchanged — so ONLY Leave moves it, always downward.
        [group: 'P171 ticket-liveness', name: 'non-Leave events preserve the measure', ok: true,
         src: tc('''class LiveFreeze {
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
                        @Requires({
                            valid(ticket, serving, cs, t) && cs[p] != CS.Thinking &&
                            serving2 == serving && t2[p] == t[p]
                        })
                        @Ensures({ (t2[p] - serving2) == (t[p] - serving) })
                        static void eventPreservesMeasure(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t,
                                                          Phil p, int serving2, Map<Phil,Integer> t2) {}
                    }''')],
        // With the liveness strengthening (serving < ticket ==> someone holds `serving`), a hungry process guarantees
        // a currently-served process exists — the one the proof follows out of the kitchen (Leino's
        // CurrentlyServedProcess). This keeps progress possible at every step.
        [group: 'P171 ticket-liveness', name: 'a served process exists while someone waits', ok: true,
         src: tc('''class LiveServed {
                        enum Phil { A, B }
                        enum CS { Thinking, Hungry, Eating }
                        static boolean valid(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t) {
                            serving <= ticket &&
                            (cs[Phil.A] != CS.Thinking ==> (serving <= t[Phil.A] && t[Phil.A] < ticket)) &&
                            (cs[Phil.B] != CS.Thinking ==> (serving <= t[Phil.B] && t[Phil.B] < ticket)) &&
                            ((cs[Phil.A] != CS.Thinking && cs[Phil.B] != CS.Thinking) ==> t[Phil.A] != t[Phil.B]) &&
                            (cs[Phil.A] == CS.Eating ==> t[Phil.A] == serving) &&
                            (cs[Phil.B] == CS.Eating ==> t[Phil.B] == serving) &&
                            (serving < ticket ==> ((cs[Phil.A] != CS.Thinking && t[Phil.A] == serving) ||
                                                   (cs[Phil.B] != CS.Thinking && t[Phil.B] == serving)))
                        }
                        @Requires({ valid(ticket, serving, cs, t) && cs[p] == CS.Hungry })
                        @Ensures({ (cs[Phil.A] != CS.Thinking && t[Phil.A] == serving) ||
                                   (cs[Phil.B] != CS.Thinking && t[Phil.B] == serving) })
                        static void servedProcessExists(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t, Phil p) {}
                    }''')],
        // Teeth: without the TicketIsInUse strengthening, nothing forces anyone to hold `serving`, so the served
        // process may not exist — the reason Leino adds that conjunct before defining CurrentlyServedProcess.
        [group: 'P171 ticket-liveness', name: 'served-process existence refutes without the strengthening', expect: 'Cannot prove postcondition',
         src: tc('''class LiveServedWeak {
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
                        @Ensures({ (cs[Phil.A] != CS.Thinking && t[Phil.A] == serving) ||
                                   (cs[Phil.B] != CS.Thinking && t[Phil.B] == serving) })
                        static void servedProcessExists(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t, Phil p) {}
                    }''')],
        // The base case: when a hungry process's measure bottoms out at zero, its ticket equals `serving`, so Enter's
        // guard holds and it transitions Hungry->Eating. Zero measure == the process eats next.
        [group: 'P171 ticket-liveness', name: 'measure zero enables entry', ok: true,
         src: tc('''class LiveBase {
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
                        @Requires({ valid(ticket, serving, cs, t) && cs[p] == CS.Hungry && (t[p] - serving) == 0 })
                        @Ensures({ t[p] == serving })
                        static void zeroEnablesEntry(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t, Phil p) {}
                    }''')],
    ]
}
