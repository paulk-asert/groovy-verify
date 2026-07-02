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

/** 'P170 ticket-lock' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G259_p170_ticket_lock {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Leino\'s ticket lock (KRML260, Modeling Concurrency in Dafny) — SMT-proved mutual exclusion over a bounded (enum) process set. Each atomic event is a Model-2 two-state predicate over a system invariant `valid`, discharged as an empty-bodied lemma (the lattice/monoid-law pattern): mutual exclusion is proved a consequence of the invariant (the paper\'s exact lemma — two symbolic processes p,q, concluding p==q, riding the enum domain-closure axiom so one lemma covers every process), and Request/Enter/Leave each preserve it (Leave, advancing serving while re-establishing the strict bound for a waiter, needs BOTH uniqueness and eating==>served). Dropping the uniqueness conjunct — the strengthening the paper adds last — refutes mutual exclusion and Leave-preservation. Process is a fixed enum {A,B} (the N=2 instance; general symbolic set<Process> is out of fragment).'

    static final List<Map> CASES = [

        // ---------- Phase 170: Leino's ticket lock (KRML260) — SAFETY over a bounded (enum) process set ----------
        // "Modeling Concurrency in Dafny": a bakery-style mutual-exclusion lock, modelled as atomic events over a
        // system invariant `valid`. `Process` is fixed to a small enum (Leino sanctions `datatype Process = Agnes|...`),
        // so P is finite and cs/t are enum-keyed maps; each atomic event is a Model-2 two-state predicate discharged as
        // an empty-bodied lemma (the lattice/monoid-law pattern). The acting process `p` is symbolic — its post-state
        // read at a symbolic key rides the enum domain-closure axiom, so one lemma covers every process.
        [group: 'P170 ticket-lock', name: 'mutual exclusion follows from the invariant', ok: true,
         src: tc('''class Ticket {
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
                        @Requires({ valid(ticket, serving, cs, t) && cs[p] == CS.Eating && cs[q] == CS.Eating })
                        @Ensures({ p == q })                        // both eating ⟹ the same process — mutual exclusion
                        static void mutualExclusion(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t, Phil p, Phil q) {}
                    }''')],
        // Teeth: drop the uniqueness conjunct (the strengthening the paper adds last) and mutual exclusion fails —
        // without distinct tickets, two processes eating at the same `serving` is consistent.
        [group: 'P170 ticket-lock', name: 'mutual exclusion refutes without unique tickets', expect: 'Cannot prove postcondition',
         src: tc('''class TicketWeak {
                        enum Phil { A, B }
                        enum CS { Thinking, Hungry, Eating }
                        static boolean valid(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t) {
                            serving <= ticket &&
                            (cs[Phil.A] != CS.Thinking ==> (serving <= t[Phil.A] && t[Phil.A] < ticket)) &&
                            (cs[Phil.B] != CS.Thinking ==> (serving <= t[Phil.B] && t[Phil.B] < ticket)) &&
                            (cs[Phil.A] == CS.Eating ==> t[Phil.A] == serving) &&
                            (cs[Phil.B] == CS.Eating ==> t[Phil.B] == serving)
                        }
                        @Requires({ valid(ticket, serving, cs, t) && cs[p] == CS.Eating && cs[q] == CS.Eating })
                        @Ensures({ p == q })
                        static void mutualExclusion(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t, Phil p, Phil q) {}
                    }''')],
        // Request(p): a thinking process grabs the current ticket and increments the dispenser. Preserving `valid`
        // leans on the STRICT upper bound t[q] < ticket — the new ticket equals the old `ticket`, distinct from every
        // held ticket (all strictly below it), so uniqueness survives.
        [group: 'P170 ticket-lock', name: 'Request preserves the invariant', ok: true,
         src: tc('''class TicketRequest {
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
                            valid(ticket, serving, cs, t) && cs[p] == CS.Thinking &&
                            ticket2 == ticket + 1 && serving2 == serving &&
                            cs2[p] == CS.Hungry && t2[p] == ticket &&
                            (Phil.A != p ==> (cs2[Phil.A] == cs[Phil.A] && t2[Phil.A] == t[Phil.A])) &&
                            (Phil.B != p ==> (cs2[Phil.B] == cs[Phil.B] && t2[Phil.B] == t[Phil.B]))
                        })
                        @Ensures({ valid(ticket2, serving2, cs2, t2) })
                        static void requestPreservesValid(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t, Phil p,
                                                          int ticket2, int serving2, Map<Phil,CS> cs2, Map<Phil,Integer> t2) {}
                    }''')],
        // Enter(p): the guarded transition — a hungry process whose ticket is being served moves to Eating, else
        // stays put. Preserving the eating==>served conjunct in the taken branch is exactly what the guard supplies.
        [group: 'P170 ticket-lock', name: 'Enter preserves the invariant', ok: true,
         src: tc('''class TicketEnter {
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
                            valid(ticket, serving, cs, t) && cs[p] == CS.Hungry &&
                            ticket2 == ticket && serving2 == serving && t2[p] == t[p] &&
                            ((t[p] == serving && cs2[p] == CS.Eating) || (t[p] != serving && cs2[p] == cs[p])) &&
                            (Phil.A != p ==> (cs2[Phil.A] == cs[Phil.A] && t2[Phil.A] == t[Phil.A])) &&
                            (Phil.B != p ==> (cs2[Phil.B] == cs[Phil.B] && t2[Phil.B] == t[Phil.B]))
                        })
                        @Ensures({ valid(ticket2, serving2, cs2, t2) })
                        static void enterPreservesValid(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t, Phil p,
                                                        int ticket2, int serving2, Map<Phil,CS> cs2, Map<Phil,Integer> t2) {}
                    }''')],
        // Leave(p): an eating process advances `serving` and returns to Thinking — the case the paper flags as
        // trickiest. Re-establishing the strict lower bound serving+1 <= t[q] for a still-waiting q needs BOTH
        // uniqueness (t[p] != t[q]) and eating==>served (t[p] == serving) to lift serving <= t[q].
        [group: 'P170 ticket-lock', name: 'Leave preserves the invariant', ok: true,
         src: tc('''class TicketLeave {
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
                            valid(ticket, serving, cs, t) && cs[p] == CS.Eating &&
                            ticket2 == ticket && serving2 == serving + 1 &&
                            cs2[p] == CS.Thinking && t2[p] == t[p] &&
                            (Phil.A != p ==> (cs2[Phil.A] == cs[Phil.A] && t2[Phil.A] == t[Phil.A])) &&
                            (Phil.B != p ==> (cs2[Phil.B] == cs[Phil.B] && t2[Phil.B] == t[Phil.B]))
                        })
                        @Ensures({ valid(ticket2, serving2, cs2, t2) })
                        static void leavePreservesValid(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t, Phil p,
                                                        int ticket2, int serving2, Map<Phil,CS> cs2, Map<Phil,Integer> t2) {}
                    }''')],
        // Teeth: the same Leave step under the weakened invariant (no uniqueness) can no longer re-establish `valid`
        // after the advance — it cannot rule out a second process stranded at the old `serving`.
        [group: 'P170 ticket-lock', name: 'Leave refutes without unique tickets', expect: 'Cannot prove postcondition',
         src: tc('''class TicketLeaveWeak {
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
                            valid(ticket, serving, cs, t) && cs[p] == CS.Eating &&
                            ticket2 == ticket && serving2 == serving + 1 &&
                            cs2[p] == CS.Thinking && t2[p] == t[p] &&
                            (Phil.A != p ==> (cs2[Phil.A] == cs[Phil.A] && t2[Phil.A] == t[Phil.A])) &&
                            (Phil.B != p ==> (cs2[Phil.B] == cs[Phil.B] && t2[Phil.B] == t[Phil.B]))
                        })
                        @Ensures({ valid(ticket2, serving2, cs2, t2) })
                        static void leavePreservesValid(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t, Phil p,
                                                        int ticket2, int serving2, Map<Phil,CS> cs2, Map<Phil,Integer> t2) {}
                    }''')],
    ]
}
