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

/** 'P174 fair-liveness' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G263_p174_fair_liveness {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Leino\'s ticket lock — FAIR-SCHEDULE eventually-eats (base case), with progress DERIVED from fairness, not assumed. The Phase-173 apply-term fix incidentally unblocked recursive-lemma induction over trace functions (a recursive call\'s @Ensures serves as the induction hypothesis) — what Phase 172/173 called Wall 2; the earlier \'no usable @Ensures\' was a downstream symptom of apply-terms not composing. With it, Leino\'s GetNextStep frame argument is expressible: a recursive frame lemma proves a trace value frozen step-by-step across a window is unchanged end-to-end (the direct closed form still does NOT close — the recursion carries it). The base-case Liveness then composes: a Hungry process holding the served ticket (measure 0) with fairness giving a future scheduled time u stays ready across [n,u) (frameA + stableServing), so its Enter fires at u -> Eating at u+1. Dropping the Enter step refutes. What remains for FULL two-process liveness is the measure-1 reduction (follow the served process out of the critical section, advancing serving so the waiter\'s measure drops to 0, then the base case) — a nested fairness round not yet built.'

    static final List<Map> CASES = [

        // ---------- Phase 174: Leino's ticket lock — FAIR-SCHEDULE eventually-eats (base case), progress DERIVED ----------
        // The apply-term fix (Phase 173) turned out to unblock more than bounded composition: recursive-lemma
        // induction over trace functions now works (a recursive call's @Ensures serves as the induction hypothesis),
        // which is what Phase 172/173 flagged as "Wall 2". With it, Leino's GetNextStep frame argument is expressible
        // — and the FAIR-SCHEDULE eventually-eats no longer *assumes* the productive step, it DERIVES it: fairness
        // yields a future time the process is scheduled, and a recursive frame lemma proves the process stays ready
        // until then. This is the genuine liveness mechanism (Section 7.5-7.6), for the base case (the waiter already
        // holds the served ticket).
        // (1) The frame lemma distilled: a trace value frozen step-by-step across a window is unchanged end-to-end —
        // recursive induction over the window (the direct closed form does NOT close; the recursion is what carries it).
        [group: 'P174 fair-liveness', name: 'windowed frame lemma via recursive induction', ok: true,
         src: tc('''class FairFrame {
                        @Requires({ n <= u && (n..<u).every { int i -> csF(i + 1) == csF(i) } })
                        @Ensures({ csF(u) == csF(n) })
                        @Decreases({ u - n })
                        static void frame(Function<Integer,Integer> csF, int n, int u) {
                            if (n < u) frame(csF, n + 1, u)
                        }
                    }''')],
        // (2) The headline: fair-schedule eventually-eats, base case. A (id 0) is Hungry holding the served ticket
        // (measure 0) at n; fairness gives a time u >= n when A is scheduled; A is unscheduled on [n,u) so it stays
        // Hungry with its ticket (frameA), and serving is stable there (only A, the holder, could advance it —
        // stableServing); at u, A's Enter fires. The frame/stability are DERIVED by the recursive helpers, then the
        // Enter step gives A Eating at u+1. Progress derived from fairness, not assumed.
        [group: 'P174 fair-liveness', name: 'fair-schedule eventually-eats (base case)', ok: true,
         src: tc('''class FairLive {
                        @Requires({ n <= u &&
                            (n..<u).every { int i -> schedF(i) != 0 } &&
                            (n..<u).every { int i -> csAF(i + 1) == csAF(i) && tAF(i + 1) == tAF(i) } })
                        @Ensures({ csAF(u) == csAF(n) && tAF(u) == tAF(n) })
                        @Decreases({ u - n })
                        static void frameA(Function<Integer,Integer> schedF, Function<Integer,Integer> csAF,
                                           Function<Integer,Integer> tAF, int n, int u) {
                            if (n < u) frameA(schedF, csAF, tAF, n + 1, u)
                        }
                        @Requires({ n <= u && (n..<u).every { int i -> servingF(i + 1) == servingF(i) } })
                        @Ensures({ servingF(u) == servingF(n) })
                        @Decreases({ u - n })
                        static void stableServing(Function<Integer,Integer> servingF, int n, int u) {
                            if (n < u) stableServing(servingF, n + 1, u)
                        }
                        @Requires({ n <= u && schedF(u) == 0 &&
                            csAF(n) == 1 && tAF(n) == servingF(n) &&
                            (n..<u).every { int i -> schedF(i) != 0 } &&
                            (n..<u).every { int i -> csAF(i + 1) == csAF(i) && tAF(i + 1) == tAF(i) } &&
                            (n..<u).every { int i -> servingF(i + 1) == servingF(i) } &&
                            ((csAF(u) == 1 && tAF(u) == servingF(u)) ==> csAF(u + 1) == 2) })
                        @Ensures({ csAF(u + 1) == 2 })
                        static void eventuallyEats(Function<Integer,Integer> csAF, Function<Integer,Integer> tAF,
                                                   Function<Integer,Integer> servingF, Function<Integer,Integer> schedF, int n, int u) {
                            frameA(schedF, csAF, tAF, n, u)
                            stableServing(servingF, n, u)
                        }
                    }''')],
        // Teeth: drop the Enter step and reaching Eating no longer follows — the fairness/framing composition is
        // doing real work, not smuggling the conclusion in.
        [group: 'P174 fair-liveness', name: 'eventually-eats refutes without the Enter step', expect: 'Cannot prove postcondition',
         src: tc('''class FairLiveBroken {
                        @Requires({ n <= u &&
                            (n..<u).every { int i -> csAF(i + 1) == csAF(i) && tAF(i + 1) == tAF(i) } })
                        @Ensures({ csAF(u) == csAF(n) && tAF(u) == tAF(n) })
                        @Decreases({ u - n })
                        static void frameA(Function<Integer,Integer> csAF,
                                           Function<Integer,Integer> tAF, int n, int u) {
                            if (n < u) frameA(csAF, tAF, n + 1, u)
                        }
                        @Requires({ n <= u && (n..<u).every { int i -> servingF(i + 1) == servingF(i) } })
                        @Ensures({ servingF(u) == servingF(n) })
                        @Decreases({ u - n })
                        static void stableServing(Function<Integer,Integer> servingF, int n, int u) {
                            if (n < u) stableServing(servingF, n + 1, u)
                        }
                        @Requires({ n <= u && schedF(u) == 0 &&
                            csAF(n) == 1 && tAF(n) == servingF(n) &&
                            (n..<u).every { int i -> csAF(i + 1) == csAF(i) && tAF(i + 1) == tAF(i) } &&
                            (n..<u).every { int i -> servingF(i + 1) == servingF(i) } })
                        @Ensures({ csAF(u + 1) == 2 })
                        static void eventuallyEats(Function<Integer,Integer> csAF, Function<Integer,Integer> tAF,
                                                   Function<Integer,Integer> servingF, Function<Integer,Integer> schedF, int n, int u) {
                            frameA(csAF, tAF, n, u)
                            stableServing(servingF, n, u)
                        }
                    }''')],
    ]
}
