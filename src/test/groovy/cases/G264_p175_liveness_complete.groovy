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

/** 'P175 liveness-complete' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G264_p175_liveness_complete {

    static final List<Map> CASES = [

        // ---------- Phase 175: Leino's ticket lock — the measure-1 reduction closes the FULL two-process liveness ----------
        // The base case (Phase 174) is the waiter that already holds the served ticket (measure 0). This is the other
        // case — the OVERTAKEN waiter (measure 1) — which is Leino's loop body: it first follows the served process
        // out of the kitchen. `reduceMeasure1` composes the frame + serving-stability lemmas with the served process's
        // `Leave` (which advances `serving` by one) to bring the waiter from measure 1 to measure 0; `overtakenEats`
        // then chains that into the base case, so the overtaken waiter reaches Eating. Bounded bypass (Phase 172) caps
        // a waiter's measure at 1, so measure-0 (Phase 174) and measure-1 (here) are EXHAUSTIVE: the two-process
        // fair-schedule eventually-eats is complete. All progress derived from fairness + framing, none assumed.
        // NB: the frame/stability lemma parameters are named to match the callers' (`csAF`/`tAF`/`servingF`) — the
        // `(lo..<hi).every` precondition at a call site is discharged by syntactic match, so aligned names matter.
        [group: 'P175 liveness-complete', name: 'overtaken (measure-1) waiter eats: reduction + base case', ok: true,
         src: tc('''class OvertakeEats {
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
                        @Requires({ n <= v &&
                            csAF(n) == 1 && tAF(n) == servingF(n) + 1 &&
                            (n..<v).every { int i -> csAF(i + 1) == csAF(i) && tAF(i + 1) == tAF(i) } &&
                            (n..<v).every { int i -> servingF(i + 1) == servingF(i) } &&
                            servingF(v + 1) == servingF(v) + 1 && csAF(v + 1) == csAF(v) && tAF(v + 1) == tAF(v) })
                        @Ensures({ csAF(v + 1) == 1 && tAF(v + 1) == servingF(v + 1) })
                        static void reduceMeasure1(Function<Integer,Integer> csAF, Function<Integer,Integer> tAF,
                                                   Function<Integer,Integer> servingF, int n, int v) {
                            frame(csAF, tAF, n, v)
                            stableServing(servingF, n, v)
                        }
                        @Requires({ n <= v && v + 1 <= u && schedF(u) == 0 &&
                            csAF(n) == 1 && tAF(n) == servingF(n) + 1 &&
                            (n..<v).every { int i -> csAF(i + 1) == csAF(i) && tAF(i + 1) == tAF(i) } &&
                            (n..<v).every { int i -> servingF(i + 1) == servingF(i) } &&
                            servingF(v + 1) == servingF(v) + 1 && csAF(v + 1) == csAF(v) && tAF(v + 1) == tAF(v) &&
                            (v + 1..<u).every { int i -> csAF(i + 1) == csAF(i) && tAF(i + 1) == tAF(i) } &&
                            (v + 1..<u).every { int i -> servingF(i + 1) == servingF(i) } &&
                            ((schedF(u) == 0 && csAF(u) == 1 && tAF(u) == servingF(u)) ==> csAF(u + 1) == 2) })
                        @Ensures({ csAF(u + 1) == 2 })
                        static void overtakenEats(Function<Integer,Integer> csAF, Function<Integer,Integer> tAF,
                                                  Function<Integer,Integer> servingF, Function<Integer,Integer> schedF, int n, int v, int u) {
                            reduceMeasure1(csAF, tAF, servingF, n, v)
                            baseEats(csAF, tAF, servingF, schedF, v + 1, u)
                        }
                    }''')],
        // Teeth: if the served process's Leave does NOT advance serving, the waiter's measure never reaches zero,
        // so the reduction cannot establish measure-0 at v+1 — reduceMeasure1's postcondition refutes.
        [group: 'P175 liveness-complete', name: 'reduction refutes when the Leave does not advance serving', expect: 'Cannot prove postcondition',
         src: tc('''class OvertakeBroken {
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
                        @Requires({ n <= v &&
                            csAF(n) == 1 && tAF(n) == servingF(n) + 1 &&
                            (n..<v).every { int i -> csAF(i + 1) == csAF(i) && tAF(i + 1) == tAF(i) } &&
                            (n..<v).every { int i -> servingF(i + 1) == servingF(i) } &&
                            servingF(v + 1) == servingF(v) && csAF(v + 1) == csAF(v) && tAF(v + 1) == tAF(v) })
                        @Ensures({ csAF(v + 1) == 1 && tAF(v + 1) == servingF(v + 1) })
                        static void reduceMeasure1(Function<Integer,Integer> csAF, Function<Integer,Integer> tAF,
                                                   Function<Integer,Integer> servingF, int n, int v) {
                            frame(csAF, tAF, n, v)
                            stableServing(servingF, n, v)
                        }
                    }''')],
    ]
}
