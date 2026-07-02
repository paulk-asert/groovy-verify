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

/** 'P173 trace-liveness' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G262_p173_trace_liveness {

    static final List<Map> CASES = [

        // ---------- Phase 173: Leino's ticket lock — TRACE-LEVEL bounded liveness (engine fix: apply-term sharing) ----------
        // An encoder fix (Phase 173) makes a numeric-returning `Function`'s application `f.apply(i)` a stable, shared
        // uninterpreted-function term that partakes in integer arithmetic — so the state of the system OVER TIME can be
        // modelled as trace functions `serving`, `t[p]`, `cs[p] : nat -> ...`, and reasoning composes across contract
        // positions. Previously the int argument was coerced into the Object value sort and `f.apply(i)` fell through
        // unmodelled (a fresh opaque value per occurrence), so nothing over the trace composed. This unblocks a
        // BOUNDED eventually-eats: with bounded bypass (Phase 172: a waiter's measure is <= 1), a Hungry process eats
        // within a fixed number of trace steps — no unbounded induction. (The full FAIR-schedule eventually-eats, which
        // must DERIVE that the productive steps occur over an unbounded window, still needs the trace-loop induction —
        // out of fragment; see ROADMAP Phase 173.)
        [group: 'P173 trace-liveness', name: 'higher-order function values compose across contracts', ok: true,
         src: tc('''class TraceCompose {
                        @Requires({ f(n) == g(n) && (f(n) == g(n) ==> h(n) == 2) })
                        @Ensures({ h(n) == 2 })
                        static void compose(Function<Integer,Integer> f,
                                            Function<Integer,Integer> g,
                                            Function<Integer,Integer> h, int n) {}
                    }''')],
        // The headline: a bounded eventually-eats STEP over the trace. A (Hungry, measure 1) at time n; the served
        // process leaves at step n (serving advances by one, A untouched), which makes A's measure zero; A's Enter
        // then fires at step n+1 — so A is Eating at n+2. All over uninterpreted trace functions; the intermediate
        // measure-zero is DERIVED (t[A] frozen == old serving+1 == new serving), not assumed.
        [group: 'P173 trace-liveness', name: 'bounded eventually-eats over the trace', ok: true,
         src: tc('''class TraceEats {
                        @Requires({
                            csAF(n) == 1 && tAF(n) == servingF(n) + 1 &&
                            servingF(n + 1) == servingF(n) + 1 && csAF(n + 1) == 1 && tAF(n + 1) == tAF(n) &&
                            ((csAF(n + 1) == 1 && tAF(n + 1) == servingF(n + 1)) ==> csAF(n + 2) == 2)
                        })
                        @Ensures({ csAF(n + 2) == 2 })
                        static void eats(Function<Integer,Integer> csAF,
                                         Function<Integer,Integer> servingF,
                                         Function<Integer,Integer> tAF, int n) {}
                    }''')],
        // Teeth: drop the Enter step and A need not reach Eating — the trace composition is doing real work.
        [group: 'P173 trace-liveness', name: 'eventually-eats refutes without the Enter step', expect: 'Cannot prove postcondition',
         src: tc('''class TraceEatsBroken {
                        @Requires({
                            csAF(n) == 1 && tAF(n) == servingF(n) + 1 &&
                            servingF(n + 1) == servingF(n) + 1 && csAF(n + 1) == 1 && tAF(n + 1) == tAF(n)
                        })
                        @Ensures({ csAF(n + 2) == 2 })
                        static void eats(Function<Integer,Integer> csAF,
                                         Function<Integer,Integer> servingF,
                                         Function<Integer,Integer> tAF, int n) {}
                    }''')],
        // The base case: a waiter whose ticket is already up (measure zero) eats at its next scheduled step (Enter).
        [group: 'P173 trace-liveness', name: 'base case: a served waiter eats in one step', ok: true,
         src: tc('''class TraceBase {
                        @Requires({
                            csAF(n) == 1 && tAF(n) == servingF(n) &&
                            ((csAF(n) == 1 && tAF(n) == servingF(n)) ==> csAF(n + 1) == 2)
                        })
                        @Ensures({ csAF(n + 1) == 2 })
                        static void eats(Function<Integer,Integer> csAF,
                                         Function<Integer,Integer> servingF,
                                         Function<Integer,Integer> tAF, int n) {}
                    }''')],
    ]
}
