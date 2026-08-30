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

/**
 * 'P257 claim select' — GROOVY-12320 (Groovy 6.0.0-beta-4+): ChannelSelect selects by CLAIM — exactly one
 * branch dequeues, losers are untouched, a select over closed channels fails fast — and offers fair() /
 * random() policies. The checker probes the runtime it runs on and models whichever it finds, so every
 * verdict here branches on CaseDsl.CLAIM_SELECT: the same source is certified on beta-4+ and honestly
 * refused (or a type error, where fair() does not exist) before it.
 */
class G321_p257_claim_select {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 257 the claim-based ChannelSelect (GROOVY-12320, Groovy 6.0.0-beta-4+; slice 17 of the SEQ/PAR ladder): the checker probes the runtime it runs on (`ChannelSelect.fair()` exists ⇒ claim-based) and models what it finds. Under the claim-based select a looping ALT takes the chosen branch\'s HEAD again (`valueAt`: positional claims through a contended branch prove), a HELD instance is a supported shape (`ChannelSelect alt = ChannelSelect.from(a, b).fair()` before the loop, `alt.select()` inside — the rotation state lives in the instance), the starvation hazard fires only where the policy is priority in effect (the default, or fair() on a FRESH instance each iteration — named, with the hoisting fix), random() is fair in expectation only, and the fair server — a held fair() select, replies guarded by r.index — has its per-client liveness CERTIFIED under weak fairness. On a runtime before beta-4 the same sources keep Phase 256\'s verdicts (fair()/random() are type errors there).'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final String GEN_A = """
                            AsyncChannel<Integer> a = AsyncChannel.create(4)
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    a.send(i)
                                    i = i + 1
                                }
                            }"""
    static final String GEN_B = """
                            AsyncChannel<Integer> b = AsyncChannel.create(4)
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    b.send(i + 100)
                                    i = i + 1
                                }
                            }"""

    static final List<Map> CASES = [

        // ---------- the head again: a positional claim through a lone ready branch ----------
        // With only 'a' ever ready, the k-th value taken is a's k-th element: exact under the claim-based
        // select (the loser 'b' is never touched), only "some remaining element" under the racing one.
        [group: 'P257 claim select', name: 'a positional claim through a lone ready branch',
         *: (CLAIM_SELECT ? [ok: true] : [expect: 'Cannot prove loop invariant']),
         src: tc("""class C {
                        static void mux() {${GEN_A}
                            AsyncChannel<Integer> b = AsyncChannel.create(4)
                            async {                                              // a producer that sends nothing
                                int i = 0
                                @Invariant({ 0 <= i && i <= 0 })
                                @Decreases({ 0 - i })
                                while (i < 0) {
                                    b.send(i)
                                    i = i + 1
                                }
                                b.close()
                            }
                            List<Integer> taken = []
                            int j = 0
                            @Invariant({ taken != null && j >= 0 && taken.size() == j && Forall.range(0, taken.size(), { int k -> taken[k] == k }) })
                            while (true) {
                                ChannelSelect.Result r = await ChannelSelect.from(b, a).select()   // b first: never ready, no hazard
                                int v = (int) r.value
                                taken.add(v)
                                j = j + 1
                            }
                        }
                    }""")],

        // ---------- the held instance (both runtimes) ----------
        [group: 'P257 claim select', name: 'a held priority select is the same multiplexer', ok: true,
         src: tc("""class C {
                        @Requires({ na >= 0 && nb >= 0 })
                        @Ensures({ result.size() == na + nb })
                        static List<Integer> merge(int na, int nb) {
                            AsyncChannel<Integer> a = AsyncChannel.create(4)
                            AsyncChannel<Integer> b = AsyncChannel.create(4)
                            async {
                                int i = 0
                                @Invariant({ 0 <= i && i <= na })
                                @Decreases({ na - i })
                                while (i < na) {
                                    a.send(i)
                                    i = i + 1
                                }
                                a.close()
                            }
                            async {
                                int i = 0
                                @Invariant({ 0 <= i && i <= nb })
                                @Decreases({ nb - i })
                                while (i < nb) {
                                    b.send(i)
                                    i = i + 1
                                }
                                b.close()
                            }
                            AsyncChannel<Integer> out = AsyncChannel.create(8)
                            ChannelSelect alt = ChannelSelect.from(a, b)
                            int j = 0
                            @Invariant({ 0 <= j && j <= na + nb })
                            @Decreases({ na + nb - j })
                            while (j < na + nb) {
                                ChannelSelect.Result r = await alt.select()
                                int v = (int) r.value
                                out.send(v)
                                j = j + 1
                            }
                            out.close()
                            return out.toList()
                        }
                    }""")],

        // ---------- policies (type errors before beta-4) ----------
        // A held fair() rotates from the last winner: no starvation of the second generator.
        [group: 'P257 claim select', name: 'a held fair() select over two generators: no starvation hazard',
         *: (CLAIM_SELECT ? [ok: true] : [expect: 'Cannot find matching method']),
         src: tc("""class C {
                        static void mux() {${GEN_A}${GEN_B}
                            ChannelSelect alt = ChannelSelect.from(a, b).fair()
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {
                                ChannelSelect.Result r = await alt.select()
                                int v = (int) r.value
                                j = j + 1
                            }
                        }
                    }""")],
        // fair() on a FRESH instance each iteration keeps no rotation state: priority in effect — named, with the fix.
        [group: 'P257 claim select', name: 'fair() on a fresh instance each iteration is priority in effect: named',
         *: (CLAIM_SELECT ? [expect: 'keeps no rotation state'] : [expect: 'Cannot find matching method']),
         src: tc("""class C {
                        static void mux() {${GEN_A}${GEN_B}
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {
                                ChannelSelect.Result r = await ChannelSelect.from(a, b).fair().select()
                                int v = (int) r.value
                                j = j + 1
                            }
                        }
                    }""")],
        // random(): no deterministic starvation — no hazard — but no bound either (the fair server case says so).
        [group: 'P257 claim select', name: 'random() over two generators: no starvation hazard',
         *: (CLAIM_SELECT ? [ok: true] : [expect: 'Cannot find matching method']),
         src: tc("""class C {
                        static void mux() {${GEN_A}${GEN_B}
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {
                                ChannelSelect.Result r = await ChannelSelect.from(a, b).random().select()
                                int v = (int) r.value
                                j = j + 1
                            }
                        }
                    }""")],
        // A held fair() certifies a client only if its REQUEST precedes the wait: a client that receives first
        // sends nothing the server could take, and the reply it waits for is never guarded into being.
        [group: 'P257 claim select', name: 'the fair server with a held fair(): a receive-first client is withheld (the request must precede the wait)',
         *: (CLAIM_SELECT ? [expect: 'the request must precede the wait'] : [expect: 'Cannot find matching method']),
         src: tc("""class C {
                        static void server() {
                            AsyncChannel<Integer> reqA = AsyncChannel.create(4)
                            AsyncChannel<Integer> reqB = AsyncChannel.create(4)
                            AsyncChannel<Integer> replyA = AsyncChannel.create(4)
                            AsyncChannel<Integer> replyB = AsyncChannel.create(4)
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    reqA.send(i)
                                    int r = replyA.first()
                                    i = i + 1
                                }
                            }
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    int r = replyB.first()                       // waits before asking
                                    reqB.send(i)
                                    i = i + 1
                                }
                            }
                            ChannelSelect alt = ChannelSelect.from(reqA, reqB).fair()
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {
                                ChannelSelect.Result r = await alt.select()
                                int q = (int) r.value
                                if (r.index == 0) {
                                    replyA.send(q + 1)
                                }
                                if (r.index == 1) {
                                    replyB.send(q + 1)
                                }
                                j = j + 1
                            }
                        }
                    }""")],
        // The fair server under random(): served in expectation, no bound — withheld with that reason.
        [group: 'P257 claim select', name: 'the fair server under random(): per-client liveness withheld (no bound)',
         *: (CLAIM_SELECT ? [expect: 'offers no bound'] : [expect: 'Cannot find matching method']),
         src: tc("""class C {
                        static void server() {
                            AsyncChannel<Integer> reqA = AsyncChannel.create(4)
                            AsyncChannel<Integer> reqB = AsyncChannel.create(4)
                            AsyncChannel<Integer> replyA = AsyncChannel.create(4)
                            AsyncChannel<Integer> replyB = AsyncChannel.create(4)
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    reqA.send(i)
                                    int r = replyA.first()
                                    i = i + 1
                                }
                            }
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    reqB.send(i)
                                    int r = replyB.first()
                                    i = i + 1
                                }
                            }
                            ChannelSelect alt = ChannelSelect.from(reqA, reqB).random()
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {
                                ChannelSelect.Result r = await alt.select()
                                int q = (int) r.value
                                if (r.index == 0) {
                                    replyA.send(q + 1)
                                }
                                if (r.index == 1) {
                                    replyB.send(q + 1)
                                }
                                j = j + 1
                            }
                        }
                    }""")],
    ]
}
