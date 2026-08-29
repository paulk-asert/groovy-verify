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
 * 'P255 liveness' — liveness of a looping network under weak fairness: the Phase 243 wait-for graph
 * lifted to the iteration index. A receive of element k waits on the producer's iteration k − pre;
 * program order within an iteration has weight 0, the wrap to the previous iteration −1; a real
 * deadlock is a cycle of weight ≥ 0, i.e. a cycle in the weight-0 subgraph: mutual receive-first loops.
 * Client–server (send, then receive) and a primed cycle are live; an ALT is live when some branch is fed
 * by a pure generator, undecided (loudly) otherwise.
 */
class G319_p255_liveness {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 255 liveness under weak fairness (slice 15 of the SEQ/PAR ladder): assuming every process whose next operation is enabled eventually runs it, a looping network is live exactly when no operation waits, in every iteration, on something that waits on itself in the same iteration — the wait-for graph lifted to the iteration index, where a receive of element k waits on the producer\'s iteration k − pre (pre = priming sends before its loop), program order is weight 0 and the wrap −1, so a deadlock is a cycle in the weight-0 subgraph. Mutual receive-first loops are "circular wait in every iteration … no message is ever ahead of this cycle"; the client–server loop (send, then receive) and a primed cycle are certified live; a three-process ring deadlocks without a priming send and is live with one; a looping ALT is live when a branch is fed by a pure generator and undecided (loudly) otherwise — fairness of the ALT\'s own choice is not assumed. Where certified, the Phase 254 "liveness not claimed" note is discharged. Priming sends enter the stream model: element k of the loop is list index k + pre.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // ---------- the deadlock: mutual receive-first loops ----------
        [group: 'P255 liveness', name: 'two forever loops that each receive before sending: circular wait in every iteration', expect: 'circular wait in every iteration',
         src: tc("""class C {
                        static void mutual() {
                            val aToB = AsyncChannel.<Integer>create(4)
                            val bToA = AsyncChannel.<Integer>create(4)
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    int x = bToA.first()
                                    aToB.send(x + 1)
                                    i = i + 1
                                }
                            }
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {
                                int y = aToB.first()
                                bToA.send(y + 1)
                                j = j + 1
                            }
                        }
                    }""")],
        // ---------- client–server, forever: send then receive breaks the cycle ----------
        [group: 'P255 liveness', name: 'a forever client–server loop is live: the request precedes the wait for its reply', ok: true,
         src: tc("""class C {
                        static void clientServer() {
                            val request = AsyncChannel.<Integer>create(4)
                            val reply = AsyncChannel.<Integer>create(4)
                            async {                                              // the server
                                int j = 0
                                @Invariant({ j >= 0 })
                                while (true) {
                                    int q = request.first()
                                    reply.send(q + 1)
                                    j = j + 1
                                }
                            }
                            int i = 0
                            @Invariant({ i >= 0 })
                            while (true) {                                       // the client
                                request.send(i)
                                int r = reply.first()
                                i = i + 1
                            }
                        }
                    }""")],
        // ---------- the primed cycle: one message ahead ----------
        [group: 'P255 liveness', name: 'a priming send before one loop makes the receive-first cycle live', ok: true,
         src: tc("""class C {
                        static void primed() {
                            val aToB = AsyncChannel.<Integer>create(4)
                            val bToA = AsyncChannel.<Integer>create(4)
                            async {
                                aToB.send(0)                                     // one message ahead
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    int x = bToA.first()
                                    aToB.send(x + 1)
                                    i = i + 1
                                }
                            }
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {
                                int y = aToB.first()
                                bToA.send(y + 1)
                                j = j + 1
                            }
                        }
                    }""")],
        // ---------- a three-process ring ----------
        [group: 'P255 liveness', name: 'a three-process ring with no priming send deadlocks in every iteration', expect: 'circular wait in every iteration',
         src: tc("""class C {
                        static void ring() {
                            val ab = AsyncChannel.<Integer>create(4)
                            val bc = AsyncChannel.<Integer>create(4)
                            val ca = AsyncChannel.<Integer>create(4)
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    int x = ca.first()
                                    ab.send(x)
                                    i = i + 1
                                }
                            }
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    int x = ab.first()
                                    bc.send(x)
                                    i = i + 1
                                }
                            }
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {
                                int x = bc.first()
                                ca.send(x)
                                j = j + 1
                            }
                        }
                    }""")],
        [group: 'P255 liveness', name: 'the same ring with one priming send is live (a token goes round)', ok: true,
         src: tc("""class C {
                        static void ring() {
                            val ab = AsyncChannel.<Integer>create(4)
                            val bc = AsyncChannel.<Integer>create(4)
                            val ca = AsyncChannel.<Integer>create(4)
                            async {
                                ab.send(0)                                       // the token
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    int x = ca.first()
                                    ab.send(x)
                                    i = i + 1
                                }
                            }
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    int x = ab.first()
                                    bc.send(x)
                                    i = i + 1
                                }
                            }
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {
                                int x = bc.first()
                                ca.send(x)
                                j = j + 1
                            }
                        }
                    }""")],
        // ---------- the ALT over dependent branches: undecided, loudly ----------
        [group: 'P255 liveness', name: 'a forever ALT over branches fed by dependent stages is undecided (the ALT\'s own fairness)', expect: 'fairness assumption about the ALT',
         src: tc("""class C {
                        static void mux() {
                            val nums = AsyncChannel.<Integer>create(4)
                            val a = AsyncChannel.<Integer>create(4)
                            val b = AsyncChannel.<Integer>create(4)
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    nums.send(i)
                                    i = i + 1
                                }
                            }
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    int v = nums.first()
                                    a.send(v)
                                    b.send(v)
                                    i = i + 1
                                }
                            }
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {
                                ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
                                int v = (int) r.value
                                j = j + 1
                            }
                        }
                    }""")],
        // ---------- priming sends in the stream model ----------
        [group: 'P255 liveness', name: 'a priming send is element 0; the loop\'s elements follow', ok: true,
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.size() == n + 1 && result[0] == -1 && Forall.range(1, result.size(), { int k -> result[k] == k - 1 }) })
                        static List<Integer> primed(int n) {
                            val out = AsyncChannel.<Integer>create(4)
                            async {
                                out.send(-1)
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    out.send(i)
                                    i = i + 1
                                }
                                out.close()
                            }
                            return out.toList()
                        }
                    }""")],
    ]
}
