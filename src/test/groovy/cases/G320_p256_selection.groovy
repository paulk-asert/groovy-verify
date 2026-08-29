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
 * 'P256 selection' — ChannelSelect as the runtime actually selects: the lowest READY index wins, and a
 * losing branch's consumed element is re-sent to the back of its queue. So a looping ALT takes SOME
 * remaining element of the chosen branch (count exact, order within a contended branch not), a branch
 * behind an always-ready one may STARVE, and a client whose reply is guarded by the choice is served only
 * when its branch is taken — not certified. ALT-loop liveness itself needs no choice fairness: the OR
 * fixpoint decides it.
 */
class G320_p256_selection {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 256 selection semantics (slice 16 of the SEQ/PAR ladder): ChannelSelect modelled as it selects — the lowest READY index wins when several are ready, and a losing branch\'s consumed element is re-sent to the BACK of its queue (Groovy 6 beta-2). A looping ALT therefore takes SOME remaining element of the chosen branch (`$channelSelect.valueAny`: count exact, element-wise contracts forward, positional claims through a contended branch do not prove); a branch behind one fed by an infinite pure generator is a NAMED "Selection starvation hazard"; a reply guarded by the choice (`if (r.index == i) X.send(..)`) leaves its client\'s liveness withheld with the runtime\'s reason ("served only when the ALT … takes branch i — ChannelSelect prefers the lowest ready index"). ALT-loop liveness needs no choice fairness: the weight-0 completion fixpoint treats the ALT as an OR node, so a multiplexer over dependent stages is certified live and an ALT whose every branch waits on its own output is a circular wait in every iteration. The fair ALT of Kerridge\'s books needs runtime support the checker names.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // ---------- the OR fixpoint: an ALT whose every branch waits on its own output deadlocks ----------
        [group: 'P256 selection', name: 'an ALT whose branches all wait on its own output: circular wait in every iteration', expect: 'circular wait in every iteration',
         src: tc("""class C {
                        static void knot() {
                            AsyncChannel<Integer> a = AsyncChannel.create(4)
                            AsyncChannel<Integer> b = AsyncChannel.create(4)
                            AsyncChannel<Integer> out = AsyncChannel.create(4)
                            async {                                              // one stage feeds both branches from the ALT's own output
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    int v = out.first()
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
                                out.send(v)
                                j = j + 1
                            }
                        }
                    }""")],
        // The same knot with one branch fed by a generator: the ALT always has that alternative — live.
        [group: 'P256 selection', name: 'the same knot with one generator branch is live', ok: true,
         src: tc("""class C {
                        static void knot() {
                            AsyncChannel<Integer> a = AsyncChannel.create(4)
                            AsyncChannel<Integer> b = AsyncChannel.create(4)
                            AsyncChannel<Integer> out = AsyncChannel.create(4)
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    int v = out.first()
                                    b.send(v)
                                    i = i + 1
                                }
                            }
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    a.send(i)
                                    i = i + 1
                                }
                            }
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {
                                ChannelSelect.Result r = await ChannelSelect.from(b, a).select()
                                int v = (int) r.value
                                out.send(v)
                                j = j + 1
                            }
                        }
                    }""")],

        // ---------- starvation under priority ----------
        [group: 'P256 selection', name: 'a branch behind an always-ready generator may starve', expect: 'Selection starvation hazard',
         src: tc("""class C {
                        static void mux() {
                            AsyncChannel<Integer> fast = AsyncChannel.create(4)
                            AsyncChannel<Integer> slow = AsyncChannel.create(4)
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    fast.send(i)
                                    i = i + 1
                                }
                            }
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    slow.send(-i)
                                    i = i + 1
                                }
                            }
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {
                                ChannelSelect.Result r = await ChannelSelect.from(fast, slow).select()
                                int v = (int) r.value
                                j = j + 1
                            }
                        }
                    }""")],
        // Bounded generators do not starve anyone for ever: no hazard.
        [group: 'P256 selection', name: 'a finite generator ahead of a branch is a delay, not a starvation', ok: true,
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
                            int j = 0
                            @Invariant({ 0 <= j && j <= na + nb })
                            @Decreases({ na + nb - j })
                            while (j < na + nb) {
                                ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
                                int v = (int) r.value
                                out.send(v)
                                j = j + 1
                            }
                            out.close()
                            return out.toList()
                        }
                    }""")],

        // ---------- the fair server: per-client liveness withheld, with the runtime's reason ----------
        [group: 'P256 selection', name: 'a server replying on the chosen client\'s channel: the client\'s liveness is not certified', expect: 'served only when the ALT',
         src: tc("""class C {
                        static void fairServer() {
                            AsyncChannel<Integer> reqA = AsyncChannel.create(4)
                            AsyncChannel<Integer> reqB = AsyncChannel.create(4)
                            AsyncChannel<Integer> replyA = AsyncChannel.create(4)
                            AsyncChannel<Integer> replyB = AsyncChannel.create(4)
                            async {                                              // client A
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    reqA.send(i)
                                    int r = replyA.first()
                                    i = i + 1
                                }
                            }
                            async {                                              // client B
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    reqB.send(i)
                                    int r = replyB.first()
                                    i = i + 1
                                }
                            }
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {                                       // the server
                                ChannelSelect.Result r = await ChannelSelect.from(reqA, reqB).select()
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
