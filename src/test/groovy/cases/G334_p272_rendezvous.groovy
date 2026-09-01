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
 * 'P272 rendezvous channels' — the SEND-SEND deadlock, which every earlier rung was blind to. Up to here the
 * certificate rested on "a send never blocks" (buffered: queued, the Awaitable discarded), so a send was a
 * wait-for node nothing waited behind. On a RENDEZVOUS channel (`AsyncChannel.create(0)` — JCSP's plain
 * one2one, and what Kerridge's c07 uses) that is false: the send completes only when its receive does. So a
 * rendezvous send becomes a blocking event, and a send and its receive are coalesced into ONE synchronisation
 * (each waits for what the other waits for) rather than two events waiting on each other, which would make
 * every matched pair a two-cycle. c07's two deadlocks then fall out of the same well-foundedness theorem.
 */
class G334_p272_rendezvous {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 272 rendezvous channels (slice 33 of the SEQ/PAR ladder): a channel declared `AsyncChannel.create(0)` is a RENDEZVOUS — the send completes only when its receive does — so a send on one is a blocking event in the wait-for graph, not the free operation a buffered send is. A rendezvous send and the receive that takes its element are coalesced into a single synchronisation (each inherits the other\'s program-order predecessors, with no edge between them), so a matched pair is not itself a cycle and a real circular wait has to close through some other event. That closes the SEND-SEND deadlock class the earlier rungs could not see: Kerridge c07\'s producer and consumer that both write before they read, and its crossed client-server pair where two servers are each other\'s client — a cycle in the client-server graph, the design rule the Welch/Martin school states informally. The fixes verify: reading before writing on one side, and a strict server hierarchy. The model is capacity-sensitive, not a blanket ban on writing first — the same shape on a BUFFERED channel verifies, because with buffering it genuinely does not deadlock.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [
        // ---------- c07's first deadlock: both processes write before they read ----------
        // Kerridge's BadP / BadC. On JCSP's unbuffered one2one each write blocks until the matching read,
        // so two processes that both write first block on each other's write. Buffered, this is not a
        // deadlock at all — which is why the verdict has to key on the capacity.
        [group: 'P272 rendezvous channels', name: 'both processes write before they read: the send-send knot is refuted', expect: 'Process-network deadlock',
         src: tc("""class C {
                        static int badPC() {
                            AsyncChannel<Integer> pToC = AsyncChannel.create(0)
                            AsyncChannel<Integer> cToP = AsyncChannel.create(0)
                            async { pToC.send(1); int i = cToP.first() }
                            async { cToP.send(1); int j = pToC.first() }
                            return 0
                        }
                    }""")],
        // The book's fix: one side reads before it writes, and the knot is untied.
        [group: 'P272 rendezvous channels', name: 'one side reading first unties the knot: certified', ok: true,
         src: tc("""class C {
                        static int goodPC() {
                            AsyncChannel<Integer> pToC = AsyncChannel.create(0)
                            AsyncChannel<Integer> cToP = AsyncChannel.create(0)
                            async { pToC.send(1); int i = cToP.first() }
                            async { int j = pToC.first(); cToP.send(1) }
                            return 0
                        }
                    }""")],
        // The SAME shape on a buffered channel is not a deadlock and is not reported as one: the send is
        // queued and the Awaitable discarded, exactly as every earlier rung assumes. Capacity decides.
        [group: 'P272 rendezvous channels', name: 'the same write-first pair on a buffered channel is not a deadlock', ok: true,
         src: tc("""class C {
                        static int bufferedPC() {
                            AsyncChannel<Integer> pToC = AsyncChannel.create(1)
                            AsyncChannel<Integer> cToP = AsyncChannel.create(1)
                            async { pToC.send(1); int i = cToP.first() }
                            async { cToP.send(1); int j = pToC.first() }
                            return 0
                        }
                    }""")],

        // ---------- c07's second deadlock: the crossed client-server pair ----------
        // Each server serves its own client and then acts as a CLIENT of the other server — a cycle in the
        // client-server graph, which the design rule forbids. The two peer requests block on each other.
        [group: 'P272 rendezvous channels', name: 'crossed clients: two servers that are each other\'s client deadlock', expect: 'Process-network deadlock',
         src: tc("""class C {
                        static int crossedClients() {
                            AsyncChannel<Integer> c0ToS0 = AsyncChannel.create(0)
                            AsyncChannel<Integer> s0ToC0 = AsyncChannel.create(0)
                            AsyncChannel<Integer> c1ToS1 = AsyncChannel.create(0)
                            AsyncChannel<Integer> s1ToC1 = AsyncChannel.create(0)
                            AsyncChannel<Integer> s0ToS1 = AsyncChannel.create(0)
                            AsyncChannel<Integer> s1ToS0 = AsyncChannel.create(0)
                            async { c0ToS0.send(1); int r0 = s0ToC0.first() }
                            async { c1ToS1.send(2); int r1 = s1ToC1.first() }
                            async {                                          // server 0, also server 1's client
                                int q = c0ToS0.first()
                                s0ToS1.send(q)
                                int a = s1ToS0.first()
                                s0ToC0.send(a)
                            }
                            async {                                          // server 1, also server 0's client
                                int q = c1ToS1.first()
                                s1ToS0.send(q)
                                int a = s0ToS1.first()
                                s1ToC1.send(a)
                            }
                            return 0
                        }
                    }""")],
        // The design rule obeyed: server 1 is a PURE server, server 0 its only client. The client-server
        // graph is a DAG, the network certifies, and the value the client gets is proved end to end.
        [group: 'P272 rendezvous channels', name: 'a strict server hierarchy certifies, and the answer proves', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x + 1 })
                        static int layered(int x) {
                            AsyncChannel<Integer> c0ToS0 = AsyncChannel.create(0)
                            AsyncChannel<Integer> s0ToC0 = AsyncChannel.create(0)
                            AsyncChannel<Integer> s0ToS1 = AsyncChannel.create(0)
                            AsyncChannel<Integer> s1ToS0 = AsyncChannel.create(0)
                            async {                                          // server 0, client of server 1
                                int q = c0ToS0.first()
                                s0ToS1.send(q)
                                int a = s1ToS0.first()
                                s0ToC0.send(a)
                            }
                            async {                                          // server 1: a pure server
                                int q = s0ToS1.first()
                                s1ToS0.send(q + 1)
                            }
                            c0ToS0.send(x)                                   // the client
                            return s0ToC0.first()
                        }
                    }""")],
    ]
}
