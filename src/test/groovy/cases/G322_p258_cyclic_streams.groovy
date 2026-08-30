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
 * 'P258 cyclic streams' — loops that read each other's streams (the client–server pair, the ring, the fair
 * server) are modelled by RELY/GUARANTEE: a cycle member reads a partner's stream through a fresh rely view
 * constrained by the whole cycle's invariants, and what it has taken is a prefix of what its partner sent.
 * A request–reply claim closes across the cycle; a wrong one is refuted with a counterexample — where the
 * flattened model of Phase 255 was vacuous for any value claim in a cycle (a soundness find).
 */
class G322_p258_cyclic_streams {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 258 cyclic streams and conditional streams (slice 18 of the SEQ/PAR ladder): loops in a CYCLE (each reads a stream the other produces — the forever client–server, the primed cycle, the ring, the fair server) are verified by RELY/GUARANTEE. A cycle member reads a partner\'s stream through a fresh rely view constrained by every partner\'s invariants (fresh locals, cursors, lists) plus the FIFO law — what a consumer has TAKEN is a prefix of what its producer sent, the reader\'s own exact list where the reader is that producer — so a request–reply claim (`r == i + 1`) PROVES across the cycle and a wrong one is REFUTED with a counterexample (Phase 255\'s flattened model was vacuous for any value claim in a cycle: a soundness find). A GUARDED REPLY `if (r.index == b) Y.send(E)` in an ALT loop is a CONDITIONAL STREAM — one element per choice of branch b, its k-th element E over the k-th element taken from that branch — so the fair server verifies whole and each client proves what it is answered (claim-based select, Groovy 6.0.0-beta-4+; under the racing select a reply may answer another request, and the same claim is refuted). Loud boundaries: a cycle with a terminating member, a guarded reply with a second send, a reply computed from a loop-written value.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final String SERVER_HEAD = """
                            AsyncChannel<Integer> reqA = AsyncChannel.create(4)
                            AsyncChannel<Integer> reqB = AsyncChannel.create(4)
                            AsyncChannel<Integer> replyA = AsyncChannel.create(4)
                            AsyncChannel<Integer> replyB = AsyncChannel.create(4)"""

    static String clients(String claimA, String claimB) { """
                            async {                                              // client A
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    reqA.send(i)
                                    int r = replyA.first()
                                    ${claimA}
                                    i = i + 1
                                }
                            }
                            async {                                              // client B
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    reqB.send(i)
                                    int r = replyB.first()
                                    ${claimB}
                                    i = i + 1
                                }
                            }""" }

    static String server(String policy, String replyA, String replyB) { """
                            ChannelSelect alt = ChannelSelect.from(reqA, reqB)${policy}
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {                                       // the server
                                ChannelSelect.Result r = await alt.select()
                                int q = (int) r.value
                                if (r.index == 0) {
                                    replyA.send(${replyA})
                                }
                                if (r.index == 1) {
                                    replyB.send(${replyB})
                                }
                                j = j + 1
                            }""" }

    static final List<Map> CASES = [
        // ---------- the forever client–server: a request–reply claim closes across the cycle ----------
        [group: 'P258 cyclic streams', name: 'the forever client–server: each reply is its request plus one (proved across the cycle)', ok: true,
         src: tc("""class C {
                        static void clientServer() {
                            AsyncChannel<Integer> request = AsyncChannel.create(4)
                            AsyncChannel<Integer> reply = AsyncChannel.create(4)
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
                                assert r == i + 1
                                i = i + 1
                            }
                        }
                    }""")],
        // The soundness find: Phase 255's flattened model ran the server first over an empty request list, so
        // its exit facts contradicted the client's assumed reply and every claim after it was vacuous.
        [group: 'P258 cyclic streams', name: 'the forever client–server: a wrong reply claim is refuted (no longer vacuous)', expect: 'Assertion may not hold',
         src: tc("""class C {
                        static void clientServer() {
                            AsyncChannel<Integer> request = AsyncChannel.create(4)
                            AsyncChannel<Integer> reply = AsyncChannel.create(4)
                            async {
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
                            while (true) {
                                request.send(i)
                                int r = reply.first()
                                assert r == i + 2
                                i = i + 1
                            }
                        }
                    }""")],
        // A server that answers with a loop-written value: the count law holds, the element law does not exist.
        [group: 'P258 cyclic streams', name: 'a server answering with its own counter: the reply claim is refuted (no element law)', expect: 'Assertion may not hold',
         src: tc("""class C {
                        static void clientServer() {
                            AsyncChannel<Integer> request = AsyncChannel.create(4)
                            AsyncChannel<Integer> reply = AsyncChannel.create(4)
                            async {
                                int j = 0
                                int acc = 0
                                @Invariant({ j >= 0 })
                                while (true) {
                                    int q = request.first()
                                    acc = acc + q
                                    reply.send(acc)
                                    j = j + 1
                                }
                            }
                            int i = 0
                            @Invariant({ i >= 0 })
                            while (true) {
                                request.send(i)
                                int r = reply.first()
                                assert r == i
                                i = i + 1
                            }
                        }
                    }""")],
        // ---------- the fair server: guarded replies as conditional streams ----------
        [group: 'P258 cyclic streams', name: 'the fair server: each client is answered its own request plus one (claim-based select)',
         *: (CLAIM_SELECT ? [ok: true] : [expect: 'Cannot find matching method']),
         src: tc("""class C {
                        static void fairServer() {${SERVER_HEAD}${clients('assert r == i + 1', 'assert r == i + 1')}${server('.fair()', 'q + 1', 'q + 1')}
                        }
                    }""")],
        [group: 'P258 cyclic streams', name: 'the fair server: a wrong reply claim is refuted',
         *: (CLAIM_SELECT ? [expect: 'Assertion may not hold'] : [expect: 'Cannot find matching method']),
         src: tc("""class C {
                        static void fairServer() {${SERVER_HEAD}${clients('assert r == i + 1', 'assert r == i + 2')}${server('.fair()', 'q + 1', 'q + 1')}
                        }
                    }""")],
        // The priority server (both runtimes): the value model is the same; under the RACING select a losing
        // branch's element is re-sent to the back, so the k-th reply may answer another request — the claim
        // is refuted there and proved under the claim-based select. Per-client LIVENESS is withheld either
        // way (Phase 256: a priority select); what the value model adds is the safety of what is answered.
        [group: 'P258 cyclic streams', name: 'the priority server: the reply claim proves under the claim-based select, is refuted under the racing one',
         *: (CLAIM_SELECT ? [expect: 'served only when the ALT', refute: 'Assertion may not hold'] : [expect: 'Assertion may not hold']),
         src: tc("""class C {
                        static void server() {${SERVER_HEAD}${clients('assert r == i + 1', '')}${server('', 'q + 1', 'q + 1')}
                        }
                    }""")],
        // ---------- the loud boundaries ----------
        [group: 'P258 cyclic streams', name: 'a guarded reply with a second send outside the ALT is not a stream', expect: 'besides the one the ALT',
         *: (CLAIM_SELECT ? [:] : [expect: 'Cannot find matching method']),
         src: tc("""class C {
                        static void server() {${SERVER_HEAD}${clients('', '')}
                            replyA.send(0)
                            ${server('.fair()', 'q + 1', 'q + 1')}
                        }
                    }""")],
        [group: 'P258 cyclic streams', name: 'a cycle with a terminating member is a rung not built', expect: 'not all while (true)',
         src: tc("""class C {
                        static void clientServer(int n) {
                            AsyncChannel<Integer> request = AsyncChannel.create(4)
                            AsyncChannel<Integer> reply = AsyncChannel.create(4)
                            async {
                                int j = 0
                                @Invariant({ j >= 0 })
                                while (true) {
                                    int q = request.first()
                                    reply.send(q + 1)
                                    j = j + 1
                                }
                            }
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) {
                                request.send(i)
                                int r = reply.first()
                                i = i + 1
                            }
                        }
                    }""")],
    ]
}
