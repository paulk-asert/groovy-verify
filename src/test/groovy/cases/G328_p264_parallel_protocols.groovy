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
 * 'P264 parallel protocols' — the fair server's session type. Not a choice one role makes: two independent
 * request–reply sessions interleaved at the server — `par { … } and { … }` (channels disjoint), projected
 * as the SHUFFLE of the parts' projections. The ALT server is one conformant implementation; a cross-wired
 * reply falls outside the shuffle, with its trace.
 */
class G328_p264_parallel_protocols {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 264 parallel protocols (slice 24 of the SEQ/PAR ladder): `par { … } and { … }` composes INDEPENDENT sub-sessions (their channels disjoint — enforced) and projects as the SHUFFLE of the parts\' projections, a product automaton the same inclusion check decides. The fair server finally has its session type — not a `choice at` one role makes (Phase 263\'s loud boundary, which stands for genuinely mixed choice), but two request–reply loops interleaved at the server: each client plays its own part, the server plays the shuffle, and its ALT — take whichever request is ready, reply on that client\'s channel — is one conformant implementation. A server that answers the wrong client (replyB for reqA) falls outside the shuffle and is named with the trace that reaches it; parts that share a channel are refused (independent sub-sessions only). Conformance is the protocol\'s ORDER only: the selection-policy liveness verdicts (Phases 256/257) stand separately, so the same typed server is certified live with a held fair() on Groovy 6.0.0-beta-4+ and withheld under priority — the layers say different things about one program.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final String PAR_PROTO = """@Protocol('''
                            par {
                                loop {
                                    reqA:   clientA -> server
                                    replyA: server -> clientA
                                }
                            } and {
                                loop {
                                    reqB:   clientB -> server
                                    replyB: server -> clientB
                                }
                            }
                        ''')"""

    static String fairServer(String proto, String select, String replyA = 'replyA', String replyB = 'replyB') { """class C {
                        ${proto}
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
                            ${select}
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {                                       // the server
                                ChannelSelect.Result r = await ${select.isEmpty() ? 'ChannelSelect.from(reqA, reqB)' : 'alt'}.select()
                                int q = (int) r.value
                                if (r.index == 0) {
                                    ${replyA}.send(q + 1)
                                }
                                if (r.index == 1) {
                                    ${replyB}.send(q + 1)
                                }
                                j = j + 1
                            }
                        }
                    }""" }

    static final List<Map> CASES = [
        // The fair server, typed: with a held fair() on the claim runtime the whole method is clean —
        // conformant to the shuffle AND certified live; before beta-4 fair() is a type error.
        [group: 'P264 parallel protocols', name: 'the fair server conforms to its par protocol (held fair(): clean on Groovy 6.0.0-beta-4+)',
         *: (CLAIM_SELECT ? [ok: true] : [expect: 'Cannot find matching method']),
         src: tc(fairServer(PAR_PROTO, 'ChannelSelect alt = ChannelSelect.from(reqA, reqB).fair()   // held'))],
        // The layers say different things: under a priority select the ORDER conforms while per-client
        // liveness is withheld (Phase 256) — on both runtimes.
        [group: 'P264 parallel protocols', name: 'under a priority select the order conforms while liveness is withheld — separate layers', expect: 'served only when the ALT', refute: 'Protocol violation',
         src: tc(fairServer(PAR_PROTO, ''))],
        [group: 'P264 parallel protocols', name: 'a cross-wired server (replyB for reqA) falls outside the shuffle, with its trace', expect: 'Protocol violation',
         src: tc(fairServer(PAR_PROTO, '', 'replyB', 'replyA'))],
        [group: 'P264 parallel protocols', name: 'parts that share a channel are refused: independent sub-sessions only', expect: 'must not share a channel',
         src: tc(fairServer("""@Protocol('''
                            par {
                                loop { reqA: clientA -> server; replyA: server -> clientA }
                            } and {
                                loop { reqA: clientB -> server; replyB: server -> clientB }
                            }
                        ''')""", ''))],
    ]
}
