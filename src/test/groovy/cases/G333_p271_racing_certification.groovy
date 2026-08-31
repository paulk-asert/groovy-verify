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
 * 'P271 racing certification' — the racing mixed choice, certified: on a runtime carrying GROOVY-12323's
 * arbitrated select, two initiators are coherent when every one opens ONLY through offers(send(…),
 * receive(…)).select() and every opener channel is rendezvous (AsyncChannel.create(0)); anything less is
 * refused with the exact missing piece. The boundary that was refused in Phase 267 and proposed upstream
 * in Phase 268, now closed the way Phases 257/271 close: modelled where it runs.
 */
class G333_p271_racing_certification {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 271 the racing mixed choice, certified (slice 32 of the SEQ/PAR ladder): on a runtime carrying GROOVY-12323\'s arbitrated select (probed: ChannelSelect.offers exists ⇒ CaseDsl.ARBITRATED_SELECT), Phase 267\'s coherence check gains its second certified outcome — TWO initiators are coherent when every one of them opens ONLY through `offers(send(…), receive(…)).select()` (never a bare send) and every opener channel is RENDEZVOUS (`AsyncChannel.create(0)`): the empirics behind the conditions are GROOVY-12323\'s own — a raced rendezvous mixed choice commits exactly one branch every time, while a buffered send offer commits unilaterally and the collision reproduces through the API (the documented caveat, made mechanical here). Refusals name the exact missing piece: a bare-send opener ("un-arbitrated"), a buffered opener (the capacity, with the caveat quoted), and on a pre-12323 runtime the offers spelling is a type error. The SessionChecker reads the offers-select as a first-class process op (send offers are `!c` automaton edges), so binding and conformance see the racing peers as the roles they play.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final String MIXED = """@Protocol({
                            loop {
                                choice {
                                    ping: left >> right
                                } or {
                                    pong: right >> left
                                }
                            }
                        })"""

    static String peers(String capPing, String capPong, String leftOpen, String rightOpen) { """class C {
                        ${MIXED}
                        static void peers() {
                            AsyncChannel<Integer> ping = AsyncChannel.create(${capPing})
                            AsyncChannel<Integer> pong = AsyncChannel.create(${capPong})
                            async {                                              // left
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    ${leftOpen}
                                    i = i + 1
                                }
                            }
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {                                       // right
                                ${rightOpen}
                                j = j + 1
                            }
                        }
                    }""" }

    static final String LEFT_OFFERS = """ChannelSelect.Result r = await ChannelSelect.offers(ChannelSelect.send(ping, i), ChannelSelect.receive(pong)).select()
                                    if (r.index == 1) {
                                        int v = (int) r.value
                                    }"""
    static final String RIGHT_OFFERS = """ChannelSelect.Result r = await ChannelSelect.offers(ChannelSelect.send(pong, j), ChannelSelect.receive(ping)).select()
                                if (r.index == 1) {
                                    int v = (int) r.value
                                }"""

    static final List<Map> CASES = [
        // The certified race: both peers may open, the select arbitrates, the openers are rendezvous.
        [group: 'P271 racing certification', name: 'the racing pair through arbitrated selects over rendezvous channels: coherent, certified',
         *: (ARBITRATED_SELECT ? [expect: 'outside fragment in loop body', refute: 'Protocol violation'] : [expect: 'Cannot find matching method']),
         src: tc(peers('0', '0', LEFT_OFFERS, RIGHT_OFFERS))],
        // Buffered openers: the collision reproduces through the API — the capacity is part of the certificate.
        [group: 'P271 racing certification', name: 'buffered openers are refused with the caveat: the racing openers must be rendezvous',
         *: (ARBITRATED_SELECT ? [expect: 'must be rendezvous'] : [expect: 'Cannot find matching method']),
         src: tc(peers('4', '4', LEFT_OFFERS, RIGHT_OFFERS))],
        // A bare-send opener bypasses the arbitration entirely.
        [group: 'P271 racing certification', name: 'a bare-send opener is refused: un-arbitrated',
         *: (ARBITRATED_SELECT ? [expect: 'bare send'] : [expect: 'Cannot find matching method']),
         src: tc(peers('0', '0', 'ping.send(i)', RIGHT_OFFERS))],
    ]
}
