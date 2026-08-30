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
 * 'P267 mixed choice' — `choice { … } or { … }` with no `at`: branches opened by different roles, the race.
 * Projection is the mixed union for an opener; the missing half is COHERENCE across the processes: two
 * peers that can both send their openers collide (buffered sends both succeed, the peers proceed down
 * different branches, and no output guards exist to arbitrate — the reason occam banned them); exactly one
 * initiator degenerates the choice to that role, certified; none, and the conversation can never take it.
 */
class G331_p267_mixed_choice {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 267 mixed choice (slice 27 of the SEQ/PAR ladder): `choice { ping: left -> right } or { pong: right -> left }` — no `at`, branches opened by DIFFERENT roles: the race, the classic boundary of session-type projection. The projection side is the easy half (an opener\'s local type is the mixed union; a bystander must still tell the branches apart); what mixed choice breaks is that LOCAL conformance stops implying GLOBAL coherence — each peer can conform alone while together they collide. The checker adds the missing half, a COHERENCE check across the bound processes: two peers that can both SEND their openers are refused with the collision named (buffered sends both succeed and the peers proceed down different branches; no output guards exist to arbitrate a race — the reason occam banned them, and ChannelSelect offers input guards only); EXACTLY ONE initiator degenerates the mixed choice to a choice at that role, certified silently; NONE, and the conversation can never take it — said. A conformant process may use a strict subset of its role\'s alphabet (the branch it never takes), so binding falls back from exact to unique-subset. True racing arbitration is a RUNTIME feature (output guards / two-phase commit), not a checker gap — the boundary moves to the runtime, as it did with GROOVY-12320.'

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

    static String peers(String left, String right) { """class C {
                        ${MIXED}
                        static void peers() {
                            AsyncChannel<Integer> ping = AsyncChannel.create(4)
                            AsyncChannel<Integer> pong = AsyncChannel.create(4)
                            async {                                              // left
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    ${left}
                                    i = i + 1
                                }
                            }
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {                                       // right
                                ${right}
                                j = j + 1
                            }
                        }
                    }""" }

    static final List<Map> CASES = [
        // Each peer conforms alone; together they collide — the race, refused with both initiators named.
        [group: 'P267 mixed choice', name: 'two initiators collide: each conforms alone, together they race — refused', expect: 'two initiators',
         src: tc(peers('ping.send(i)', 'pong.send(j)'))],
        [group: 'P267 mixed choice', name: 'one initiator: the mixed choice degenerates to a choice at that role — certified', ok: true,
         src: tc(peers('ping.send(i)', 'int x = ping.first()'))],
        [group: 'P267 mixed choice', name: 'no initiator: the conversation can never take the choice — said', expect: 'no process opens the mixed choice',
         src: tc(peers('int x = pong.first()', 'int y = ping.first()'))],
        // Same opener on both branches is not mixed at all: an internal choice, checked as before.
        // The client's sends sit inside if/else, so the channel VALUE model skips loudly (its boundary since
        // Phase 250) — the protocol layer is what this case watches: no violation.
        [group: 'P267 mixed choice', name: 'both branches from one role is an internal choice, not a mixed one', expect: 'Skipped channel verification', refute: 'Protocol violation',
         src: tc("""class C {
                        @Protocol({
                            loop {
                                choice {
                                    add: client >> server
                                } or {
                                    neg: client >> server
                                }
                            }
                        })
                        static void calc() {
                            AsyncChannel<Integer> add = AsyncChannel.create(4)
                            AsyncChannel<Integer> neg = AsyncChannel.create(4)
                            async {                                              // the client chooses
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    if (i % 2 == 0) {
                                        add.send(i)
                                    } else {
                                        neg.send(i)
                                    }
                                    i = i + 1
                                }
                            }
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {                                       // the server offers
                                ChannelSelect.Result r = await ChannelSelect.from(add, neg).select()
                                int v = (int) r.value
                                j = j + 1
                            }
                        }
                    }""")],
        // `choice at` with a foreign opener now points at the mixed spelling.
        [group: 'P267 mixed choice', name: 'a choice at one role opened by another points at the mixed spelling', expect: "write it without 'at'",
         src: tc(peers('ping.send(i)', 'int x = ping.first()').replace('choice {', 'choice(at: left) {'))],
    ]
}
