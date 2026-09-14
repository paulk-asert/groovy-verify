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
 * 'P295 branch replies' — an actor's reply inside a {@code choice}: the key/value actor that answers {@code get}
 * with a value and {@code put} with an acknowledgement. Which message a reply answers is decided PER TRACE rather
 * than by its label, so the branches may answer with different labels or with the SAME one — and the reply the
 * actor owes is the one for the message the protocol just delivered on this branch.
 */
class G345_p295_branch_replies {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 295 actor replies inside a choice: an actor role\'s reply is resolved to the message the protocol just delivered on THIS branch, not by a lookup on the reply\'s label — so a key/value actor answering `get` with \'value\' and `put` with \'ok\' is checked branch by branch, and two branches may equally share one \'ack\' label (which Phase 294 wrongly refused as ambiguous; par\'s own channel disjointness is what keeps a shared label unowed twice at once). A reactor that returns the other branch\'s label is a cross-wired reply and refutes; a branch whose message the actor defers is STUCK on that branch alone, with Phase 292 silent because an unstashAll() exists; a bare send in one branch is refuted in that branch. A message answered by two different labels is skipped loudly — a sendAndGet cannot know which reply to wait for.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    /** The key/value protocol: a choice the client makes, each branch a request answered by the actor. */
    static final String KV = '''@Protocol({
                            loop {
                                choice(at: client) {
                                    get: client >> gate
                                    value: gate >> client
                                } or {
                                    put: client >> gate
                                    ok: gate >> client
                                }
                            }
                        })'''

    static final String BOTH = "if (flag) { gate.sendAndGet('get').get() } else { gate.sendAndGet('put').get() }"

    static String kv(String arm, String sends = BOTH, String proto = KV) { """class C {
                        ${proto}
                        static void run(boolean flag) {
                            Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                                ${arm}
                            } as ReactorHandler<String, String>)
                            ${sends}
                        }
                    }""" }

    static final List<Map> CASES = [
        // ── each branch answered with its own label.
        [group: 'P295 branch replies', name: 'a key/value actor answering each branch with its own label conforms', ok: true,
         refute: ['Protocol violation', 'Skipped protocol check'],
         src: tc(kv("if (m == 'get') { return 'value' }\n                                'ok'"))],

        // ── both branches answered with the SAME label: a write-ack protocol. Phase 294 refused this as
        //    ambiguous; the reply is resolved by which message was just delivered, so it is not.
        [group: 'P295 branch replies', name: 'two branches sharing one reply label conform (the write-ack shape)', ok: true,
         refute: ['Protocol violation', 'Skipped protocol check', 'cannot know which reply'],
         src: tc(kv("'ack'", BOTH, '''@Protocol({
                            loop {
                                choice(at: client) {
                                    get: client >> gate
                                    ack: gate >> client
                                } or {
                                    put: client >> gate
                                    ack: gate >> client
                                }
                            }
                        })'''))],

        // ── the cross-wired reply, the Phase 264 fair-server bug in actor form: the get branch answered with
        //    the put branch's label.
        [group: 'P295 branch replies', name: 'a reactor answering get with the put branch\'s label is cross-wired',
         expect: "actor 'gate' replies 'ok' to 'get' in phase 'the handler' after it receives 'get' where the protocol's reply is 'value'",
         src: tc(kv("if (m == 'get') { return 'ok' }\n                                'ok'"))],

        // ── one branch deferred: STUCK on that branch only. Phase 292 is silent — an unstashAll() exists.
        [group: 'P295 branch replies', name: 'a branch whose message the actor defers is stuck on that branch alone',
         expect: "actor 'gate' defers 'put' in phase 'the handler' after it receives 'put', so the reply 'ok' its sendAndGet is waiting for is never produced: the conversation is STUCK",
         refute: 'Stashed messages are never replayed',
         src: tc(kv("if (m == 'get') { ctx.unstashAll(); return 'value' }\n                                ctx.stash()\n                                'ok'"))],

        // ── the peer's half, per branch: one branch that never opens a reply channel.
        [group: 'P295 branch replies', name: 'a bare send in one branch is refuted in that branch',
         expect: "the main body ends (it sends 'put' to 'gate') where the protocol still expects it to receive the reply 'ok' from 'gate' (a sendAndGet)",
         src: tc(kv("if (m == 'get') { return 'value' }\n                                'ok'",
                    "if (flag) { gate.sendAndGet('get').get() } else { gate.send('put') }"))],

        // ── the other direction MUST be unique: one message, one reply, or a sendAndGet cannot know what to await.
        [group: 'P295 branch replies', name: 'a message answered by two different labels is skipped loudly',
         expect: "message 'get' is answered both by 'value' and by 'other' — a sendAndGet cannot know which reply to wait for",
         src: tc(kv("'value'", "gate.sendAndGet('get').get()\n                            gate.sendAndGet('get').get()", '''@Protocol({
                            get: client >> gate
                            value: gate >> client
                            get: client >> gate
                            other: gate >> client
                        })'''))],
    ]
}
