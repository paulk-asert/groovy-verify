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
 * 'P294 actor replies' — the other direction of an actor's {@code @Protocol} role: its REPLY, the value a
 * {@code sendAndGet} is completed with. A reply is positional — {@code ack: gate >> client} answers the message
 * directly before it — so the peer must open a reply channel with {@code sendAndGet} rather than {@code send},
 * and the actor must actually produce it: a phase that DEFERS the answered message leaves the peer blocked on a
 * reply that never comes, which is a deadlock neither Phase 292 nor Phase 293 can see.
 */
class G344_p294_actor_replies {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 294 actor replies: an actor role\'s SEND in a @Protocol is its reply to the message directly before it (`req: client >> gate; ack: gate >> client`), the value a sendAndGet is completed with. The peer must open the reply channel — a bare send() where the protocol answers is a conformance violation naming the reply it can never receive — and the actor must produce it: a phase that defers the answered message leaves the peer blocked on a reply that never arrives and the conversation STUCK (measured: the reply completes only when the message is finally handled, and fails at stop() if it never is). For a reactor the handler\'s return IS the reply, so its literal is checked against the protocol\'s label; for a stateful actor the return is the new state, so the label is withheld and only the reply\'s production is checked. An actor send that answers nothing is skipped loudly.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final String REQ_REPLY = '''@Protocol({
                            req: client >> gate
                            ack: gate >> client
                            loop { cmd: client >> gate }
                        })'''

    /** A reactor request/reply actor: its handler's return is the reply. */
    static String reactor(String arm, String sends, String proto = REQ_REPLY) { """class C {
                        ${proto}
                        static void run() {
                            Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                                ${arm}
                                'done'
                            } as ReactorHandler<String, String>)
                            ${sends}
                        }
                    }""" }

    static final String ROUND_TRIP = "gate.sendAndGet('req').get()\n                            gate.send('cmd')"

    static final List<Map> CASES = [
        // ── the round trip conforms: sendAndGet opens the reply channel, the arm returns the protocol's label.
        [group: 'P294 actor replies', name: 'a reactor request/reply round trip conforms', ok: true,
         refute: ['Protocol violation', 'Skipped protocol check'],
         src: tc(reactor("if (m == 'req') { return 'ack' }", ROUND_TRIP))],

        // ── the peer never opens the reply channel: send() has none, so the promised reply cannot reach it.
        [group: 'P294 actor replies', name: 'a bare send where the protocol answers cannot receive the reply',
         expect: "the main body sends 'cmd' to 'gate' (line 15) after it sends 'req' to 'gate' where the protocol expects it to receive the reply 'ack' from 'gate' (a sendAndGet)",
         src: tc(reactor("if (m == 'req') { return 'ack' }", "gate.send('req')\n                            gate.send('cmd')"))],

        // ── the actor DEFERS the answered message: the peer blocks on a reply that never comes. The deadlock
        //    neither Phase 292 (an unstashAll exists) nor Phase 293 (nothing is left stashed at the end) sees.
        [group: 'P294 actor replies', name: 'a phase that defers the answered message leaves the peer stuck on its reply',
         expect: "actor 'gate' defers 'req' in phase 'waiting' after it receives 'req', so the reply 'ack' its sendAndGet is waiting for is never produced: the conversation is STUCK",
         refute: ['Stashed messages are never replayed', 'still stashed'],
         src: tc('''class C {
                        @Protocol({
                            req: client >> gate
                            ack: gate >> client
                            open: client >> gate
                        })
                        static void run() {
                            ReactorHandler<String, String> waiting, serving
                            serving = { ActorContext<String> ctx, String m -> 'ack' } as ReactorHandler<String, String>
                            waiting = { ActorContext<String> ctx, String m ->
                                if (m == 'open') { ctx.become(serving); ctx.unstashAll(); return 'ack' }
                                ctx.stash()
                                'ack'
                            } as ReactorHandler<String, String>
                            Actor<String> gate = Actor.reactor(waiting)
                            gate.sendAndGet('req').get()
                            gate.send('open')
                        }
                    }''')],

        // ── the reply's LABEL, for a reactor: the handler's return is what the sendAndGet is completed with.
        [group: 'P294 actor replies', name: 'a reactor that returns the wrong literal replies with the wrong label',
         expect: "actor 'gate' replies 'nak' to 'req' in phase 'the handler' after it receives 'req' where the protocol's reply is 'ack'",
         src: tc(reactor("if (m == 'req') { return 'nak' }", ROUND_TRIP))],

        // ── a stateful actor's return is the new STATE, not the reply: the label is withheld, the production checked.
        [group: 'P294 actor replies', name: 'a stateful actor\'s reply label is withheld (its return is the state)', ok: true,
         refute: ['Protocol violation', 'Skipped protocol check'],
         src: tc('''class C {
                        @Protocol({
                            req: client >> gate
                            ack: gate >> client
                            loop { cmd: client >> gate }
                        })
                        static void run() {
                            Actor<String> gate = Actor.stateful(0, { ActorContext<String> ctx, Integer s, String m -> s + 1 } as StatefulHandler<Integer, String>)
                            gate.sendAndGet('req').get()
                            gate.send('cmd')
                        }
                    }''')],

        // ── loud boundary: an actor send that answers nothing is not a reply.
        [group: 'P294 actor replies', name: 'an actor send that answers nothing is skipped loudly',
         expect: "role 'gate' is an actor that sends 'ping' where it answers nothing — an actor's only send is the reply to the message directly before it",
         src: tc('''class C {
                        @Protocol({
                            ping: gate >> client
                            go: client >> gate
                        })
                        static void run() {
                            Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m -> 'ack' } as ReactorHandler<String, String>)
                            gate.send('go')
                        }
                    }''')],
    ]
}
