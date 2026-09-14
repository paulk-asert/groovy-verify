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
 * 'P293 actor protocol' — {@code become} conformance, the Actor surface's third property, with the stock
 * {@code @Protocol}: a role named after an actor local is played by that actor's become-graph, and a message to it
 * is labelled by the literal sent. Both sides are checked: the method's sends against the sender's projection
 * (Phase 263's conformance, unchanged), and the become-graph against the actor's — the other way round, since an
 * actor does not choose what arrives: every message the protocol delivers must be taken, stashes must be replayed
 * before the conversation can end, and a stash must not grow without bound.
 */
class G343_p293_actor_protocol {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 293 actor protocol conformance: a @Protocol role named after an actor local is played by the actor\'s become-graph (phases = the handler and its become targets, arms = `if (m == LIT)` branches, a default that handles / stashes / throws), a message to it labelled by the literal sent. The method\'s sends are checked against the sender\'s projection (Phase 263\'s conformance), and the become-graph against the actor\'s the other way round — every delivered message must be taken (a throwing default rejects it), a stash must be replayed before the conversation can end (a stash is rejected at stop(), measured), and a phase the protocol keeps stashing into grows without bound. A trigger literal that does not match its label, a sender out of order, and a phase that throws on a protocol message are refuted; deferral that is replayed in time conforms; an actor whose behaviours are not all visible, or that replies, is skipped loudly.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final String PROTO = '''@Protocol({
                            connect: client >> gate
                            auth_ok: client >> gate
                            loop { cmd: client >> gate }
                        })'''

    /** The Groovy docs' three-phase connection actor, `authArm` its authenticating phase's trigger branch. */
    static String actor(String authArm, String sends, String proto = PROTO, String connectedBody = 's + 1') { """class C {
                        ${proto}
                        static void run() {
                            StatefulHandler<Integer, String> disconnected, authenticating, connected
                            disconnected = { ActorContext<String> ctx, Integer s, String m ->
                                if (m == 'connect') { ctx.become(authenticating); return s }
                                s
                            } as StatefulHandler<Integer, String>
                            authenticating = { ActorContext<String> ctx, Integer s, String m ->
                                ${authArm}
                                ctx.stash()
                                s
                            } as StatefulHandler<Integer, String>
                            connected = { ActorContext<String> ctx, Integer s, String m -> ${connectedBody} } as StatefulHandler<Integer, String>
                            Actor<String> gate = Actor.stateful(0, disconnected)
                            ${sends}
                        }
                    }""" }

    static final String AUTH_OK = "if (m == 'auth_ok') { ctx.become(connected); ctx.unstashAll(); return s }"
    static final String IN_ORDER = "gate.send('connect')\n                            gate.send('auth_ok')\n                            gate.send('cmd')"

    static final List<Map> CASES = [
        // ── the documented actor conforms on both sides.
        [group: 'P293 actor protocol', name: 'the three-phase connection actor conforms to its protocol', ok: true,
         refute: ['Protocol violation', 'Skipped protocol check'],
         src: tc(actor(AUTH_OK, IN_ORDER))],

        // ── the SENDER out of order: Phase 263's conformance, now over messages to an actor.
        [group: 'P293 actor protocol', name: 'a sender that sends cmd before auth_ok violates the client role',
         expect: "Protocol violation in run (role 'client'): the main body sends 'cmd' to 'gate'",
         src: tc(actor(AUTH_OK, "gate.send('connect')\n                            gate.send('cmd')\n                            gate.send('auth_ok')"))],

        // ── the ACTOR: a trigger literal that does not match its label. The phase never transitions, so the
        //    protocol's auth_ok is stashed with everything after it. Phase 292 cannot see this — an unstashAll exists.
        [group: 'P293 actor protocol', name: 'a trigger literal that misses its label stashes the protocol\'s own message',
         expect: "actor 'gate' can reach the end of the conversation in phase 'authenticating' after it receives 'connect', then 'auth_ok' with 'auth_ok' still stashed",
         refute: 'Stashed messages are never replayed',
         src: tc(actor("if (m == 'auth-ok') { ctx.become(connected); ctx.unstashAll(); return s }", IN_ORDER))],

        // ── the ACTOR rejects: the connected phase throws on anything but cmd, and the protocol also sends ping.
        [group: 'P293 actor protocol', name: 'a phase whose default throws rejects a message the protocol delivers',
         expect: "actor 'gate' rejects 'ping' in phase 'connected' (its default branch throws)",
         src: tc(actor(AUTH_OK, IN_ORDER, '''@Protocol({
                            connect: client >> gate
                            auth_ok: client >> gate
                            loop {
                                choice(at: client) {
                                    cmd: client >> gate
                                } or {
                                    ping: client >> gate
                                }
                            }
                        })''', "if (m == 'cmd') { return s + 1 }\n                                throw new IllegalStateException('unexpected ' + m)"))],

        // ── deferral that is replayed in time conforms: cmd arrives during authentication, is stashed, and
        //    auth_ok's replay dispatches it to the connected phase.
        [group: 'P293 actor protocol', name: 'a message deferred during authentication and replayed by auth_ok conforms', ok: true,
         refute: ['Protocol violation', 'Skipped protocol check'],
         src: tc(actor(AUTH_OK, "gate.send('connect')\n                            gate.send('cmd')\n                            gate.send('auth_ok')", '''@Protocol({
                            connect: client >> gate
                            cmd: client >> gate
                            auth_ok: client >> gate
                            loop { cmd: client >> gate }
                        })'''))],

        // ── loud boundaries: behaviours that are not all visible, and an actor that replies.
        [group: 'P293 actor protocol', name: 'an actor with an opaque become target is skipped loudly',
         expect: "Skipped protocol check for run (the behaviours of actor 'gate' are not all visible",
         src: tc('''class C {
                        @Protocol({ go: client >> gate })
                        static void run() {
                            Actor<String> gate = Actor.stateful(0, { ActorContext<String> ctx, Integer s, String m ->
                                if (m == 'go') { ctx.become(elsewhere()); return s }
                                s
                            } as StatefulHandler<Integer, String>)
                            gate.send('go')
                        }
                        static StatefulHandler<Integer, String> elsewhere() {
                            { ActorContext<String> c, Integer s, String m -> s } as StatefulHandler<Integer, String>
                        }
                    }''')],
        [group: 'P293 actor protocol', name: 'an actor that replies is skipped loudly (only receives are modelled)',
         expect: "role 'gate' is an actor that SENDS ('ack')",
         src: tc('''class C {
                        @Protocol({
                            go: client >> gate
                            ack: gate >> client
                        })
                        static void run() {
                            Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m -> m } as ReactorHandler<String, String>)
                            gate.send('go')
                        }
                    }''')],
    ]
}
