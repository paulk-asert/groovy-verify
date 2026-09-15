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
 * 'P296 actor onError' — {@code onError} as the become-graph's RECOVERY edge, and the one thing it cannot do.
 * Measured: the callback fires wherever the throw happens (inside a {@code become} target too, so the edge is the
 * ACTOR's, not a phase's), its {@code ctx.become(…)} takes effect for the next message, and the actor survives a
 * throw with or without one. So a callback does not make a throw CONFORMANT — the message the protocol delivered
 * is lost either way — it makes the report precise: the error is observed, and the actor carries on in a named
 * phase. The one thing it cannot do is rescue a reply: a {@code sendAndGet} fails with the error either way.
 */
class G346_p296_actor_on_error {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 296 actor onError: what the callback installed with `actor.onError(\u2026)` does and does not buy you. Measured: it fires wherever the throw happens (inside a become target too, so the edge is the ACTOR\'s, not a phase\'s), its ctx.become(\u2026) takes effect for the next message, the actor survives a throw with or without one, and a stateful actor\'s state is simply not advanced by the failed dispatch. So a callback does NOT make a throw conformant \u2014 a message the protocol delivered and the actor threw on was never processed either way \u2014 but it changes what the report can say: the error is observed and the actor carries on in a NAMED recovery phase (or stays put, for a two-parameter callback with no context), instead of Phase 293\'s bare rejection. What a callback cannot do is rescue a promised reply: the sendAndGet fails with that error either way, said explicitly because the callback makes it look handled. A throwing ARM is now read as well as a throwing default. A callback that defers, replays, hands its context on, or is installed twice withholds the whole graph.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    /** A two-phase actor whose `risky` arm throws; `recover` is the onError callback, `safeArm` the safe phase. */
    static String actor(String recover, String proto, String safeArm = "s", String sends = "gate.send('risky')\n                            gate.send('cmd')") { """class C {
                        ${proto}
                        static void run() {
                            StatefulHandler<Integer, String> safe
                            safe = { ActorContext<String> ctx, Integer s, String m -> ${safeArm} } as StatefulHandler<Integer, String>
                            Actor<String> gate = Actor.stateful(0, { ActorContext<String> ctx, Integer s, String m ->
                                if (m == 'risky') { throw new IllegalStateException('boom') }
                                s
                            } as StatefulHandler<Integer, String>)
                            gate.onError(${recover})
                            ${sends}
                        }
                    }""" }

    static final String PLAIN = '''@Protocol({
                            risky: client >> gate
                            loop { cmd: client >> gate }
                        })'''

    static final String BECOME_SAFE = "{ ActorContext<String> ctx, Throwable t, String msg -> ctx.become(safe) } as groovy.util.function.TriConsumer<ActorContext<String>, Throwable, String>"

    static final List<Map> CASES = [
        // ── a callback does not make the throw conformant: the message the protocol delivered is still gone.
        //    What it buys is the report — the error is observed, and the actor carries on in a named phase.
        //    (The throwing ARM is itself new: Phase 293 could only read a throwing default.)
        [group: 'P296 actor onError', name: 'a throw an onError observes is still a message the protocol delivered and lost',
         expect: "actor 'gate' throws on 'risky' in phase 'the handler' at the start (its 'risky' branch throws): its onError observes the error and the actor carries on in phase 'safe', but the message the protocol delivered is never processed",
         refute: 'rejects',
         src: tc(actor(BECOME_SAFE, PLAIN))],

        // ── a callback on an actor that never throws changes nothing.
        [group: 'P296 actor onError', name: 'a callback on an actor that never throws changes nothing', ok: true,
         refute: ['Protocol violation', 'Skipped protocol check'],
         src: tc('''class C {
                        @Protocol({
                            risky: client >> gate
                            loop { cmd: client >> gate }
                        })
                        static void run() {
                            StatefulHandler<Integer, String> safe
                            safe = { ActorContext<String> ctx, Integer s, String m -> s } as StatefulHandler<Integer, String>
                            Actor<String> gate = Actor.stateful(0, { ActorContext<String> ctx, Integer s, String m -> s } as StatefulHandler<Integer, String>)
                            gate.onError({ ActorContext<String> ctx, Throwable t, String msg -> ctx.become(safe) } as groovy.util.function.TriConsumer<ActorContext<String>, Throwable, String>)
                            gate.send('risky')
                            gate.send('cmd')
                        }
                    }''')],

        // ── the thing onError cannot do: a promised reply fails with the error either way (measured).
        [group: 'P296 actor onError', name: 'an onError cannot rescue the reply the protocol promises',
         expect: "and the reply 'ack' the protocol promises fails with that error too — an onError cannot rescue it",
         src: tc(actor(BECOME_SAFE, '''@Protocol({
                            risky: client >> gate
                            ack: gate >> client
                            loop { cmd: client >> gate }
                        })''', "s", "gate.sendAndGet('risky').get()\n                            gate.send('cmd')"))],

        // ── a two-parameter callback has no context, so the actor stays where it is: the SAME phase must then
        //    take what follows, and this one throws on everything.
        [group: 'P296 actor onError', name: 'a callback with no context leaves the actor in the phase that threw',
         expect: "its onError observes the error and the actor stays in it (its callback takes no context, so it cannot become another)",
         src: tc('''class C {
                        @Protocol({
                            risky: client >> gate
                            loop { cmd: client >> gate }
                        })
                        static void run() {
                            Actor<String> gate = Actor.stateful(0, { ActorContext<String> ctx, Integer s, String m ->
                                throw new IllegalStateException('boom')
                            } as StatefulHandler<Integer, String>)
                            gate.onError({ Throwable t, String msg -> } as java.util.function.BiConsumer<Throwable, String>)
                            gate.send('risky')
                            gate.send('cmd')
                        }
                    }''')],

        // ── with NO callback a throw is still a bare rejection: the callback is what changes the verdict.
        [group: 'P296 actor onError', name: 'without a callback the same throw is still a bare rejection',
         expect: "actor 'gate' rejects 'risky' in phase 'the handler'",
         src: tc('''class C {
                        @Protocol({
                            risky: client >> gate
                            loop { cmd: client >> gate }
                        })
                        static void run() {
                            Actor<String> gate = Actor.stateful(0, { ActorContext<String> ctx, Integer s, String m ->
                                if (m == 'risky') { throw new IllegalStateException('boom') }
                                s
                            } as StatefulHandler<Integer, String>)
                            gate.send('risky')
                            gate.send('cmd')
                        }
                    }''')],

        // ── loud boundary: a callback that replays the stash is Phase 292's business, not modelled here.
        [group: 'P296 actor onError', name: 'a callback that replays the stash withholds the whole graph',
         expect: "the behaviours of actor 'gate' are not all visible",
         src: tc(actor("{ ActorContext<String> ctx, Throwable t, String msg -> ctx.unstashAll() } as groovy.util.function.TriConsumer<ActorContext<String>, Throwable, String>", PLAIN))],
    ]
}
