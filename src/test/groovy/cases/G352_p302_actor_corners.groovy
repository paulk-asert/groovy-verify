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
 * 'P302 actor corners' — the withheld corners the Actor phases left behind, closed. A DEFAULT branch that
 * {@code become}s is an ordinary edge of the graph, not a reason to withhold the whole of it; an {@code onError}
 * that arms a timer arms it wherever the error fires; and a {@code sendAndGet}'s reply is received however the
 * {@code Awaitable} is used, which turned out to need cases rather than machinery.
 */
class G352_p302_actor_corners {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 302 the withheld actor corners: a DEFAULT branch that becomes ("anything else moves me on") is read as an ordinary edge of the become-graph rather than withholding the whole graph, so the protocol check and the timers follow it; an onError callback that arms a timer arms it wherever the error fires, so the timer is checked against the phase the callback recovers into — or against every phase, when the callback takes no context and cannot become. And a sendAndGet receives the reply the protocol promises however its Awaitable is used — read at the site, bound and never read, discarded outright, or passed to another method — which was already true and is now pinned, with a plain send() as the control that refutes.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    /** A client whose `use` of sendAndGet varies; the protocol answers 'req' with 'ack'. */
    static String client(String use) { """class C {
                        @Protocol({ req: client >> gate; ack: gate >> client; loop { cmd: client >> gate } })
                        static void run() {
                            Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                                if (m == 'req') { return 'ack' }
                                'done'
                            } as ReactorHandler<String, String>)
                            ${use}
                            gate.send('cmd')
                        }
                        static void helper(Awaitable<String> a) { }
                    }""" }

    static final List<Map> CASES = [
        // ── a DEFAULT that becomes: the graph is read, and the protocol check follows the edge.
        [group: 'P302 actor corners', name: 'a default branch that becomes is an edge of the graph, not a reason to withhold it',
         expect: "actor 'gate' rejects 'cmd' in phase 'later' (its default branch throws) after it receives 'go'",
         refute: 'not all visible',
         src: tc('''class C {
                        @Protocol({ go: client >> gate; loop { cmd: client >> gate } })
                        static void run() {
                            ReactorHandler<String, String> later
                            later = { ActorContext<String> ctx, String m -> throw new IllegalStateException('x') } as ReactorHandler<String, String>
                            Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                                if (m == 'never') { return m }
                                ctx.become(later)
                                m
                            } as ReactorHandler<String, String>)
                            gate.send('go')
                            gate.send('cmd')
                        }
                    }''')],

        // ── the same shape where the moving default is fine: nothing is claimed against it.
        [group: 'P302 actor corners', name: 'a moving default whose target handles what follows conforms', ok: true,
         refute: ['Protocol violation', 'Skipped protocol check'],
         src: tc('''class C {
                        @Protocol({ go: client >> gate; loop { cmd: client >> gate } })
                        static void run() {
                            ReactorHandler<String, String> later
                            later = { ActorContext<String> ctx, String m -> m } as ReactorHandler<String, String>
                            Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                                if (m == 'never') { return m }
                                ctx.become(later)
                                m
                            } as ReactorHandler<String, String>)
                            gate.send('go')
                            gate.send('cmd')
                        }
                    }''')],

        // ── an onError that arms a timer: armed wherever the error fires, checked against the recovery phase.
        [group: 'P302 actor corners', name: 'a timer armed by an onError is checked against the phase it recovers into',
         expect: "Scheduled message rejected by its own actor: 'gate' in run() schedules 'tick' for itself (line 9, repeating)",
         src: tc('''class C {
                        static void run() {
                            ReactorHandler<String, String> later
                            later = { ActorContext<String> ctx, String m -> throw new IllegalStateException('x') } as ReactorHandler<String, String>
                            Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m -> m } as ReactorHandler<String, String>)
                            gate.onError({ ActorContext<String> ctx, Throwable t, String msg ->
                                ctx.scheduleAtFixedRate('tick', Duration.ofMillis(50), Duration.ofMillis(50))
                                ctx.become(later)
                            } as TriConsumer<ActorContext<String>, Throwable, String>)
                            gate.send('a')
                        }
                    }''')],

        // ── the same, where the recovery phase handles the tick: left alone.
        [group: 'P302 actor corners', name: 'a timer armed by an onError whose recovery phase handles it is left alone', ok: true,
         refute: ['Scheduled message', 'Unbounded stash'],
         src: tc('''class C {
                        static void run() {
                            ReactorHandler<String, String> later
                            later = { ActorContext<String> ctx, String m -> m } as ReactorHandler<String, String>
                            Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m -> m } as ReactorHandler<String, String>)
                            gate.onError({ ActorContext<String> ctx, Throwable t, String msg ->
                                ctx.scheduleAtFixedRate('tick', Duration.ofMillis(50), Duration.ofMillis(50))
                                ctx.become(later)
                            } as TriConsumer<ActorContext<String>, Throwable, String>)
                            gate.send('a')
                        }
                    }''')],

        // ── the reply is received however the Awaitable is used. Four spellings, one control.
        [group: 'P302 actor corners', name: 'a sendAndGet read at the site receives its reply', ok: true,
         refute: ['Protocol violation', 'Skipped protocol check'], src: tc(client("gate.sendAndGet('req').get()"))],
        [group: 'P302 actor corners', name: 'a sendAndGet bound but never read still receives its reply', ok: true,
         refute: ['Protocol violation', 'Skipped protocol check'], src: tc(client("def a = gate.sendAndGet('req')"))],
        [group: 'P302 actor corners', name: 'a sendAndGet discarded outright still receives its reply', ok: true,
         refute: ['Protocol violation', 'Skipped protocol check'], src: tc(client("gate.sendAndGet('req')"))],
        [group: 'P302 actor corners', name: 'a sendAndGet passed to another method still receives its reply', ok: true,
         refute: ['Protocol violation', 'Skipped protocol check'], src: tc(client("helper(gate.sendAndGet('req'))"))],
        [group: 'P302 actor corners', name: 'the control: a plain send opens no reply channel and is refuted',
         expect: "where the protocol expects it to receive the reply 'ack' from 'gate' (a sendAndGet)",
         src: tc(client("gate.send('req')"))],
    ]
}
