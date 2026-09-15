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
 * 'P298 actor fields' — the actor held in a FIELD, which is the shape real code is written in: a service class
 * owns the actor and its methods send to it. Every actor check before this one read a METHOD body, so all of
 * them — the stash, the timers, the whole {@code @Protocol} stack — were silent on exactly that shape. A field
 * initialiser IS a declaration, so presenting the class's initialisers as one lets the existing machinery read a
 * class unchanged; what is new is WHERE the findings are raised. A behaviour-graph finding belongs to the class,
 * not to any one method that happens to mention the actor, so it is reported once however many methods do.
 */
class G348_p298_actor_fields {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 298 the actor as a field: an actor declared in a field initialiser, with its behaviours as fields too, is now read by the whole Actor gallery — the stash check (292), the timers (297) and the @Protocol stack (293-296) — where before every one of them was silent because they each read a single METHOD body. A field initialiser is a declaration, so the class\'s initialisers are presented as one and the existing machinery reads a class unchanged. The behaviour-graph findings (stash never replayed, the timers) are about the actor rather than about any method, so they are raised once for the CLASS and named as such however many methods send to it; the protocol checks stay per method, with the field actor playing its role. A phase graph with a CYCLE cannot be written as initialisers (it needs declare-then-assign, in a constructor or an init block) and is simply not found — open.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [
        // ── the reach this phase exists for: the identical defect Phase 292 refutes for a local, now as a field,
        //    and reported ONCE for the class though two methods send to it.
        [group: 'P298 actor fields', name: 'a field-held actor that stashes without replay is refuted, once for the class',
         expect: "Stashed messages are never replayed: actor 'gate' in the class C stashes (line 5)",
         src: tc('''class C {
                        static Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                            ctx.stash()
                            m
                        } as ReactorHandler<String, String>)
                        static void run() { gate.send('a') }
                        static void other() { gate.send('b') }
                    }''')],

        // ── a clean field-held actor is left alone.
        [group: 'P298 actor fields', name: 'a field-held actor with nothing wrong is left alone', ok: true,
         refute: ['Stashed messages', 'Scheduled message', 'Unbounded stash'],
         src: tc('''class C {
                        static Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m -> m } as ReactorHandler<String, String>)
                        static void run() { gate.send('a') }
                    }''')],

        // ── the become-graph across FIELDS: a timer armed in one field's behaviour, landing in another's.
        [group: 'P298 actor fields', name: 'a timer armed in one field behaviour and landing in another is refuted',
         expect: "Scheduled message rejected by its own actor: 'gate' in the class C schedules 'timeout' for itself (line 8), but a timer fires into whichever behaviour is current AT THAT MOMENT, not the one that armed it — and phase 'later', reachable from there, throws on 'timeout'",
         src: tc('''class C {
                        static ReactorHandler<String, String> later = { ActorContext<String> ctx, String m ->
                            throw new IllegalStateException('unexpected ' + m)
                        } as ReactorHandler<String, String>
                        static Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                            if (m == 'go') { ctx.scheduleOnce('timeout', Duration.ofMillis(500)); ctx.become(later); return m }
                            m
                        } as ReactorHandler<String, String>)
                        static void run() { gate.send('go') }
                    }''')],

        // ── the @Protocol stack over a field actor: the role is played by the field's become-graph.
        [group: 'P298 actor fields', name: 'a field-held actor plays its protocol role and the round trip conforms', ok: true,
         refute: ['Protocol violation', 'Skipped protocol check'],
         src: tc('''class C {
                        static Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                            if (m == 'req') { return 'ack' }
                            'done'
                        } as ReactorHandler<String, String>)
                        @Protocol({
                            req: client >> gate
                            ack: gate >> client
                            loop { cmd: client >> gate }
                        })
                        static void run() {
                            gate.sendAndGet('req').get()
                            gate.send('cmd')
                        }
                    }''')],

        // ── and refutes through it: Phase 295's cross-wired reply, with the actor in a field.
        [group: 'P298 actor fields', name: 'a field-held actor with a cross-wired reply is refuted in its role',
         expect: "actor 'gate' replies 'nak' to 'req' in phase 'the handler' after it receives 'req' where the protocol's reply is 'ack'",
         src: tc('''class C {
                        static Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                            if (m == 'req') { return 'nak' }
                            'done'
                        } as ReactorHandler<String, String>)
                        @Protocol({
                            req: client >> gate
                            ack: gate >> client
                            loop { cmd: client >> gate }
                        })
                        static void run() {
                            gate.sendAndGet('req').get()
                            gate.send('cmd')
                        }
                    }''')],

        // ── an actor assigned in a constructor rather than an initialiser is not found: nothing is claimed,
        //    and nothing is wrongly claimed either.
        [group: 'P298 actor fields', name: 'an actor assigned in a constructor is not found, and nothing is claimed', ok: true,
         refute: ['Stashed messages', 'Scheduled message', 'Unbounded stash'],
         src: tc('''class C {
                        Actor<String> gate
                        C() {
                            gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                                ctx.stash()
                                m
                            } as ReactorHandler<String, String>)
                        }
                        void run() { gate.send('a') }
                    }''')],
    ]
}
