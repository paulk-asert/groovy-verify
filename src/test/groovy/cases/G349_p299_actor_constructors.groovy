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
 * 'P299 actor constructors' — the actor BUILT in a constructor, a static block or an instance initialiser, which
 * is what Phase 298's initialiser-only reading could not reach. The payoff is not the extra syntax but the
 * CYCLE: a field initialiser cannot name a field declared after it, so mutual {@code become} has to be written
 * declare-then-assign — which means the Groovy docs' own three-phase connection actor, with its
 * {@code connected → disconnected} back edge, could not be expressed as a service class at all until now.
 */
class G349_p299_actor_constructors {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 299 the actor built in a constructor: fields ASSIGNED in the class\'s constructor, static block or instance initialiser are read alongside Phase 298\'s field initialisers (an unqualified name or `this.x`), which is what makes a CYCLIC phase graph reachable — a field initialiser cannot name a field declared after it, so mutual become has to be written declare-then-assign, and the Groovy docs\' three-phase connection actor with its connected → disconnected back edge could not be expressed as a service class before. The whole gallery then reads it: the stash check, the timers and the @Protocol stack, with the mistyped trigger refuting exactly as it does for a method-local actor. Withheld, rather than guessed at: any field given a MODELLED value twice (an actor factory or a behaviour closure, from an initialiser and a constructor or twice in one) — a null placeholder followed by a real assignment is one definition and is kept. (Phase 301 generalised the single-constructor reading to every constructor and method, so WHERE the actor is built is decided by counting the definitions; that group owns the multi-constructor case.)'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    /** The Groovy docs' three-phase connection actor, as a service class. `authArm` is the trigger branch. */
    static String service(String authArm) { """class C {
                        StatefulHandler<Integer, String> disconnected, authenticating, connected
                        Actor<String> gate
                        C() {
                            disconnected = { ActorContext<String> ctx, Integer s, String m ->
                                if (m == 'connect') { ctx.become(authenticating); return s }
                                s
                            } as StatefulHandler<Integer, String>
                            authenticating = { ActorContext<String> ctx, Integer s, String m ->
                                ${authArm}
                                ctx.stash()
                                s
                            } as StatefulHandler<Integer, String>
                            connected = { ActorContext<String> ctx, Integer s, String m ->
                                if (m == 'bye') { ctx.become(disconnected); return s }
                                s + 1
                            } as StatefulHandler<Integer, String>
                            gate = Actor.stateful(0, disconnected)
                        }
                        @Protocol({
                            connect: client >> gate
                            auth_ok: client >> gate
                            loop { cmd: client >> gate }
                        })
                        void run() {
                            gate.send('connect')
                            gate.send('auth_ok')
                            gate.send('cmd')
                        }
                    }""" }

    static final List<Map> CASES = [
        // ── the shape this phase exists for: a CYCLIC phase graph, impossible as field initialisers.
        [group: 'P299 actor constructors', name: 'the docs three-phase actor as a service class, with a back edge, conforms', ok: true,
         refute: ['Protocol violation', 'Skipped protocol check', 'Stashed messages'],
         src: tc(service("if (m == 'auth_ok') { ctx.become(connected); ctx.unstashAll(); return s }"))],

        // ── and it is genuinely CHECKED, not merely unreported: Phase 293's mistyped trigger refutes through it.
        [group: 'P299 actor constructors', name: 'the same service class with a mistyped trigger is refuted',
         expect: "actor 'gate' can reach the end of the conversation in phase 'authenticating' after it receives 'connect', then 'auth_ok' with 'auth_ok' still stashed",
         src: tc(service("if (m == 'auth-ok') { ctx.become(connected); ctx.unstashAll(); return s }"))],

        // ── the plain constructor form, and the `this.`-qualified spelling of it.
        [group: 'P299 actor constructors', name: 'an actor built in a constructor is read, this-qualified or not',
         expect: "Stashed messages are never replayed: actor 'gate' in the class C stashes (line 7)",
         src: tc('''class C {
                        Actor<String> gate
                        C() {
                            this.gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                                ctx.stash()
                                m
                            } as ReactorHandler<String, String>)
                        }
                        void run() { gate.send('a') }
                    }''')],

        // ── a static block is the static-field spelling of the same thing.
        [group: 'P299 actor constructors', name: 'an actor built in a static block is read',
         expect: "Stashed messages are never replayed: actor 'gate' in the class C stashes (line 7)",
         src: tc('''class C {
                        static Actor<String> gate
                        static {
                            gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                                ctx.stash()
                                m
                            } as ReactorHandler<String, String>)
                        }
                        static void run() { gate.send('a') }
                    }''')],

        // ── a null placeholder is not a definition: one real assignment remains, and is read.
        [group: 'P299 actor constructors', name: 'a null placeholder then a real assignment is one definition',
         expect: "Stashed messages are never replayed: actor 'gate' in the class C",
         src: tc('''class C {
                        Actor<String> gate = null
                        C() {
                            gate = Actor.reactor({ ActorContext<String> ctx, String m -> ctx.stash(); m } as ReactorHandler<String, String>)
                        }
                        void run() { gate.send('a') }
                    }''')],

        // ── withheld: two MODELLED definitions of the actor compete, so neither is read.
        [group: 'P299 actor constructors', name: 'an actor given two competing definitions is withheld', ok: true,
         refute: ['Stashed messages', 'Scheduled message', 'Unbounded stash'],
         src: tc('''class C {
                        Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m -> m } as ReactorHandler<String, String>)
                        C() {
                            gate = Actor.reactor({ ActorContext<String> ctx, String m -> ctx.stash(); m } as ReactorHandler<String, String>)
                        }
                        void run() { gate.send('a') }
                    }''')],

        // ── withheld likewise for a BEHAVIOUR, so the overwritten one is never scanned.
        [group: 'P299 actor constructors', name: 'a behaviour given two competing definitions is withheld', ok: true,
         refute: ['Stashed messages', 'Scheduled message', 'Unbounded stash'],
         src: tc('''class C {
                        ReactorHandler<String, String> h = { ActorContext<String> ctx, String m -> ctx.stash(); m } as ReactorHandler<String, String>
                        Actor<String> gate
                        C() {
                            h = { ActorContext<String> ctx, String m -> m } as ReactorHandler<String, String>
                            gate = Actor.reactor(h)
                        }
                        void run() { gate.send('a') }
                    }''')],

    ]
}
