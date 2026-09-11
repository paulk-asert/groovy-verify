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
 * 'P292 actor stash' — stash conservation, the Actor surface's second property.
 *
 * <p>A stashed message comes back ONLY through {@code unstashAll()}. That is measured, not assumed
 * ({@code ActorStashSemanticsTest}): without it the message never reaches a handler again, and at {@code stop()}
 * a {@code sendAndGet} reply fails with IllegalStateException while a plain send is discarded. So an actor that
 * stashes, none of whose behaviours ever calls {@code unstashAll()}, loses every message it defers — a definite
 * loss. The claim is made only when the whole behaviour family is visible (the handler and every
 * {@code ctx.become(…)} target, inline or a local of the method) and is withheld when anything is opaque.
 */
class G342_p292_actor_stash {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 292 actor stash conservation: a stashed message comes back only through unstashAll() (measured by ActorStashSemanticsTest — never unstashed, it is rejected at stop()), so an actor that stashes while none of its behaviours — the handler and every ctx.become(…) target, inline or a local, declared then assigned as the Groovy docs do — ever calls unstashAll() loses every deferred message. The documented FSM idioms prove; the same idioms missing the replay refute; an opaque become target, a context handed to a helper, or an unstashAll() anywhere else in the method (an onError callback) withhold the claim.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [
        // ── the documented idiom (core-concurrent-actors.adoc, "Deferring messages with stash"): stash until
        //    ready, then become the connected phase and replay.
        [group: 'P292 actor stash', name: 'the documented stash-until-ready idiom replays its stash', ok: true,
         refute: 'Stashed messages are never replayed',
         src: tc('''class C {
                        static void phased() {
                            StatefulHandler<String, String> connected = { ActorContext<String> c, String s, String m -> 'got(' + m + ')' } as StatefulHandler<String, String>
                            Actor<String> actor = Actor.stateful('init', { ActorContext<String> ctx, String s, String m ->
                                if (m == 'ready') {
                                    ctx.become(connected)
                                    ctx.unstashAll()
                                    return s
                                }
                                ctx.stash()
                                s
                            } as StatefulHandler<String, String>)
                            actor.send('A')
                            actor.send('ready')
                        }
                    }''')],

        // ── the mistake: the same actor, the replay forgotten — everything stashed before 'ready' is lost.
        [group: 'P292 actor stash', name: 'stash-until-ready without unstashAll loses every deferred message',
         expect: "Stashed messages are never replayed: actor 'actor' in phased() stashes",
         src: tc('''class C {
                        static void phased() {
                            StatefulHandler<String, String> connected = { ActorContext<String> c, String s, String m -> 'got(' + m + ')' } as StatefulHandler<String, String>
                            Actor<String> actor = Actor.stateful('init', { ActorContext<String> ctx, String s, String m ->
                                if (m == 'ready') {
                                    ctx.become(connected)
                                    return s
                                }
                                ctx.stash()
                                s
                            } as StatefulHandler<String, String>)
                            actor.send('A')
                            actor.send('ready')
                        }
                    }''')],

        // ── the docs' three-phase connection actor: phases declared first, assigned afterwards, the handler
        //    passed as a local, and the stash two become-steps from the start.
        [group: 'P292 actor stash', name: 'the documented three-phase actor (declared, then assigned) replays its stash', ok: true,
         refute: 'Stashed messages are never replayed',
         src: tc('''class C {
                        static void auth() {
                            StatefulHandler<Integer, String> disconnected, authenticating, connected
                            disconnected = { ActorContext<String> ctx, Integer s, String m ->
                                if (m == 'connect') { ctx.become(authenticating); return s }
                                s
                            } as StatefulHandler<Integer, String>
                            authenticating = { ActorContext<String> ctx, Integer s, String m ->
                                if (m == 'auth-ok') {
                                    ctx.become(connected)
                                    ctx.unstashAll()
                                    return s
                                }
                                ctx.stash()
                                s
                            } as StatefulHandler<Integer, String>
                            connected = { ActorContext<String> ctx, Integer s, String m -> s + 1 } as StatefulHandler<Integer, String>
                            Actor<String> actor = Actor.stateful(0, disconnected)
                            actor.send('connect')
                        }
                    }''')],

        // ── …and its mistake: the family is followed from the handler local through BOTH become steps, so the
        //    stash in the middle phase is found, and so is the absence of any replay.
        [group: 'P292 actor stash', name: 'the three-phase actor without the replay is refuted through two become steps',
         expect: "Stashed messages are never replayed: actor 'actor' in auth() stashes",
         src: tc('''class C {
                        static void auth() {
                            StatefulHandler<Integer, String> disconnected, authenticating, connected
                            disconnected = { ActorContext<String> ctx, Integer s, String m ->
                                if (m == 'connect') { ctx.become(authenticating); return s }
                                s
                            } as StatefulHandler<Integer, String>
                            authenticating = { ActorContext<String> ctx, Integer s, String m ->
                                if (m == 'auth-ok') { ctx.become(connected); return s }
                                ctx.stash()
                                s
                            } as StatefulHandler<Integer, String>
                            connected = { ActorContext<String> ctx, Integer s, String m -> s + 1 } as StatefulHandler<Integer, String>
                            Actor<String> actor = Actor.stateful(0, disconnected)
                            actor.send('connect')
                        }
                    }''')],

        // ── the reactor form of the mistake: a context-aware reactor that only ever defers.
        [group: 'P292 actor stash', name: 'a reactor that stashes with no replay anywhere is refuted',
         expect: "Stashed messages are never replayed: actor 'deferrer' in defers() stashes",
         src: tc('''class C {
                        static void defers() {
                            Actor<String> deferrer = Actor.reactor({ ActorContext<String> ctx, String m ->
                                ctx.stash()
                                return m
                            } as ReactorHandler<String, String>)
                            deferrer.send('x')
                        }
                    }''')],

        // ── what is NOT claimed. A become target from elsewhere may replay; nothing visible says it does not.
        [group: 'P292 actor stash', name: 'an opaque become target withholds the claim', ok: true,
         refute: 'Stashed messages are never replayed',
         src: tc('''class C {
                        static StatefulHandler<Integer, String> elsewhere() {
                            { ActorContext<String> c, Integer s, String m -> s } as StatefulHandler<Integer, String>
                        }
                        static void opaque() {
                            Actor<String> actor = Actor.stateful(0, { ActorContext<String> ctx, Integer s, String m ->
                                if (m == 'go') { ctx.become(elsewhere()); return s }
                                ctx.stash()
                                s
                            } as StatefulHandler<Integer, String>)
                            actor.send('x')
                        }
                    }''')],
        // A context handed to a helper may be replayed there.
        [group: 'P292 actor stash', name: 'a context handed to a helper withholds the claim', ok: true,
         refute: 'Stashed messages are never replayed',
         src: tc('''class C {
                        static void replay(ActorContext<String> c) { if (c != null) c.unstashAll() }
                        static void helped() {
                            Actor<String> actor = Actor.reactor({ ActorContext<String> ctx, String m ->
                                if (m == 'go') { replay(ctx); return m }
                                ctx.stash()
                                return m
                            } as ReactorHandler<String, String>)
                            actor.send('x')
                        }
                    }''')],
        // An unstashAll() anywhere else in the method — here a context-aware onError retry — withholds it too.
        [group: 'P292 actor stash', name: 'an unstashAll in an onError callback withholds the claim', ok: true,
         refute: 'Stashed messages are never replayed',
         src: tc('''class C {
                        static void retried() {
                            Actor<String> actor = Actor.reactor({ ActorContext<String> ctx, String m ->
                                ctx.stash()
                                return m
                            } as ReactorHandler<String, String>)
                            actor.onError { ActorContext<String> c, Throwable t, String m -> c.unstashAll() }
                            actor.send('x')
                        }
                    }''')],

        // ── Slice 2 — the stash BOUND. A "stash until 'open'" handler stashes every message this method sends
        //    before 'open', so a literal burst is a count of the stash; each policy's outcome is measured.
        [group: 'P292 actor stash', name: 'a burst past a FAIL stash bound fails the overflowing message',
         expect: ["Stash overflow in 'burst': actor 'gate' stashes every message until 'open'", 'the 3rd stashed before it',
                  'StashOverflow.FAIL: its stash() throws IllegalStateException'],
         src: tc('''class C {
                        static void burst() {
                            Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                                if (m == 'open') {
                                    ctx.become({ ActorContext<String> c, String n -> n } as ReactorHandler<String, String>)
                                    ctx.unstashAll()
                                    return m
                                }
                                ctx.stash()
                                return m
                            } as ReactorHandler<String, String>, ActorOptions.DEFAULTS.withStashBound(2, ActorOptions.StashOverflow.FAIL))
                            gate.send('a')
                            gate.send('b')
                            gate.send('c')
                            gate.send('open')
                        }
                    }''')],
        [group: 'P292 actor stash', name: 'a burst past a DROP_OLDEST stash bound evicts the first stashed message',
         expect: ['StashOverflow.DROP_OLDEST: stashing it evicts the OLDEST stashed message (line'],
         src: tc('''class C {
                        static void burst() {
                            Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                                if (m == 'open') {
                                    ctx.become({ ActorContext<String> c, String n -> n } as ReactorHandler<String, String>)
                                    ctx.unstashAll()
                                    return m
                                }
                                ctx.stash()
                                return m
                            } as ReactorHandler<String, String>, ActorOptions.DEFAULTS.withStashBound(2, ActorOptions.StashOverflow.DROP_OLDEST))
                            gate.send('a')
                            gate.send('b')
                            gate.send('c')
                            gate.send('open')
                        }
                    }''')],
        // The stateful, if/else spelling of the same handler, under REJECT.
        [group: 'P292 actor stash', name: 'a burst past a REJECT stash bound refuses the overflowing message (stateful, if/else)',
         expect: ['StashOverflow.REJECT: it is rejected rather than stashed'],
         src: tc('''class C {
                        static void burst() {
                            StatefulHandler<Integer, String> open = { ActorContext<String> c, Integer s, String n -> s + 1 } as StatefulHandler<Integer, String>
                            Actor<String> gate = Actor.stateful(0, { ActorContext<String> ctx, Integer s, String m ->
                                if (m == 'open') {
                                    ctx.become(open)
                                    ctx.unstashAll()
                                } else {
                                    ctx.stash()
                                }
                                s
                            } as StatefulHandler<Integer, String>, ActorOptions.DEFAULTS.withStashBound(1, ActorOptions.StashOverflow.REJECT))
                            gate.send('a')
                            gate.send('b')
                            gate.send('open')
                        }
                    }''')],
        // ── what is left alone: a burst that fits, the trigger sent first, and an unbounded stash.
        [group: 'P292 actor stash', name: 'a burst within the stash bound is left alone', ok: true,
         refute: 'Stash overflow',
         src: tc('''class C {
                        static void fits() {
                            Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                                if (m == 'open') {
                                    ctx.become({ ActorContext<String> c, String n -> n } as ReactorHandler<String, String>)
                                    ctx.unstashAll()
                                    return m
                                }
                                ctx.stash()
                                return m
                            } as ReactorHandler<String, String>, ActorOptions.DEFAULTS.withStashBound(2, ActorOptions.StashOverflow.FAIL))
                            gate.send('a')
                            gate.send('b')
                            gate.send('open')
                            gate.send('c')
                        }
                    }''')],
        [group: 'P292 actor stash', name: 'an unbounded stash never overflows (the heap is the javadoc\'s warning, not this check\'s)', ok: true,
         refute: 'Stash overflow',
         src: tc('''class C {
                        static void unbounded() {
                            Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                                if (m == 'open') {
                                    ctx.become({ ActorContext<String> c, String n -> n } as ReactorHandler<String, String>)
                                    ctx.unstashAll()
                                    return m
                                }
                                ctx.stash()
                                return m
                            } as ReactorHandler<String, String>)
                            gate.send('a')
                            gate.send('b')
                            gate.send('c')
                            gate.send('open')
                        }
                    }''')],
        // ── what is not claimed: a message the checker cannot read could BE the trigger, and an actor handed on
        //    could be sent the trigger by someone else first.
        [group: 'P292 actor stash', name: 'a non-literal message before the trigger withholds the count', ok: true,
         refute: 'Stash overflow',
         src: tc('''class C {
                        static void unknown(String first) {
                            Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                                if (m == 'open') {
                                    ctx.become({ ActorContext<String> c, String n -> n } as ReactorHandler<String, String>)
                                    ctx.unstashAll()
                                    return m
                                }
                                ctx.stash()
                                return m
                            } as ReactorHandler<String, String>, ActorOptions.DEFAULTS.withStashBound(2, ActorOptions.StashOverflow.FAIL))
                            gate.send(first)
                            gate.send('b')
                            gate.send('c')
                            gate.send('open')
                        }
                    }''')],
        [group: 'P292 actor stash', name: 'an actor handed to another method withholds the count', ok: true,
         refute: 'Stash overflow',
         src: tc('''class C {
                        static void share(Actor<String> other) { }
                        static void shared() {
                            Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                                if (m == 'open') {
                                    ctx.become({ ActorContext<String> c, String n -> n } as ReactorHandler<String, String>)
                                    ctx.unstashAll()
                                    return m
                                }
                                ctx.stash()
                                return m
                            } as ReactorHandler<String, String>, ActorOptions.DEFAULTS.withStashBound(2, ActorOptions.StashOverflow.FAIL))
                            share(gate)
                            gate.send('a')
                            gate.send('b')
                            gate.send('c')
                            gate.send('open')
                        }
                    }''')],
    ]
}
