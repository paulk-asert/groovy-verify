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
 * 'P300 field actor sends' — the last piece of the Actor surface that could not see a service class: the
 * SEND-dependent checks, the bounded mailbox (289) and the stash bound (292 slice 2). They read this method's
 * sends, and a field-held actor OUTLIVES the call — so the burst in one method is the whole count only when
 * nothing else can add to it or drain it. That condition is checked rather than assumed, and said out loud when
 * it fails.
 */
class G350_p300_field_actor_sends {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 300 the send-dependent checks over a field-held actor: the bounded mailbox (289) and the stash bound (292 slice 2) count THIS method\'s sends, so a field-held actor — which outlives the call — is only checkable when nothing else can add to the burst or drain it. Both are claimed exactly when the field is genuinely private (a Groovy field written without a modifier is a PROPERTY, whose generated accessor lets code outside the class send to it) and exactly one method of the class sends to it; repeat calls of that one method are then the only other source and can only repeat the burst, which adds to a bound and never rescues one, so a refutation stands. Otherwise a loud skip names the reason — the property, or the sibling methods that can interleave. The behaviour-graph checks stay where Phase 298 put them, raised once for the class.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    /** A field-held actor that stashes until 'open', with a stash bound of 2; `mods` decides its visibility. */
    static String stashBound(String mods, String extra = '') { """class C {
                        ${mods} Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                            if (m == 'open') {
                                ctx.become({ ActorContext<String> c, String n -> n } as ReactorHandler<String, String>)
                                ctx.unstashAll()
                                return m
                            }
                            ctx.stash()
                            return m
                        } as ReactorHandler<String, String>, ActorOptions.DEFAULTS.withStashBound(2, ActorOptions.StashOverflow.FAIL))
                        static void burst() {
                            gate.send('a')
                            gate.send('b')
                            gate.send('c')
                            gate.send('open')
                        }${extra}
                    }""" }

    static final List<Map> CASES = [
        // ── the reach: the identical burst Phase 292 refutes for a local, now with the actor on the class.
        [group: 'P300 field actor sends', name: 'a burst past a stash bound is refuted with the actor held in a field',
         expect: ["Stash overflow in 'burst': actor 'gate' stashes every message until 'open'", 'the 3rd stashed before it',
                  'StashOverflow.FAIL: its stash() throws IllegalStateException'],
         src: tc(stashBound('private static'))],

        // ── the bounded MAILBOX half, likewise: the handler waits for a channel this method feeds too late.
        [group: 'P300 field actor sends', name: 'a BLOCK mailbox knot is refuted with the actor held in a field',
         expect: 'Actor mailbox deadlock',
         src: tc('''class C {
                        private static AsyncChannel<Integer> gate = AsyncChannel.create(4)
                        private static Actor<Integer> worker = Actor.reactor({ Integer m -> gate.first() },
                            ActorOptions.DEFAULTS.withBoundedMailbox(1, ActorOptions.Overflow.BLOCK))
                        static int knot() {
                            worker.send(1)
                            worker.send(2)
                            worker.send(3)
                            gate.send(0)
                            return 0
                        }
                    }''')],

        // ── a field written without a modifier is a PROPERTY: its accessor lets anyone send, so no count is whole.
        [group: 'P300 field actor sends', name: 'a property-held actor is skipped loudly, since anyone can send to it',
         expect: "Skipped actor send certificate for 'gate' in burst ('gate' is a property, so its generated accessor lets code outside C send to it too)",
         refute: 'Stash overflow',
         src: tc(stashBound('static'))],

        // ── two methods of the class send: a sibling can interleave the trigger, so the burst is not the count.
        [group: 'P300 field actor sends', name: 'two sending methods are skipped loudly, naming both',
         expect: "2 methods of C send to 'gate' (burst(), other()), so this method's sends are not the whole count",
         refute: 'Stash overflow',
         src: tc(stashBound('private static', "\n                        static void other() { gate.send('open') }"))],

        // ── a burst within the bound is left alone, field or not.
        [group: 'P300 field actor sends', name: 'a burst within the bound on a field-held actor is left alone', ok: true,
         refute: ['Stash overflow', 'Skipped actor send certificate'],
         src: tc('''class C {
                        private static Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                            if (m == 'open') {
                                ctx.become({ ActorContext<String> c, String n -> n } as ReactorHandler<String, String>)
                                ctx.unstashAll()
                                return m
                            }
                            ctx.stash()
                            return m
                        } as ReactorHandler<String, String>, ActorOptions.DEFAULTS.withStashBound(2, ActorOptions.StashOverflow.FAIL))
                        static void burst() {
                            gate.send('a')
                            gate.send('b')
                            gate.send('open')
                        }
                    }''')],

        // ── an unbounded field-held actor asks for no bound, so a second sender is not worth a word.
        [group: 'P300 field actor sends', name: 'an unbounded field-held actor with two senders says nothing', ok: true,
         refute: ['Stash overflow', 'Skipped actor send certificate', 'Actor mailbox deadlock'],
         src: tc('''class C {
                        private static Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m -> m } as ReactorHandler<String, String>)
                        static void burst() { gate.send('a'); gate.send('b') }
                        static void other() { gate.send('c') }
                    }''')],
    ]
}
