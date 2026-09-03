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
 * 'P289 actor mailbox' — the first send in `groovy.concurrent` besides a rendezvous that really BLOCKS.
 *
 * <p>Every other certificate in the ladder rests on "a buffered send never blocks", and that is measured
 * rather than assumed: {@code ActorMailboxSemanticsTest} pushes eight sends into a capacity-2 AsyncChannel
 * with nothing draining and every one returns. {@code withBoundedMailbox(k, Overflow.BLOCK)} is different —
 * the same test shows a send into a full BLOCK mailbox parking the caller until space appears — so a burst
 * into a bounded actor is a chain of blocking events, and filling a mailbox whose handler is waiting on the
 * filler is a circular wait the compiler can name.
 *
 * <p>The lossy policies are modelled as what they are. Under DROP_NEWEST / FAIL nothing blocks, but a
 * sendAndGet past the bound has its reply completed with IllegalStateException (measured; documented on
 * StashOverflow but NOT on Overflow), so a claim about that reply can hold only by luck.
 */
class G339_p289_actor_mailbox {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 289 actor mailbox (the Actor surface\'s first case coverage): `ActorOptions.withBoundedMailbox(k, Overflow.BLOCK)` is the only send in groovy.concurrent besides a rendezvous channel that BLOCKS the sender — established by measurement (ActorMailboxSemanticsTest drives 8 sends into a capacity-2 AsyncChannel and all return, then shows a send into a full BLOCK mailbox parking the caller). So one message in the handler plus k in the box means the (k+2)-th send waits for the handler to take another; if the handler is itself waiting for a channel this method only feeds AFTER that send, the two wait for each other and the burst is refused with both halves of the cycle named. A burst that fits the bound, an unbounded mailbox, and a handler that never blocks are all left alone. Under the non-blocking policies nothing deadlocks, but a sendAndGet past the bound has its reply bound to IllegalStateException rather than a value, so a claim on that reply is refused in the spirit of Phase 285\'s correlated shared reply. One boundary is stated loudly rather than papered over: a channel an actor HANDLER touches falls out of the one-shot FIFO model, because the handler runs once per message rather than once — unlike an async arm, which is a single process run. The mailbox verdict is independent of that skip and is what these cases pin.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [
        // ── the shape that certifies: the burst fits inside the bound, so no send ever waits.
        [group: 'P289 actor mailbox', name: 'a burst within the bound never blocks the sender',
         expect: 'Skipped channel verification',
         refute: ['Actor mailbox deadlock', 'Reply from a full bounded mailbox'],
         src: tc("""class C {
                        static int fits() {
                            AsyncChannel<Integer> gate = AsyncChannel.create(4)
                            Actor<Integer> worker = Actor.reactor({ Integer m -> gate.first() },
                                ActorOptions.DEFAULTS.withBoundedMailbox(4, ActorOptions.Overflow.BLOCK))
                            worker.send(1)
                            worker.send(2)
                            gate.send(0)
                            return 0
                        }
                    }""")],

        // ── the mistake: one in the handler, k in the box, and the (k+2)-th send waits for a handler that
        //    is itself waiting for this very process. The classic actor footgun as a wait-for cycle.
        [group: 'P289 actor mailbox', name: 'filling a BLOCK mailbox before feeding its handler is a circular wait',
         expect: 'Actor mailbox deadlock',
         src: tc("""class C {
                        static int knot() {
                            AsyncChannel<Integer> gate = AsyncChannel.create(4)
                            Actor<Integer> worker = Actor.reactor({ Integer m -> gate.first() },
                                ActorOptions.DEFAULTS.withBoundedMailbox(1, ActorOptions.Overflow.BLOCK))
                            worker.send(1)
                            worker.send(2)
                            worker.send(3)
                            gate.send(0)
                            return 0
                        }
                    }""")],

        // ── the same burst, unbounded: a send is queued and never blocks, so there is no cycle to find.
        //    This is the control that shows the BOUND is what the refutation turns on, not the ordering.
        [group: 'P289 actor mailbox', name: 'the same burst on an unbounded mailbox is not a deadlock',
         expect: 'Skipped channel verification',
         refute: 'Actor mailbox deadlock',
         src: tc("""class C {
                        static int unbounded() {
                            AsyncChannel<Integer> gate = AsyncChannel.create(4)
                            Actor<Integer> worker = Actor.reactor({ Integer m -> gate.first() })
                            worker.send(1)
                            worker.send(2)
                            worker.send(3)
                            gate.send(0)
                            return 0
                        }
                    }""")],

        // ── feeding the gate FIRST unties it: the handler drains, so no send ever has to wait.
        [group: 'P289 actor mailbox', name: 'feeding the handler before the burst unties the knot',
         expect: 'Skipped channel verification',
         refute: 'Actor mailbox deadlock',
         src: tc("""class C {
                        static int fedFirst() {
                            AsyncChannel<Integer> gate = AsyncChannel.create(4)
                            Actor<Integer> worker = Actor.reactor({ Integer m -> gate.first() },
                                ActorOptions.DEFAULTS.withBoundedMailbox(1, ActorOptions.Overflow.BLOCK))
                            gate.send(0)
                            worker.send(1)
                            worker.send(2)
                            worker.send(3)
                            return 0
                        }
                    }""")],

        // ── a handler that never blocks always drains, so the bound is not a hazard however big the burst.
        [group: 'P289 actor mailbox', name: 'a handler that never blocks drains its own mailbox', ok: true,
         refute: 'Actor mailbox deadlock',
         src: tc("""class C {
                        static int drains() {
                            Actor<Integer> worker = Actor.reactor({ Integer m -> m + 1 },
                                ActorOptions.DEFAULTS.withBoundedMailbox(1, ActorOptions.Overflow.BLOCK))
                            worker.send(1)
                            worker.send(2)
                            worker.send(3)
                            return 0
                        }
                    }""")],

        // ── the lossy half: nothing blocks, but the reply to a dropped sendAndGet is an IllegalStateException,
        //    so believing it carries an answer is the shared-reply mistake of Phase 285 in another dress.
        [group: 'P289 actor mailbox', name: 'a claim on a reply past a DROP_NEWEST bound is refused',
         expect: 'Reply from a full bounded mailbox',
         src: tc("""class C {
                        static int lossy() {
                            Actor<Integer> worker = Actor.reactor({ Integer m -> m + 1 },
                                ActorOptions.DEFAULTS.withBoundedMailbox(1, ActorOptions.Overflow.DROP_NEWEST))
                            worker.send(1)
                            worker.send(2)
                            def reply = worker.sendAndGet(3)
                            return 0
                        }
                    }""")],

        // ── FAIL says the same thing in its own words: the send is rejected at the sender.
        [group: 'P289 actor mailbox', name: 'the FAIL policy refuses the same claim in its own words',
         expect: 'Overflow.FAIL',
         src: tc("""class C {
                        static int failing() {
                            Actor<Integer> worker = Actor.reactor({ Integer m -> m + 1 },
                                ActorOptions.DEFAULTS.withBoundedMailbox(1, ActorOptions.Overflow.FAIL))
                            worker.send(1)
                            worker.send(2)
                            def reply = worker.sendAndGet(3)
                            return 0
                        }
                    }""")],

        // ── a sendAndGet WITHIN the bound is an ordinary round-trip: the refusal is about the overflow,
        //    not about sendAndGet, and this pins that the check does not cry wolf over every reply.
        [group: 'P289 actor mailbox', name: 'a sendAndGet within the bound is an ordinary round trip', ok: true,
         refute: 'Reply from a full bounded mailbox',
         src: tc("""class C {
                        static int withinBound() {
                            Actor<Integer> worker = Actor.reactor({ Integer m -> m + 1 },
                                ActorOptions.DEFAULTS.withBoundedMailbox(4, ActorOptions.Overflow.DROP_NEWEST))
                            def reply = worker.sendAndGet(1)
                            return 0
                        }
                    }""")],
    ]
}
