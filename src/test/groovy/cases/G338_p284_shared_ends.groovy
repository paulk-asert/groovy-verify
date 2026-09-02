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
 * 'P284 shared ends' — JCSP's `any2one` / `one2any`, as a DECLARED relaxation of channel-end linearity.
 * By default a channel is point-to-point and a second sender or receiver is refused (Phase 241), because
 * the FIFO per-element model rests on it. c11, c12's canteen and c24 need shared ends, so they are opt-in:
 * `@SharedSend` (many writers, one reader) and `@SharedReceive` (one writer, many competing readers).
 *
 * <p>Declared, never inferred — that is the whole design point. Inferring sharing from "two processes send
 * here" would convert the rule's main value, catching sharing nobody intended, into a silent weakening.
 * What the declaration costs is the positional model, said out loud at the channel. What it keeps is the
 * element CONTRACT (every sender must satisfy it, so the reader may assume it whoever sent) and
 * DEADLOCK-FREEDOM, with a receive waiting on the disjunction of the sends rather than on one of them.
 */
class G338_p284_shared_ends {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 284 shared channel ends (slice 45): JCSP\'s any2one / one2any as a DECLARED relaxation of Phase 241 linearity — `@SharedSend` (many writers, one reader) and `@SharedReceive` (one writer, many competing readers) on the channel declaration. Declared and never inferred: inferring sharing from two senders would turn the linearity rule\'s main value, catching sharing nobody intended, into a silent weakening, so the undeclared shapes still refuse exactly as before. The declaration costs the POSITIONAL model, reported at the channel in terms of what is given up (nothing is claimed about which element a receive returns, nor the order they arrive in). It keeps the element CONTRACT — every sender must satisfy it, so the reader may assume it whoever sent — and DEADLOCK-FREEDOM, with a receive on a shared send end waiting on the DISJUNCTION of the sends (the OR node an ALT uses) rather than on the j-th, which would report a deadlock whenever the paired sender happened to be the blocked one.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [
        // ---------- c12's canteen, the other half of the chapter (Phase 286) ----------
        // The servery holds a chicken count, takes supply always and a request only while it HAS one, and
        // chooses with a held fair() — JCSP's `fairSelect(precondition)`. Guarded ALT and fair selection
        // together, which no earlier case combines: the guard proves the assert in its own arm while the
        // rotation state lives in the held instance.
        [group: 'P284 shared ends', name: 'c12\'s servery: a guarded fair select never serves what it has not got',
         *: (WHEN_GUARD ? [expect: 'Skipped channel verification'] : [expect: 'Cannot find matching method']),
         refute: ['Assertion may not hold', 'Cannot prove loop invariant', 'Skipped loop verification'],
         src: tc("""class C {
                        static void servery() {
                            AsyncChannel<Integer> supply = AsyncChannel.create(4)
                            AsyncChannel<Integer> service = AsyncChannel.create(4)
                            int chickens = 0
                            ChannelSelect alt = ChannelSelect.offers(ChannelSelect.receive(supply),
                                                                     ChannelSelect.receive(service).when { chickens > 0 }).fair()
                            @Invariant({ chickens >= 0 })
                            while (true) {
                                ChannelSelect.Result r = await alt.select()
                                if (r.index == 0) {
                                    chickens = chickens + 1
                                }
                                if (r.index == 1) {
                                    assert chickens > 0
                                    chickens = chickens - 1
                                }
                            }
                        }
                    }""")],
        // Serve whenever asked and the servery hands out a chicken it has not got — refuted at the empty
        // counter. The precondition is the whole difference, fair selection or not.
        [group: 'P284 shared ends', name: 'a servery that serves whenever asked is refused',
         *: (WHEN_GUARD ? [expect: 'Assertion may not hold'] : [expect: 'Cannot find matching method']),
         src: tc("""class C {
                        static void servery() {
                            AsyncChannel<Integer> supply = AsyncChannel.create(4)
                            AsyncChannel<Integer> service = AsyncChannel.create(4)
                            int chickens = 0
                            ChannelSelect alt = ChannelSelect.offers(ChannelSelect.receive(supply),
                                                                     ChannelSelect.receive(service).when { chickens >= 0 }).fair()
                            @Invariant({ chickens >= 0 })
                            while (true) {
                                ChannelSelect.Result r = await alt.select()
                                if (r.index == 0) {
                                    chickens = chickens + 1
                                }
                                if (r.index == 1) {
                                    assert chickens > 0
                                    chickens = chickens - 1
                                }
                            }
                        }
                    }""")],
        // any2one: many writers, one reader — c12's canteen `service`, c11's particles. Permitted because
        // declared, and the skip says what the declaration costs rather than reporting a surprise.
        [group: 'P284 shared ends', name: 'a declared any2one send end is permitted, at the cost of the positional model',
         expect: 'is declared @SharedSend', refute: 'Channel linearity',
         src: tc("""class C {
                        static int anyToOne() {
                            @verification.SharedSend AsyncChannel<Integer> service = AsyncChannel.create(4)
                            async { service.send(1) }
                            async { service.send(2) }
                            return service.first()
                        }
                    }""")],
        // THE control: the same shape without the declaration is still a linearity violation. Accidental
        // sharing is what the rule is for, and relaxing it on declaration must not relax it on inference.
        [group: 'P284 shared ends', name: 'undeclared sharing is still refused', expect: 'Channel linearity',
         src: tc("""class C {
                        static int undeclared() {
                            AsyncChannel<Integer> service = AsyncChannel.create(4)
                            async { service.send(1) }
                            async { service.send(2) }
                            return service.first()
                        }
                    }""")],
        // one2any: one writer, many competing readers — c12's canteen `deliver`. Note this is NOT the
        // broadcast fan-out of Phase 241 (every subscriber sees every element); here each element goes to
        // exactly one of them.
        [group: 'P284 shared ends', name: 'a declared one2any receive end is permitted', expect: 'is declared @SharedReceive',
         refute: 'Channel linearity',
         src: tc("""class C {
                        static int oneToAny() {
                            @verification.SharedReceive AsyncChannel<Integer> deliver = AsyncChannel.create(4)
                            deliver.send(1)
                            deliver.send(2)
                            async { int a = deliver.first() }
                            async { int b = deliver.first() }
                            return 0
                        }
                    }""")],
        [group: 'P284 shared ends', name: 'undeclared competing receivers are still refused', expect: 'Channel linearity',
         src: tc("""class C {
                        static int undeclaredRecv() {
                            AsyncChannel<Integer> deliver = AsyncChannel.create(4)
                            deliver.send(1)
                            deliver.send(2)
                            async { int a = deliver.first() }
                            async { int b = deliver.first() }
                            return 0
                        }
                    }""")],
        // Deadlock-freedom survives the relaxation: a receive with no send at all is still named.
        [group: 'P284 shared ends', name: 'a shared end does not excuse a receive nothing sends to', expect: 'can never be satisfied',
         src: tc("""class C {
                        static int noSend() {
                            @verification.SharedSend AsyncChannel<Integer> service = AsyncChannel.create(4)
                            return service.first()
                        }
                    }""")],
        // …and it does not INVENT one either: with one sender blocked and another free, the receive waits
        // on the disjunction, so no deadlock is reported. Pairing it to the j-th send would have.
        [group: 'P284 shared ends', name: 'one blocked sender does not deadlock a shared end', expect: 'is declared @SharedSend',
         refute: 'Process-network deadlock',
         src: tc("""class C {
                        static int orNode() {
                            @verification.SharedSend AsyncChannel<Integer> service = AsyncChannel.create(4)
                            AsyncChannel<Integer> other = AsyncChannel.create(1)
                            other.send(9)
                            async { int w = other.first(); service.send(1) }
                            async { service.send(2) }
                            return service.first()
                        }
                    }""")],

        // ---------- the obligation a shared reply end unlocks (Phase 285) ----------
        // c12's canteen: every philosopher writes one `service` and reads one `deliver`. The book leaves
        // the consequence implicit; it is the bug the shape invites. A client that believes the reply it
        // took answers the request it sent is relying on luck — any client may take any reply.
        [group: 'P284 shared ends', name: 'a client that assumes the shared reply is its own is refused',
         expect: 'Correlated claim on a shared reply end',
         src: tc("""class C {
                        static int canteen() {
                            @verification.SharedSend AsyncChannel<Integer> service = AsyncChannel.create(4)
                            @verification.SharedReceive AsyncChannel<Integer> deliver = AsyncChannel.create(4)
                            deliver.send(1)
                            deliver.send(2)
                            async {
                                int mine = 1
                                service.send(mine)
                                int r = deliver.first()
                                assert r == mine + 1
                            }
                            async {
                                int mine = 2
                                service.send(mine)
                                int r = deliver.first()
                            }
                            return 0
                        }
                    }""")],
        // The fix the gallery already certifies: give each client its OWN reply channel, and the
                // correlation is sound again — so the refusal is about the sharing, not about replies.
        [group: 'P284 shared ends', name: 'a private reply channel carries the correlation fine',
         expect: 'is declared @SharedSend', refute: 'Correlated claim on a shared reply end',
         src: tc("""class C {
                        static int privateReply() {
                            @verification.SharedSend AsyncChannel<Integer> service = AsyncChannel.create(4)
                            AsyncChannel<Integer> replyA = AsyncChannel.create(4)
                            replyA.send(2)
                            async {
                                int mine = 1
                                service.send(mine)
                                int r = replyA.first()
                                assert r == mine + 1
                            }
                            async { service.send(9) }
                            return 0
                        }
                    }""")],
    ]
}
