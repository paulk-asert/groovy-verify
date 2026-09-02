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
 * 'P277 barriers' — the first barrier rung, and the first synchronisation in this gallery that is not a
 * channel. Kerridge c14 builds its whole system on JCSP's `Barrier` (sync / enroll / resign) and
 * `AltingBarrier`; `java.util.concurrent.Phaser` is that Barrier under another name —
 * `arriveAndAwaitAdvance()` is sync, `register()` / `arriveAndDeregister()` are enroll / resign — so the
 * shapes port with no new runtime primitive. This slice models STATIC enrolment: a phaser built with a
 * literal party count, arrived at by that many processes. A round is the j-th sync of every party, and the
 * round is ONE synchronisation — each party inherits the round's program-order predecessors and none waits
 * on another, exactly as a rendezvous send and its receive are coalesced (Phase 272), lifted from two
 * parties to n. Dynamic enrolment is the next rung, not this one.
 */
class G336_p277_barriers {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 277 barriers (slice 38 of the SEQ/PAR ladder): the first non-channel synchronisation in the ladder — Kerridge c14\'s `Barrier`, ported onto `java.util.concurrent.Phaser` (`arriveAndAwaitAdvance()` = sync), which needs no new runtime primitive. STATIC enrolment only: a phaser constructed with a literal party count and arrived at by that many processes. A barrier ROUND (the j-th sync of every party) is coalesced into one synchronisation — each party inherits the round\'s program-order predecessors and none waits on another, the n-way lift of Phase 272\'s rendezvous pair — so a matched barrier is not itself a cycle and a real circular wait has to close through some other event: two barriers synced in opposite orders by two processes is the classic knot, refuted with the cycle spelled out. A barrier constructed for more parties than ever arrive can never advance, and is refuted with both counts. Dynamic enrolment (register / arriveAndDeregister) is deliberately not modelled here.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [
        // ---------- barriers AND channels in one network (Phase 283) ----------
        // c14's real shape: the targets agree on a phase with barriers while also exchanging messages over
        // channels. A knot can close through both media at once — here one party waits for a message before
        // it syncs, holding the phase up, while the party that would send it waits for the phase. The
        // `expect` pins the wording: a barrier in the cycle must read as a SYNC, not as a receive.
        [group: 'P277 barriers', name: 'a knot closed by a barrier and a channel together', expect: "which waits for the sync on 'gate'",
         src: tc("""class C {
                        static int mixed() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            AsyncChannel<Integer> ch = AsyncChannel.create(1)
                            async {
                                int x = ch.first()
                                gate.arriveAndAwaitAdvance()
                            }
                            gate.arriveAndAwaitAdvance()
                            ch.send(1)
                            return 0
                        }
                    }""")],
        // The same two media in the same order in both parties — sync, then exchange — and it certifies.
        [group: 'P277 barriers', name: 'sync then exchange in every party: certified', ok: true,
         src: tc("""class C {
                        static int mixedOk() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            AsyncChannel<Integer> ch = AsyncChannel.create(1)
                            async {
                                gate.arriveAndAwaitAdvance()
                                int x = ch.first()
                            }
                            gate.arriveAndAwaitAdvance()
                            ch.send(1)
                            return 0
                        }
                    }""")],
        // A regression, found while building this rung: a local bound to `new …` carried an
        // undischargeable null-deref obligation, so ordinary code refuted. A constructor yields an object
        // or throws — never null — which generalises the channel-factory and held-select exemptions.
        [group: 'P277 barriers', name: 'a local bound to new is never null (no deref obligation)', ok: true,
         src: tc("""class C {
                        static int plain() {
                            StringBuilder sb = new StringBuilder()
                            sb.append('x')
                            return 0
                        }
                    }""")],
        // 1 — the shape c14 is built on: N processes advancing in lockstep through phases.
        [group: 'P277 barriers', name: 'a two-party barrier in lockstep: certified', ok: true,
         src: tc("""class C {
                        static int phases() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            AsyncChannel<Integer> done = AsyncChannel.create(2)
                            async {
                                gate.arriveAndAwaitAdvance()
                                gate.arriveAndAwaitAdvance()
                                done.send(1)
                            }
                            gate.arriveAndAwaitAdvance()
                            gate.arriveAndAwaitAdvance()
                            return done.first()
                        }
                    }""")],
        // 2 — the classic barrier deadlock: two barriers synced in opposite orders.
        [group: 'P277 barriers', name: 'two barriers synced in opposite orders: circular wait', expect: 'Process-network deadlock',
         src: tc("""class C {
                        static int crossed() {
                            java.util.concurrent.Phaser first = new java.util.concurrent.Phaser(2)
                            java.util.concurrent.Phaser second = new java.util.concurrent.Phaser(2)
                            async {
                                first.arriveAndAwaitAdvance()
                                second.arriveAndAwaitAdvance()
                            }
                            second.arriveAndAwaitAdvance()
                            first.arriveAndAwaitAdvance()
                            return 0
                        }
                    }""")],
        // 3 — a barrier constructed for more parties than ever arrive never advances.
        [group: 'P277 barriers', name: 'a party that never arrives leaves the barrier stuck', expect: 'can never advance',
         src: tc("""class C {
                        static int shortParty() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(3)
                            async {
                                gate.arriveAndAwaitAdvance()
                            }
                            gate.arriveAndAwaitAdvance()
                            return 0
                        }
                    }""")],

        // ---------- dynamic enrolment: c14's own enroll / sync / resign pairing (Phase 278) ----------
        // TargetProcess resigns up front, then each round enrols, syncs, and resigns again — so a target
        // takes part only in the rounds it is active for. The discipline is checked; the party count and
        // deadlock-freedom are withheld, because a round's party set is now a runtime value.
        [group: 'P277 barriers', name: 'enrol / sync / resign, the c14 pairing: discipline holds, the count is withheld', expect: 'Skipped barrier certificate',
         refute: 'Barrier discipline violated',
         src: tc("""class C {
                        static int rounds() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(1)
                            async {
                                gate.register()
                                gate.arriveAndAwaitAdvance()
                                gate.arriveAndDeregister()
                            }
                            gate.arriveAndAwaitAdvance()
                            return 0
                        }
                    }""")],
        // The mistake the pairing exists to prevent: syncing on a barrier this process has resigned from.
        [group: 'P277 barriers', name: 'a sync after resigning is refused', expect: 'Barrier discipline violated',
         src: tc("""class C {
                        static int stale() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            async {
                                gate.arriveAndAwaitAdvance()
                            }
                            gate.arriveAndDeregister()
                            gate.arriveAndAwaitAdvance()
                            return 0
                        }
                    }""")],
        // …and resigning twice, which gives up a party the process no longer holds.
        [group: 'P277 barriers', name: 'resigning twice is refused', expect: 'Barrier discipline violated',
         src: tc("""class C {
                        static int twice() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            async {
                                gate.arriveAndAwaitAdvance()
                            }
                            gate.arriveAndDeregister()
                            gate.arriveAndDeregister()
                            return 0
                        }
                    }""")],
    ]
}
