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
 * 'P317 barrier values' — a barrier orders processes and moves no data, so the value model sees the body without
 * its Phasers: the declaration and every statement-level call on one are dropped (in the body, if-branches and
 * async arms) after the network check has had them. A value computed across barrier rounds now proves; a Phaser
 * used any other way (its phase read) keeps the loud outside-fragment skip.
 */
class G362_p317_barrier_values {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 317 barrier values: a barrier orders processes and moves no data, so with PAR disjointness the values a method computes are those of its body without the barrier. The value model now drops each Phaser\'s declaration and every statement-level call on it (in the body, if-branches and async arms — rebuilt, never mutated; an arm left empty goes too), after the network check has used them: @Ensures on a barrier-synchronised computation proves (a wrong claim is refuted) where it was skipped as outside the fragment. Ordering and progress stay the network check\'s claim, reported independently. A Phaser used any other way — its phase number read, passed to a call — is left alone and keeps the loud skip.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final String LOCKSTEP_SUM = """java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            AsyncChannel<Integer> done = AsyncChannel.create(2)
                            async {
                                int s = 0
                                for (int i in 0..<3) {
                                    s = s + i
                                    gate.arriveAndAwaitAdvance()
                                }
                                done.send(s)
                            }
                            for (int i in 0..<3) {
                                gate.arriveAndAwaitAdvance()
                            }
                            return done.first()"""

    static final List<Map> CASES = [

        // The Phase 316 lockstep with work between the rounds: the task's sum comes out through a channel, and
        // the claim about it proves. It was "outside fragment" before — a Phaser declaration is not a value.
        [group: 'P317 barrier values', name: 'a value computed across lockstep rounds proves', ok: true,
         src: tc("""class C {
                        @Ensures({ result == 3 })
                        static int run() {
                            ${LOCKSTEP_SUM}
                        }
                    }""")],
        // …and a wrong claim about it is refuted, so the proof above is not vacuous.
        [group: 'P317 barrier values', name: 'a wrong value across lockstep rounds is refuted',
         expect: 'Cannot prove postcondition of run',
         src: tc("""class C {
                        @Ensures({ result == 4 })
                        static int run() {
                            ${LOCKSTEP_SUM}
                        }
                    }""")],
        // Sync, then exchange: the request goes out after the phase, and the reply's value proves over a parameter.
        [group: 'P317 barrier values', name: 'a reply after a barrier phase proves over a parameter', ok: true,
         src: tc("""class C {
                        @Ensures({ result == 2 * v })
                        static int run(int v) {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            AsyncChannel<Integer> req = AsyncChannel.create(1)
                            AsyncChannel<Integer> rep = AsyncChannel.create(1)
                            async {
                                gate.arriveAndAwaitAdvance()
                                int x = req.first()
                                rep.send(2 * x)
                            }
                            gate.arriveAndAwaitAdvance()
                            req.send(v)
                            return rep.first()
                        }
                    }""")],
        // One process and a one-party barrier: plain sequential code around a sync.
        [group: 'P317 barrier values', name: 'sequential code around a sync proves', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x + 1 })
                        static int run(int x) {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(1)
                            int y = x + 1
                            gate.arriveAndAwaitAdvance()
                            return y
                        }
                    }""")],
        // A sync in an if: the barrier certificate skips (Phase 315), the value claim is decided independently.
        [group: 'P317 barrier values', name: 'a sync in a branch: the barrier skips, the value proves',
         expect: 'is not one-shot', refute: ['Cannot prove', 'Skipped verification of postcondition'],
         src: tc("""class C {
                        @Ensures({ result == (b ? 1 : 2) })
                        static int run(boolean b) {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(1)
                            int r = 2
                            if (b) {
                                gate.arriveAndAwaitAdvance()
                                r = 1
                            }
                            return r
                        }
                    }""")],
        // The two claims are independent: a deadlocked network is still refuted, whatever the value says.
        [group: 'P317 barrier values', name: 'a stuck barrier is still refuted beside a value claim',
         expect: 'can never complete round 2', refute: 'Skipped verification of postcondition',
         src: tc("""class C {
                        @Ensures({ result == 0 })
                        static int run() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            async {
                                gate.arriveAndAwaitAdvance()
                            }
                            gate.arriveAndAwaitAdvance()
                            gate.arriveAndAwaitAdvance()
                            return 0
                        }
                    }""")],
        // The phase number IS a value, and not one the model has: such a Phaser is left in, and skipped loudly.
        [group: 'P317 barrier values', name: 'a phase number read keeps the skip',
         expect: "Skipped verification of postcondition for run (assignment 'gate = new java.util.concurrent.Phaser(1)' is outside fragment)",
         src: tc("""class C {
                        @Ensures({ result >= 0 })
                        static int run() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(1)
                            int p = gate.arriveAndAwaitAdvance()
                            return p
                        }
                    }""")],
    ]
}
