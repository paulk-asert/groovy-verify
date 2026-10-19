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
 * 'P314 parallel callbacks' — the callbacks of a parallel-collection method (eachParallel, collectParallel, …,
 * and a @Parallel for loop, which lowers to eachParallel) are tasks on a ForkJoin pool, not processes: a
 * callback that blocks can hold its worker while the sibling it waits for stays queued (GROOVY-12457). Their
 * barrier / channel uses were counted as the calling process's, so a working sibling barrier was refuted as
 * short of parties. They are now recorded apart, and the method's certificates are withheld, loudly.
 */
class G359_p314_parallel_callbacks {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 314 parallel-collection callbacks (GROOVY-12457): the callbacks of eachParallel / collectParallel / … (and of a @Parallel for loop, which lowers to eachParallel) run as tasks on a ForkJoin pool, not as processes — how many run at once is the pool size against the element count, and a callback that blocks can hold its worker while the sibling it waits for stays queued, so the weak fairness the deadlock and liveness certificates rest on does not hold. A barrier sync, channel op, select or drain inside such a callback was counted as the calling process\'s (a working sibling barrier was refuted as short of parties); it is now recorded apart, and the method\'s barrier / network certificates are withheld with a skip naming the callback. Callbacks that block on nothing are unaffected.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // GROOVY-12457's shape: sibling callbacks meeting at a barrier. Two pool tasks arrive — it was refuted
        // as one process short; whether both ever run at once is the pool's call, so no certificate either way.
        [group: 'P314 parallel callbacks', name: 'sibling callbacks syncing a barrier withhold the certificate',
         expect: "Skipped barrier certificate for 'gate' in run (its arriveAndAwaitAdvance() at line 6 is inside the eachParallel callback",
         refute: 'can never advance',
         src: tc("""class C {
                        static int run() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            [1, 2].eachParallel { gate.arriveAndAwaitAdvance() }
                            return 0
                        }
                    }""")],
        // The same through @Parallel: the diagnostic names the loop, as written, not the lowered call.
        [group: 'P314 parallel callbacks', name: 'a @Parallel loop body syncing a barrier withholds the certificate',
         expect: 'inside the @Parallel loop', refute: 'can never advance',
         src: tc("""class C {
                        static int run() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            @groovy.transform.Parallel
                            for (int i in 0..1) {
                                gate.arriveAndAwaitAdvance()
                            }
                            return 0
                        }
                    }""")],
        // A forked process whose callbacks sync with the main body: the arm side is recognised too.
        [group: 'P314 parallel callbacks', name: 'callbacks inside a forked process withhold the certificate',
         expect: "Skipped barrier certificate for 'gate'", refute: 'can never advance',
         src: tc("""class C {
                        static int run() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(3)
                            async {
                                [1, 2].eachParallel { gate.arriveAndAwaitAdvance() }
                            }
                            gate.arriveAndAwaitAdvance()
                            return 0
                        }
                    }""")],
        // Siblings exchanging over a rendezvous channel: the sender holds its worker until a receiver runs.
        [group: 'P314 parallel callbacks', name: 'sibling callbacks exchanging over a channel withhold the network check',
         expect: "Skipped network well-formedness check for 'ch' in run (its send() at line 8 is inside the eachParallel callback at line 6)",
         src: tc("""class C {
                        static int run() {
                            AsyncChannel<Integer> ch = AsyncChannel.create(0)
                            [0, 1].eachParallel { int i ->
                                if (i == 0) {
                                    ch.send(1)
                                } else {
                                    int x = ch.first()
                                }
                            }
                            return 0
                        }
                    }""")],
        // A drain inside a callback blocks until the producer's close — on a pool worker.
        [group: 'P314 parallel callbacks', name: 'a drain inside a callback withholds the network check',
         expect: "(its iteration at line 13 is inside the eachParallel callback at line 12)",
         src: tc("""class C {
                        static int run() {
                            AsyncChannel<Integer> out = AsyncChannel.create(2)
                            async {
                                out.send(1)
                                out.send(2)
                                out.close()
                            }
                            int seen = 0
                            [1].eachParallel {
                                for (v in out) {
                                    seen = seen + 1
                                }
                            }
                            return seen
                        }
                    }""")],
        // A callback that blocks on nothing is the ordinary use: no skip.
        [group: 'P314 parallel callbacks', name: 'a callback that blocks on nothing is unaffected', ok: true,
         src: tc("""class C {
                        static List<Integer> run() {
                            return [1, 2, 3].collectParallel { int v -> v * 2 }
                        }
                    }""")],
        // ... and does not cost a certified barrier between processes its certificate.
        [group: 'P314 parallel callbacks', name: 'a non-blocking callback beside a lockstep barrier: still certified', ok: true,
         src: tc("""class C {
                        static int phases() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            AsyncChannel<Integer> done = AsyncChannel.create(2)
                            async {
                                gate.arriveAndAwaitAdvance()
                                done.send(1)
                            }
                            List<Integer> ys = [1, 2].collectParallel { int v -> v * 2 }
                            gate.arriveAndAwaitAdvance()
                            return done.first()
                        }
                    }""")],
        // The certificate it replaces still bites where a process really is missing: no parallel callback here.
        [group: 'P314 parallel callbacks', name: 'a barrier one process short still refutes', expect: 'can never advance',
         src: tc("""class C {
                        static int run() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            gate.arriveAndAwaitAdvance()
                            return 0
                        }
                    }""")],
    ]
}
