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
 * 'P316 barrier loops' — a literal-bounded loop that syncs a barrier unrolls before the structural walk (the
 * Phase 248 unroller, now keyed on Phaser vars as well as channels), so `for (i in 0..<k)` is k one-shot syncs
 * and the Phase 315 counts decide it: a lockstep certifies, a count mismatch is refuted, and a symbolic bound
 * or one over the unroll limit keeps the loud not-one-shot skip.
 */
class G361_p316_barrier_loops {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 316 literal-bounded barrier loops: a loop with a literal bound (for (i in 0..<k), for (i in a..b), for (int i = 0; i < k; i++)) that syncs a Phaser unrolls before the structural walk — the Phase 248 unroller, now keyed on barrier vars as well as channels, in the method body and in forked tasks — so its syncs are k one-shot syncs the Phase 315 counts decide: a lockstep of loops certifies, a loop of k against a partner\'s m ≠ k is refuted at round m + 1, and barriers crossed inside loops are the named circular wait. A symbolic bound, a loop over the unroll limit (32) and while (true) keep the loud not-one-shot skip.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // c14's shape with a literal round count: both processes advance through three phases, written as loops
        // (one for-in, one C-style). Before this phase the loop syncs were not one-shot and the certificate skipped.
        [group: 'P316 barrier loops', name: 'a lockstep of literal-bounded loops: certified', ok: true,
         src: tc("""class C {
                        static int run() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            async {
                                for (int i in 0..<3) {
                                    gate.arriveAndAwaitAdvance()
                                }
                            }
                            for (int j = 0; j < 3; j++) {
                                gate.arriveAndAwaitAdvance()
                            }
                            return 0
                        }
                    }""")],
        // Two rounds against one: the second round waits for a task that has finished. Phase 315 could only skip.
        [group: 'P316 barrier loops', name: 'a loop of two against a single sync is refuted',
         expect: "can never complete round 2: its 2 parties are the 2 processes that sync on it, and the method body syncs 2 times but the task forked at line 6 only 1",
         src: tc("""class C {
                        static int run() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            async {
                                gate.arriveAndAwaitAdvance()
                            }
                            for (int i in 0..1) {
                                gate.arriveAndAwaitAdvance()
                            }
                            return 0
                        }
                    }""")],
        // Loops in both processes with different literal bounds: three rounds against two.
        [group: 'P316 barrier loops', name: 'loops with different literal bounds are refuted',
         expect: 'the task forked at line 6 syncs 3 times but the method body only 2',
         src: tc("""class C {
                        static int run() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            async {
                                for (int i in 1..3) {
                                    gate.arriveAndAwaitAdvance()
                                }
                            }
                            for (int i in 0..<2) {
                                gate.arriveAndAwaitAdvance()
                            }
                            return 0
                        }
                    }""")],
        // Crossed barriers inside the loops: the first iteration already knots, and the wait cycle names it.
        [group: 'P316 barrier loops', name: 'barriers crossed inside literal loops: circular wait', expect: 'Process-network deadlock',
         src: tc("""class C {
                        static int run() {
                            java.util.concurrent.Phaser a = new java.util.concurrent.Phaser(2)
                            java.util.concurrent.Phaser b = new java.util.concurrent.Phaser(2)
                            async {
                                for (int i in 0..<2) {
                                    a.arriveAndAwaitAdvance()
                                    b.arriveAndAwaitAdvance()
                                }
                            }
                            for (int i in 0..<2) {
                                b.arriveAndAwaitAdvance()
                                a.arriveAndAwaitAdvance()
                            }
                            return 0
                        }
                    }""")],
        // The boundary: over the unroll limit the loop stays a loop, and the count is unknown — skipped loudly.
        [group: 'P316 barrier loops', name: 'a loop over the unroll limit keeps the skip', expect: 'is not one-shot',
         src: tc("""class C {
                        static int run() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            async {
                                for (int i in 0..<40) {
                                    gate.arriveAndAwaitAdvance()
                                }
                            }
                            for (int i in 0..<40) {
                                gate.arriveAndAwaitAdvance()
                            }
                            return 0
                        }
                    }""")],
    ]
}
