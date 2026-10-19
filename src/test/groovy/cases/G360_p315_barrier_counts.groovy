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
 * 'P315 barrier counts' — a soundness fix to the Phase 277 barrier certificate. With static enrolment every
 * round needs every party, so the certificate rests on each process's sync COUNT. Only "too few processes" was
 * checked: a process syncing more often than its partner, a surplus process, and syncs that may run zero times
 * or many (in an if / loop / catch / closure, skipped silently) all certified while hanging at runtime.
 */
class G360_p315_barrier_counts {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 315 barrier counts (a soundness fix to the Phase 277 barrier certificate): with static enrolment every round needs every party, so the certificate rests on each process\'s sync count. Exactly N processes with unequal counts are refuted (the round after the fewest never fills — a finished process does not deregister); more processes than parties are refuted when the one-shot arrivals are not a whole number of rounds, and otherwise skipped loudly (who meets in which round is decided at runtime); a sync that is not one-shot (inside an if / loop / catch / closure, on either side) withholds the barrier\'s certificate loudly, where it used to be skipped silently and the barrier certified.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // ---------- counts: every sync one-shot ----------
        // The plainest hang there is: one more sync than the partner. The second round waits for a process
        // that has finished. This compiled clean.
        [group: 'P315 barrier counts', name: 'one more sync than the partner is refuted',
         expect: "Barrier 'gate' in 'run' can never complete round 2: its 2 parties are the 2 processes that sync on it, and the method body syncs 2 times but the task forked at line 6 only 1",
         src: tc("""class C {
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
        // The same the other way round: the task is the one left waiting.
        [group: 'P315 barrier counts', name: 'a task with one sync too many is refuted',
         expect: 'the task forked at line 6 syncs 2 times but the method body only 1',
         src: tc("""class C {
                        static int run() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            async {
                                gate.arriveAndAwaitAdvance()
                                gate.arriveAndAwaitAdvance()
                            }
                            gate.arriveAndAwaitAdvance()
                            return 0
                        }
                    }""")],
        // Three processes on a two-party barrier, once each: three arrivals are not a whole number of rounds.
        [group: 'P315 barrier counts', name: 'a surplus process that can never be partnered is refuted',
         expect: "always leaves a process waiting: it is constructed for 2 parties, and the 3 processes that sync on it arrive 3 times in all",
         src: tc("""class C {
                        static int run() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            async {
                                gate.arriveAndAwaitAdvance()
                            }
                            async {
                                gate.arriveAndAwaitAdvance()
                            }
                            gate.arriveAndAwaitAdvance()
                            return 0
                        }
                    }""")],
        // Four on two, once each: two whole rounds — it can work out, but who meets whom is the scheduler's.
        [group: 'P315 barrier counts', name: 'surplus processes in whole rounds are skipped, not certified',
         expect: "Skipped barrier certificate for 'gate' in run (4 processes sync on it, but it is constructed for 2 parties)",
         src: tc("""class C {
                        static int run() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            async {
                                gate.arriveAndAwaitAdvance()
                            }
                            async {
                                gate.arriveAndAwaitAdvance()
                            }
                            async {
                                gate.arriveAndAwaitAdvance()
                            }
                            gate.arriveAndAwaitAdvance()
                            return 0
                        }
                    }""")],
        // Three parties in lockstep for two rounds: equal counts, every round full — still certified.
        [group: 'P315 barrier counts', name: 'three processes in lockstep for two rounds: certified', ok: true,
         src: tc("""class C {
                        static int run() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(3)
                            async {
                                gate.arriveAndAwaitAdvance()
                                gate.arriveAndAwaitAdvance()
                            }
                            async {
                                gate.arriveAndAwaitAdvance()
                                gate.arriveAndAwaitAdvance()
                            }
                            gate.arriveAndAwaitAdvance()
                            gate.arriveAndAwaitAdvance()
                            return 0
                        }
                    }""")],

        // ---------- syncs that are not one-shot ----------
        // A sync in a loop: two rounds against a partner's one. Skipped silently before, so it certified.
        [group: 'P315 barrier counts', name: 'a sync in a loop withholds the certificate',
         expect: "Skipped barrier certificate for 'gate' in run (its arriveAndAwaitAdvance() at line 10 is not one-shot",
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
        // A sync in an if: zero rounds or one.
        [group: 'P315 barrier counts', name: 'a sync in an if withholds the certificate', expect: 'is not one-shot',
         src: tc("""class C {
                        static int run(boolean b) {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            async {
                                gate.arriveAndAwaitAdvance()
                            }
                            if (b) {
                                gate.arriveAndAwaitAdvance()
                            }
                            return 0
                        }
                    }""")],
        // A sequential each runs its closure once per element; the closure's one sync was counted as one.
        [group: 'P315 barrier counts', name: 'a sync in an each closure withholds the certificate', expect: 'is not one-shot',
         src: tc("""class C {
                        static int run() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            async {
                                gate.arriveAndAwaitAdvance()
                            }
                            [1, 2].each { gate.arriveAndAwaitAdvance() }
                            return 0
                        }
                    }""")],
        // A closure that is never called: its sync was counted as the method body's, and the task's partner
        // never arrives.
        [group: 'P315 barrier counts', name: 'a sync in a closure never called withholds the certificate', expect: 'is not one-shot',
         src: tc("""class C {
                        static int run() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            async {
                                gate.arriveAndAwaitAdvance()
                            }
                            Closure c = { gate.arriveAndAwaitAdvance() }
                            return 0
                        }
                    }""")],
        // The task side too: a closure nested in a forked process.
        [group: 'P315 barrier counts', name: 'a task syncing in a nested closure withholds the certificate', expect: 'is not one-shot',
         src: tc("""class C {
                        static int run() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            async {
                                [1, 2].each { gate.arriveAndAwaitAdvance() }
                            }
                            gate.arriveAndAwaitAdvance()
                            return 0
                        }
                    }""")],
        // The boundary, stated: a forever lockstep is fine at runtime, but its count is unbounded — skipped.
        [group: 'P315 barrier counts', name: 'a while (true) lockstep is skipped, not certified', expect: 'is not one-shot',
         src: tc("""class C {
                        static void run() {
                            java.util.concurrent.Phaser gate = new java.util.concurrent.Phaser(2)
                            async {
                                while (true) {
                                    gate.arriveAndAwaitAdvance()
                                }
                            }
                            while (true) {
                                gate.arriveAndAwaitAdvance()
                            }
                        }
                    }""")],
    ]
}
