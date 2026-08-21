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

/** 'P240 par interference' — the fork-window disjointness check (slice 1 of the SEQ/PAR ladder). */
class G304_p240_par_interference {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 240 PAR disjointness: the side condition the async safe-value model (Phases 118/119/153-155) had assumed is now checked — between an async task\'s fork and its join, the enclosing body must not write anything the task reads or writes (stale-read races over a local, a field, and through a gather all error as "Parallel interference" instead of proving the post-write value), the body must not read anything the task writes, and two tasks with overlapping fork-join windows must not conflict (write-vs-touch). The join is the first mention of the task\'s handle after the fork, so a write after the join, or between one task\'s join and the next task\'s fork, is safe and still proves; DataflowVariable and AsyncChannel locals and the Awaitable handles are exempt (the synchronisation media, like channels in the CSP PAR rule).'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // ---------- Phase 240: fork-window interference REFUTATIONS ----------
        // Before this phase, each of these PROVED the post-write value — the safe-value model
        // resolved the arm's captured read at the read-out site, after the interfering write.
        // A racy read is a genuine bug (the task may run before or after the write), so it errors.
        [group: 'P240 par interference', name: 'stale read: body writes a captured local between fork and await', expect: 'Parallel interference',
         src: tc('''class C {
                        @Ensures({ result == 101 })
                        static int stale() {
                            int s = 0
                            def fa = async { s + 1 }
                            s = 100
                            int a = await fa
                            return a
                        }
                    }''')],
        // The field version of the same race.
        [group: 'P240 par interference', name: 'stale read: body writes a captured field between fork and await', expect: 'Parallel interference',
         src: tc('''class C {
                        int x
                        @Ensures({ result == 101 })
                        int staleField() {
                            def fa = async { x + 1 }
                            x = 100
                            int a = await fa
                            return a
                        }
                    }''')],
        // Through the multi-arg gather: t1 forked before the write, joined after it — racy.
        // (Before this phase the case surfaced only as accidental r[0] bounds noise.)
        [group: 'P240 par interference', name: 'stale read through a gather (write inside the first task\'s window)', expect: 'Parallel interference',
         src: tc('''class C {
                        @Ensures({ result == 102 })
                        static int staleGather() {
                            int s = 1
                            def t1 = async { s + 1 }
                            s = 50
                            def t2 = async { s + 1 }
                            def r = await(t1, t2)
                            return ((int) r[0]) + ((int) r[1])
                        }
                    }''')],
        // Arm-vs-arm, write against write: the RacyGather shape — two concurrent read-modify-writes.
        [group: 'P240 par interference', name: 'two concurrent tasks write the same local (racy gather)', expect: 'Parallel interference',
         src: tc('''class C {
                        @Ensures({ result == 2 })
                        static int racy() {
                            int s = 0
                            def t1 = async { s = s + 1 }
                            def t2 = async { s = s + 1 }
                            await(t1, t2)
                            return s
                        }
                    }''')],
        // Arm-vs-arm, write against read: one task writes what its concurrent sibling reads.
        [group: 'P240 par interference', name: 'one task writes what a concurrent task reads', expect: 'Parallel interference',
         src: tc('''class C {
                        static int writeVsRead() {
                            int s = 0
                            def t1 = async { s = 5 }
                            def t2 = async { s + 1 }
                            def r = await(t1, t2)
                            return (int) r[1]
                        }
                    }''')],
        // Body-read against arm-write: the mirror direction — the body reads while the task may write.
        [group: 'P240 par interference', name: 'body reads what a live task writes', expect: 'Parallel interference',
         src: tc('''class C {
                        static int readRace() {
                            int s = 0
                            def fa = async { s = 5 }
                            int b = s
                            await fa
                            return b
                        }
                    }''')],

        // ---------- window precision: sequentially-separated accesses stay green ----------
        // A write AFTER the join is ordinary sequential code — proves, no interference.
        [group: 'P240 par interference', name: 'a write after the join is safe (proves)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == x + 101 })
                        static int postJoinWrite(int x) {
                            int s = x
                            def fa = async { s + 1 }
                            int a = await fa
                            s = 100
                            return a + s
                        }
                    }''')],
        // A write BETWEEN one task's join and the next task's fork is safe: the windows are
        // disjoint, and each await reads the value its task saw (a == 1, b == 101).
        [group: 'P240 par interference', name: 'a write between sequential fork-join pairs is safe (proves)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 102 })
                        static int sequentialPairs() {
                            int s = 0
                            def fa = async { s + 1 }
                            int a = await fa
                            s = 100
                            def fb = async { s + 1 }
                            int b = await fb
                            return a + b
                        }
                    }''')],
        // Disjoint state: the body writes a DIFFERENT variable inside the window — no conflict.
        [group: 'P240 par interference', name: 'a window write to disjoint state is safe (proves)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == x + 8 })
                        static int disjointState(int x) {
                            int other = 0
                            def fa = async { x + 1 }
                            other = 7
                            int a = await fa
                            return a + other
                        }
                    }''')],

        // ---------- boundary: an arm write with no concurrent toucher is not interference ----------
        // The task writes `s`, but the body only reads it AFTER the join — sequentially safe, so no
        // interference error (pinned via `refute`). The side-effecting await stays outside the
        // safe-value model, so the postcondition still skips loudly — the pre-existing boundary.
        [group: 'P240 par interference', name: 'arm write read only after the join: no interference, still the model skip', expect: 'Skipped verification', refute: 'Parallel interference',
         src: tc('''class C {
                        @Ensures({ result == 5 })
                        static int armWrite() {
                            int s = 0
                            def fa = async { s = 5 }
                            await fa
                            return s
                        }
                    }''')],
    ]
}
