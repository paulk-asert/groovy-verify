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

/** 'P245 channel drain' — iteration, close, and the terminating network (slice 6 of the SEQ/PAR ladder). */
class G309_p245_channel_drain {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 245 channel drain discipline: `for (v in ch)` and the drain ops (toList/each/collect) are whole-stream receives that BLOCK UNTIL CLOSE — a new dependency family in the Phase 243 wait-for graph (an iteration completes only when its root\'s close() executes). The forgotten close errors ("can never finish — no close()"); a close behind the iteration — later in the same process, or in a task forked after it — is a circular wait; a conditional close is uncertifiable (loud skip); two concurrent iterators trip the Phase 241 receiver-linearity rule for free. The well-ordered shapes (producer task sends and closes, main iterates or drains) are certified silently — the PAR-termination story: every blocking op in a clean one-shot network completes. Value modelling stays out (the guard now also refuses loops and drains — a loop send can no longer half-rewrite), pinned by a loop-producer case that skips loudly instead of proving a FIFO-false value.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // ---------- the well-ordered drains: certified silently ----------
        // Producer task sends and CLOSES; main iterates. The iteration's wait-for dependency (its
        // root's close) is satisfiable — the network terminates. (Values stay unmodelled — honest.)
        [group: 'P245 channel drain', name: 'iterate with a closing producer finishes', ok: true,
         src: tc("""class C {
                        static int drain() {
                            AsyncChannel<Integer> src = AsyncChannel.create(4)
                            src.send(1)
                            src.close()
                            async {
                                int total = 0
                                for (v in src) {
                                    total = total + v
                                }
                            }
                            return 0
                        }
                    }""")],
        // The drain-op spelling: toList() blocks until close the same way. (The drained list's
        // CONTENTS stay unmodelled — the case returns a constant, honestly.)
        [group: 'P245 channel drain', name: 'toList with a closing producer finishes', ok: true,
         src: tc("""class C {
                        static int drainList() {
                            AsyncChannel<Integer> src = AsyncChannel.create(4)
                            async { src.send(7); src.close() }
                            def all = src.toList()
                            return 0
                        }
                    }""")],

        // ---------- the forgotten close, and closes in the wrong place ----------
        // No close anywhere: the iteration blocks forever — the classic hang, named.
        [group: 'P245 channel drain', name: 'iterating a never-closed channel hangs', expect: 'can never finish',
         src: tc("""class C {
                        static int forgotClose() {
                            AsyncChannel<Integer> src = AsyncChannel.create(4)
                            async { src.send(1) }
                            int total = 0
                            for (v in src) {
                                total = total + v
                            }
                            return total
                        }
                    }""")],
        // The close AFTER the iteration in the same process: the iteration waits for a close the
        // process would only reach afterwards — a circular wait.
        [group: 'P245 channel drain', name: 'closing after the iteration is a circular wait', expect: 'Process-network deadlock',
         src: tc("""class C {
                        static int closeAfter() {
                            AsyncChannel<Integer> src = AsyncChannel.create(4)
                            src.send(1)
                            async {
                                for (v in src) {
                                }
                                src.close()
                            }
                            return 0
                        }
                    }""")],
        // The closing task forked only after the iteration: main never gets there.
        [group: 'P245 channel drain', name: 'forking the closer after the iteration is a circular wait', expect: 'Process-network deadlock',
         src: tc("""class C {
                        static int closerTooLate() {
                            AsyncChannel<Integer> src = AsyncChannel.create(4)
                            src.send(1)
                            for (v in src) {
                            }
                            async { src.close() }
                            return 0
                        }
                    }""")],

        // ---------- the edges: linearity for free, conditional close uncertifiable ----------
        // Two live iterators split the stream — the Phase 241 receiver rule catches it unchanged.
        [group: 'P245 channel drain', name: 'two concurrent iterators split the stream', expect: 'Channel linearity',
         src: tc("""class C {
                        static int twoIterators() {
                            AsyncChannel<Integer> src = AsyncChannel.create(4)
                            async { src.send(1); src.close() }
                            async { for (v in src) { } }
                            for (w in src) {
                            }
                            return 0
                        }
                    }""")],
        // A close that may not run: the one-shot certificate does not apply — no claim either way.
        [group: 'P245 channel drain', name: 'a conditional close is uncertifiable', expect: 'Skipped network well-formedness',
         src: tc("""class C {
                        static int maybeClose(int x) {
                            AsyncChannel<Integer> src = AsyncChannel.create(4)
                            async {
                                src.send(1)
                                if (x > 0) {
                                    src.close()
                                }
                            }
                            for (v in src) {
                            }
                            return 0
                        }
                    }""")],

        // ---------- the guard hardening: loop traffic never half-rewrites ----------
        // A producer LOOP is unbounded traffic: the scalar rewrite refuses outright, so the wrong
        // claim skips loudly (FIFO first() is 0 here; nothing proves 3).
        [group: 'P245 channel drain', name: 'a loop producer skips instead of proving a FIFO-false value', expect: 'Skipped verification',
         src: tc("""class C {
                        @Ensures({ result == 3 })
                        static int loopSend() {
                            AsyncChannel<Integer> src = AsyncChannel.create(4)
                            int i = 0
                            while (i < 3) {
                                src.send(i)
                                i = i + 1
                            }
                            src.close()
                            return src.first()
                        }
                    }""")],
    ]
}
