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
 * 'P250 streaming termination' — the structural half of symbolic streaming: a send inside a loop never
 * blocks, so it no longer voids the network certificate; it only makes the element count non-static.
 * A symbolic-count producer loop plus an unconditional close certifies its drain (GNumbers(n) → GPrint
 * terminates), while a blocking first() on such a channel is a named uncertifiable skip. The VALUE model
 * still refuses loop traffic loudly — that is the remaining (value) half of the frontier.
 */
class G314_p250_streaming_termination {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 250 streaming termination (slice 10 of the SEQ/PAR ladder; the structural half of symbolic streaming): a send inside a loop / if never blocks, so it no longer voids the network certificate — it only makes the channel\'s element count non-static. A symbolic-count producer loop (for (i in 0..<n) out.send(i)) followed by an unconditional close CERTIFIES its drain (for-in / toList wait for the close, not for a count): GNumbers(n) → GPrint terminates for every n, deadlock-freedom included, and the forgotten close is still the named hang. A blocking first() on a channel whose count is not static is a NAMED uncertifiable skip (it cannot be paired with a send), as is an ALT branch on such a channel. The value model keeps refusing loop traffic loudly — the value half of the streaming frontier remains.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // GNumbers(n) → GPrint: the drain's close dependency is satisfiable for EVERY n — the network
        // certificate is silent (no network skip, no deadlock); only the value model's loud refusal of
        // loop traffic remains (the honest half still open).
        [group: 'P250 streaming termination', name: 'a symbolic producer loop with a close certifies its drain', expect: 'Skipped channel verification', refute: 'network',
         src: tc("""class C {
                        static int numbersToPrint(int n) {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(4)
                            async {
                                for (i in 0..<n) {
                                    out.send(i)
                                }
                                out.close()
                            }
                            int seen = 0
                            for (v in out) {
                                seen = seen + 1
                            }
                            return seen
                        }
                    }""")],
        // Through a map stage, drained by toList in the body: same certificate.
        [group: 'P250 streaming termination', name: 'a symbolic pipeline drained by toList certifies', expect: 'Skipped channel verification', refute: 'network',
         src: tc("""class C {
                        static List<Integer> squares(int n) {
                            groovy.concurrent.AsyncChannel<Integer> nums = groovy.concurrent.AsyncChannel.create(4)
                            groovy.concurrent.AsyncChannel<Integer> sq = nums.map { it * it }
                            async {
                                for (i in 0..<n) {
                                    nums.send(i)
                                }
                                nums.close()
                            }
                            return sq.toList()
                        }
                    }""")],
        // The forgotten close is still the named hang — the loop send did not paper over it.
        [group: 'P250 streaming termination', name: 'a symbolic producer loop without a close: the drain never finishes', expect: 'can never finish',
         src: tc("""class C {
                        static int noClose(int n) {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(4)
                            async {
                                for (i in 0..<n) {
                                    out.send(i)
                                }
                            }
                            int seen = 0
                            for (v in out) {
                                seen = seen + 1
                            }
                            return seen
                        }
                    }""")],
        // A close INSIDE the loop is still conditional — uncertifiable, as before.
        [group: 'P250 streaming termination', name: 'a close inside the loop stays uncertifiable', expect: 'Skipped network well-formedness',
         src: tc("""class C {
                        static int closeInLoop(int n) {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(4)
                            async {
                                for (i in 0..<n) {
                                    out.send(i)
                                    out.close()
                                }
                            }
                            int seen = 0
                            for (v in out) {
                                seen = seen + 1
                            }
                            return seen
                        }
                    }""")],
        // A blocking first() on a channel whose count is not static: a named uncertifiable skip (n may
        // be 0 — the receive would hang), not a "no send" error and not a silent pass.
        [group: 'P250 streaming termination', name: 'a blocking receive on a non-static count is uncertifiable', expect: 'element count',
         src: tc("""class C {
                        static int firstOf(int n) {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(4)
                            async {
                                for (i in 0..<n) {
                                    out.send(i)
                                }
                                out.close()
                            }
                            return out.first()
                        }
                    }""")],
        // A conditional single send before a drain: same story — the count (0 or 1) is not static, the
        // drain waits for the close, certified.
        [group: 'P250 streaming termination', name: 'an if-send before a closed drain certifies', expect: 'Skipped channel verification', refute: 'network',
         src: tc("""class C {
                        static int maybeOne(boolean flag) {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(4)
                            if (flag) out.send(1)
                            out.close()
                            int seen = 0
                            for (v in out) {
                                seen = seen + 1
                            }
                            return seen
                        }
                    }""")],
    ]
}
