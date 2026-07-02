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

/** 'P119 channels' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G227_p119_channels {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A channel pipeline collapses to function composition (FIFO assumed) and proves the per-element transform; a wrong transform refutes.'

    static final List<Map> CASES = [
        // ---------- P119 channels: the per-element transform via FIFO ----------
        // A channel's structural guarantee is FIFO delivery: the i-th value received is the i-th value sent,
        // run through the pipeline's pure stages. So for a representative element the network collapses to
        // function composition (the combiner trick): `src.send(x)` is `src = x`, each `map { f }` stage is `f`
        // applied to the upstream value, and receiving one element (`first()`) is a read. We prove that
        // per-element transform; FIFO ordering is the half we assume (we don't prove delivery or termination).
        // A two-stage `map` pipeline (note the producer in a trailing async — resolved lazily at the receive):
        [group: 'P119 channels', name: 'channel map pipeline composes', ok: true,
         src: tc("""class C {
                        @Ensures({ result == (x + 1) * 2 })
                        static int pipe(int x) {
                            groovy.concurrent.AsyncChannel<Integer> src = groovy.concurrent.AsyncChannel.create(1)
                            groovy.concurrent.AsyncChannel<Integer> out = src.map { it + 1 }.map { it * 2 }
                            async { src.send(x); src.close() }
                            return out.first()
                        }
                    }""")],
        // A wrong functional claim about the same pipeline is still refuted with a counterexample — FIFO buys
        // the order, not the arithmetic.
        [group: 'P119 channels', name: 'wrong channel transform is refuted', ok: false, expect: 'result',
         src: tc("""class C {
                        @Ensures({ result == x + 1 })
                        static int pipe(int x) {
                            groovy.concurrent.AsyncChannel<Integer> src = groovy.concurrent.AsyncChannel.create(1)
                            groovy.concurrent.AsyncChannel<Integer> out = src.map { it + 1 }.map { it * 2 }
                            async { src.send(x); src.close() }
                            return out.first()
                        }
                    }""")],
        // Producer-first ordering (send before the pipeline is built) proves the same way — a single `map` stage.
        [group: 'P119 channels', name: 'single-stage channel transform (producer first)', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x * 3 })
                        static int triple(int x) {
                            groovy.concurrent.AsyncChannel<Integer> src = groovy.concurrent.AsyncChannel.create(1)
                            src.send(x)
                            src.close()
                            groovy.concurrent.AsyncChannel<Integer> out = src.map { it * 3 }
                            return out.first()
                        }
                    }""")],
    ]
}
