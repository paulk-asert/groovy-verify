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

/** 'P242 channel contracts' — the element type is the protocol invariant (slice 3 of the SEQ/PAR ladder). */
class G306_p242_channel_contracts {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 242 channel contracts: Bean Validation bounds on a channel\'s element type (`AsyncChannel<@PositiveOrZero Integer>`) are the channel\'s protocol invariant — CHECKED at each send (an assert at the send site, refuting with a counterexample) and ASSUMED at each receive from a channel-typed parameter (the producer lives in another method, checked by its own compilation). That is the compositional rule: producer and consumer verify separately against the type, no whole-network analysis. An unconstrained param channel binds an unconstrained fresh receive value, so a postcondition stronger than the contract honestly refutes instead of skipping. Local channels get the same send assert inside the pipeline rewrite, which is now single-assignment (the send declares the scalar; the create placeholder is gone) — so a never-sent channel read proves NOTHING (it previously proved the placeholder 0 where the runtime blocks forever), and channel receives are exempt from the collection non-empty obligation (a receive blocks; delivery is the assumed structural half). Fragment: int/long elements, numeric bounds (@Positive/@PositiveOrZero/@Negative/@NegativeOrZero/@Min/@Max; @NotNull a no-op); any other jakarta constraint on a channel element skips loudly.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // ---------- the producer half: sends are CHECKED against the element bounds ----------
        // `ch.send(x * x)` on a @PositiveOrZero channel: the send becomes `assert x * x >= 0`,
        // which proves — the producer's compilation carries its half of the contract.
        [group: 'P242 channel contracts', name: 'producer send proves the element bound', ok: true,
         src: tc("""class C {
                        static void produce(groovy.concurrent.AsyncChannel<@PositiveOrZero Integer> ch, int x) {
                            ch.send(x * x)
                        }
                    }""")],
        // Soundness: a send that can violate the bound refutes with a counterexample.
        [group: 'P242 channel contracts', name: 'producer send refutes with a counterexample', expect: 'Assertion may not hold',
         src: tc("""class C {
                        static void produce(groovy.concurrent.AsyncChannel<@Min(0L) Integer> ch, int x) {
                            ch.send(x - 1)
                        }
                    }""")],
        // An upper bound is checked the same way: 7 can't go down a @Max(6) channel.
        [group: 'P242 channel contracts', name: 'producer send over the upper bound refutes', expect: 'Assertion may not hold',
         src: tc("""class C {
                        static void roll(groovy.concurrent.AsyncChannel<@Min(1L) @Max(6L) Integer> ch) {
                            ch.send(7)
                        }
                    }""")],

        // ---------- the consumer half: receives from a param channel ASSUME the bounds ----------
        // The producer is another method (its sends checked there), so the receive binds a fresh
        // value carrying the contract — and the postcondition proves from the channel type alone.
        [group: 'P242 channel contracts', name: 'consumer receive assumes the element bound', ok: true,
         src: tc("""class C {
                        @Ensures({ result >= 0 })
                        static int consume(@NotNull groovy.concurrent.AsyncChannel<@Min(0L) Integer> ch) {
                            int v = ch.first()
                            return v
                        }
                    }""")],
        // Honesty: with NO constraint on the channel there is no contract to assume — the same
        // postcondition refutes (the channel may deliver any value), instead of skipping.
        [group: 'P242 channel contracts', name: 'unconstrained channel receive refutes a stronger claim', expect: 'Cannot prove postcondition',
         src: tc("""class C {
                        @Ensures({ result >= 0 })
                        static int consume(@NotNull groovy.concurrent.AsyncChannel<Integer> ch) {
                            int v = ch.first()
                            return v
                        }
                    }""")],
        // The awaited receive() spelling binds the same way. (@NotNull on the channel handle itself
        // discharges the ordinary ch-deref obligation — the handle's nullity is separate from the
        // element contract, and take(null) really would NPE.)
        [group: 'P242 channel contracts', name: 'awaited receive() assumes the element bound', ok: true,
         src: tc("""class C {
                        @Ensures({ result >= 1 })
                        static int take(@NotNull groovy.concurrent.AsyncChannel<@Positive Integer> ch) {
                            int v = await ch.receive()
                            return v
                        }
                    }""")],
        // A two-sided contract flows whole: the die channel delivers 1..6.
        [group: 'P242 channel contracts', name: 'range contract assumed at the receive', ok: true,
         src: tc("""class C {
                        @Ensures({ 1 <= result && result <= 6 })
                        static int roll(@NotNull groovy.concurrent.AsyncChannel<@Min(1L) @Max(6L) Integer> ch) {
                            int v = ch.first()
                            return v
                        }
                    }""")],

        // ---------- local pipelines: the same send check inside the Phase 119 rewrite ----------
        // The flattened producer's send carries the assert: with the @Requires it proves and the
        // pipeline value flows as before.
        [group: 'P242 channel contracts', name: 'local pipeline send checked under the precondition', ok: true,
         src: tc("""class C {
                        @Requires({ x > 0 })
                        @Ensures({ result == x + 1 })
                        static int localPipe(int x) {
                            groovy.concurrent.AsyncChannel<@Positive Integer> src = groovy.concurrent.AsyncChannel.create(1)
                            groovy.concurrent.AsyncChannel<Integer> out = src.map { it + 1 }
                            async { src.send(x); src.close() }
                            return out.first()
                        }
                    }""")],
        // Soundness: drop the precondition and the local send's contract assert refutes.
        [group: 'P242 channel contracts', name: 'local pipeline send refutes without the precondition', expect: 'Assertion may not hold',
         src: tc("""class C {
                        @Ensures({ result == x + 1 })
                        static int localPipe(int x) {
                            groovy.concurrent.AsyncChannel<@Positive Integer> src = groovy.concurrent.AsyncChannel.create(1)
                            groovy.concurrent.AsyncChannel<Integer> out = src.map { it + 1 }
                            async { src.send(x); src.close() }
                            return out.first()
                        }
                    }""")],

        // ---------- the compositional capstone, and the fragment boundary ----------
        // Producer and consumer verify SEPARATELY against the shared channel type — the modular
        // rule: no whole-network analysis, the type is the contract.
        [group: 'P242 channel contracts', name: 'producer and consumer compose through the channel type', ok: true,
         src: tc("""class C {
                        static void produce(groovy.concurrent.AsyncChannel<@PositiveOrZero Integer> ch, int x) {
                            ch.send(x * x)
                        }
                        @Ensures({ result >= 0 })
                        static int consume(@NotNull groovy.concurrent.AsyncChannel<@PositiveOrZero Integer> ch) {
                            int v = ch.first()
                            return v
                        }
                    }""")],
        // A never-sent local channel has no element: the read is unconstrained (the runtime BLOCKS
        // forever there). Before this phase the scalar placeholder `def src = 0` PROVED result == 0 —
        // a proof about a value that never exists. Now it honestly refutes.
        [group: 'P242 channel contracts', name: 'a never-sent channel read proves nothing', expect: 'Cannot prove postcondition',
         src: tc("""class C {
                        @Ensures({ result == 0 })
                        static int neverSent() {
                            groovy.concurrent.AsyncChannel<Integer> src = groovy.concurrent.AsyncChannel.create(1)
                            return src.first()
                        }
                    }""")],
        // A constraint outside the numeric-bounds vocabulary is neither checked nor assumed — loudly.
        [group: 'P242 channel contracts', name: 'unsupported element constraint skips loudly', expect: 'Skipped channel-contract constraint',
         src: tc("""class C {
                        @Ensures({ result >= 0 })
                        static int consume(@NotNull groovy.concurrent.AsyncChannel<@Digits(integer = 3, fraction = 0) Integer> ch) {
                            int v = ch.first()
                            return v
                        }
                    }""")],
    ]
}
