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
 * 'P254 non-terminating processes' — the safety half of `while (true)`: a process that never stops is
 * certified for what it preserves (its invariant, its send contracts, what its consumers receive), with
 * termination not claimed and liveness — that a receive from it is eventually served — reported as an
 * assumption, loudly. In the flattened model an infinite loop gets a FREE guard, so nothing that follows
 * it is reasoned about vacuously.
 */
class G318_p254_forever {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 254 non-terminating processes (slice 14 of the SEQ/PAR ladder; the safety half of while (true)): a `while (true)` producer, consumer or multiplexer loop with an @Invariant (no @Decreases — none is possible) is certified for SAFETY: its invariant is preserved per iteration, its send-side channel contract is checked per iteration, and its consumers\' received values carry its element relation (the infinite GNumbers → GSquares → GPrint network proves every printed value is a square; a broken stage refutes). Termination is not claimed, and the element-exists obligation of a receive served by an infinite producer is ASSUMED, with a loud network note ("… is served by a non-terminating producer — that it is eventually served is a liveness property, not claimed"). Soundness: in the flattened model an infinite loop gets a free guard, so the other processes are reasoned about under its invariant alone, never under the vacuous ¬true (a false claim after an infinite producer is refuted, not proved); an infinite consumer of a FINITE producer is still "may block forever" — the classic hang.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final String GEN = """
                            val out = AsyncChannel.<Integer>create(4)
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    out.send(i)
                                    i = i + 1
                                }
                            }"""

    static final List<Map> CASES = [

        // ---------- the infinite generator, consumed finitely ----------
        // GNumbers as the book writes it. A finite consumer's received values prove; that each receive is
        // served is liveness — certified under weak fairness since Phase 255 (the generator has no
        // receives of its own, so nothing it waits on can wait on it).
        [group: 'P254 non-terminating processes', name: 'an infinite generator feeds a finite consumer: the received values prove', ok: true,
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.size() == n && Forall.range(0, result.size(), { int k -> result[k] == k }) })
                        static List<Integer> take(int n) {${GEN}
                            List<Integer> printed = []
                            int j = 0
                            @Invariant({ printed != null && 0 <= j && j <= n && printed.size() == j && Forall.range(0, printed.size(), { int k -> printed[k] == k }) })
                            @Decreases({ n - j })
                            while (j < n) {
                                int v = out.first()
                                printed.add(v)
                                j = j + 1
                            }
                            return printed
                        }
                    }""")],
        // A false claim after an infinite producer is REFUTED, not vacuously proved — the free guard.
        [group: 'P254 non-terminating processes', name: 'no vacuity after an infinite producer: a false claim is refuted', expect: 'Cannot prove postcondition',
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n + 1 })
                        static int count(int n) {${GEN}
                            int j = 0
                            @Invariant({ 0 <= j && j <= n })
                            @Decreases({ n - j })
                            while (j < n) {
                                int v = out.first()
                                j = j + 1
                            }
                            return j
                        }
                    }""")],

        // ---------- the network as the book writes it: every process runs forever ----------
        // GNumbers → GSquares → GPrint, all `while (true)`. Nothing terminates and nothing is claimed to;
        // what IS certified is that every value GPrint accumulates is a square — GPrint's own invariant,
        // preserved per iteration through GSquares' and GNumbers' relations — and, since Phase 255, that
        // the pipeline is live under weak fairness (no receive waits on itself within an iteration).
        [group: 'P254 non-terminating processes', name: 'GNumbers → GSquares → GPrint, all forever: safety proved, liveness certified under weak fairness', ok: true,
         src: tc("""class C {
                        static void network() {
                            val nums = AsyncChannel.<Integer>create(4)
                            val sq = AsyncChannel.<Integer>create(4)
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    nums.send(i)
                                    i = i + 1
                                }
                            }
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    int v = nums.first()
                                    sq.send(v * v)
                                    i = i + 1
                                }
                            }
                            List<Integer> printed = []
                            int j = 0
                            @Invariant({ printed != null && j >= 0 && printed.size() == j && Forall.range(0, printed.size(), { int k -> printed[k] == k * k }) })
                            while (true) {
                                int s = sq.first()
                                printed.add(s)
                                j = j + 1
                            }
                        }
                    }""")],
        [group: 'P254 non-terminating processes', name: 'a broken stage in the forever network refutes GPrint\'s invariant', expect: 'Cannot prove loop invariant',
         src: tc("""class C {
                        static void network() {
                            val nums = AsyncChannel.<Integer>create(4)
                            val sq = AsyncChannel.<Integer>create(4)
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    nums.send(i)
                                    i = i + 1
                                }
                            }
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    int v = nums.first()
                                    sq.send(v * v + 1)
                                    i = i + 1
                                }
                            }
                            List<Integer> printed = []
                            int j = 0
                            @Invariant({ printed != null && j >= 0 && printed.size() == j && Forall.range(0, printed.size(), { int k -> printed[k] == k * k }) })
                            while (true) {
                                int s = sq.first()
                                printed.add(s)
                                j = j + 1
                            }
                        }
                    }""")],

        // ---------- the send contract of an infinite producer ----------
        [group: 'P254 non-terminating processes', name: 'an infinite producer\'s send contract holds under its invariant', ok: true,
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int count(int n) {
                            AsyncChannel<@PositiveOrZero Integer> out = AsyncChannel.create(4)
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    out.send(i)
                                    i = i + 1
                                }
                            }
                            int j = 0
                            @Invariant({ 0 <= j && j <= n })
                            @Decreases({ n - j })
                            while (j < n) {
                                int v = out.first()
                                j = j + 1
                            }
                            return j
                        }
                    }""")],
        [group: 'P254 non-terminating processes', name: 'an infinite producer\'s send contract is refuted at the first iteration', expect: 'Assertion may not hold',
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int count(int n) {
                            AsyncChannel<@PositiveOrZero Integer> out = AsyncChannel.create(4)
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    out.send(i - 1)
                                    i = i + 1
                                }
                            }
                            int j = 0
                            @Invariant({ 0 <= j && j <= n })
                            @Decreases({ n - j })
                            while (j < n) {
                                int v = out.first()
                                j = j + 1
                            }
                            return j
                        }
                    }""")],

        // ---------- the classic hang: a consumer that never stops, a producer that does ----------
        [group: 'P254 non-terminating processes', name: 'an infinite consumer of a finite producer may block forever', expect: 'may block forever',
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        static void printer(int n) {
                            val out = AsyncChannel.<Integer>create(4)
                            async {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    out.send(i)
                                    i = i + 1
                                }
                                out.close()
                            }
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {
                                int v = out.first()
                                j = j + 1
                            }
                        }
                    }""")],

        // ---------- the forever multiplexer ----------
        // The contract forwards; but under ChannelSelect's priority the second generator may starve (Phase 256
        // names it: 'a' is always ready and precedes 'b').
        [group: 'P254 non-terminating processes', name: 'a forever multiplexer over two infinite generators: the contract forwards, the second branch may starve', expect: 'may starve', refute: 'Assertion may not hold',
         src: tc("""class C {
                        static void mux() {
                            val a = AsyncChannel.<Integer>create(4)
                            val b = AsyncChannel.<Integer>create(4)
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    a.send(i)
                                    i = i + 1
                                }
                            }
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    b.send(i + 100)
                                    i = i + 1
                                }
                            }
                            AsyncChannel<@PositiveOrZero Integer> merged = AsyncChannel.create(8)
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {
                                ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
                                int v = (int) r.value
                                merged.send(v)
                                j = j + 1
                            }
                        }
                    }""")],
    ]
}
