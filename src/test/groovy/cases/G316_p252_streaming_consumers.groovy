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
 * 'P252 streaming consumers' — the looping consumer: a specified unit-counter loop reading one element per
 * iteration from a streaming channel reads element k of the shadow list, with the block-forever obligation
 * (the element must exist) asserted before it and the producer loop's post-state injected as frame facts.
 * A loop that receives and sends is a stage as a process; a chain of them is the book's network.
 */
class G316_p252_streaming_consumers {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 252 streaming consumers (slice 12 of the SEQ/PAR ladder; the looping consumer): a specified unit-counter loop that receives once per iteration from a streaming channel reads element k of the shadow list (`x.first()` → `x$q[i − a]`), a labelled assert carries the BLOCK-FOREVER obligation (the element must exist — a consumer reading past what the producer sends is refuted: "may block forever"), and the producer loop\'s invariants, sequence facts and ¬guard are injected into the consumer\'s spec as frame facts. A loop that both receives and sends is a stage as a process (its sent expression\'s element relation goes through the receive), so GNumbers → GSquares → GPrint as THREE looping processes proves the printed list element by element for symbolic n. Enablers: a loop after a list-building loop is now summarised (size and contents havoc\'d, invariant assumed); arm locals are alpha-renamed apart (both loops count with `i`). Loud boundary: a receive in a loop without a spec / unit counter, or twice per iteration.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // ---------- GPrint as a counting loop ----------
        // Producer and consumer both count with `i` (renamed apart in the model); the consumer reads
        // exactly n elements, each of which exists — certified, and the count proves.
        [group: 'P252 streaming consumers', name: 'a counting consumer loop reads every element: count == n', ok: true,
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int count(int n) {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(4)
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
                            int seen = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && seen == i })
                            @Decreases({ n - i })
                            while (i < n) {
                                int v = out.first()
                                seen = seen + 1
                                i = i + 1
                            }
                            return seen
                        }
                    }""")],
        // Reading one element more than the producer sends: the (n+1)-th receive blocks forever.
        [group: 'P252 streaming consumers', name: 'a consumer reading past the producer may block forever', expect: 'may block forever',
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n + 1 })
                        static int overRead(int n) {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(4)
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
                            int seen = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n + 1 && seen == i })
                            @Decreases({ n + 1 - i })
                            while (i < n + 1) {
                                int v = out.first()
                                seen = seen + 1
                                i = i + 1
                            }
                            return seen
                        }
                    }""")],
        // The consumer collects: the received elements are the produced ones, in order.
        [group: 'P252 streaming consumers', name: 'a collecting consumer loop: the k-th received is the k-th sent', ok: true,
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.size() == n && Forall.range(0, result.size(), { int k -> result[k] == k }) })
                        static List<Integer> collect(int n) {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(4)
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
        // The last element received.
        [group: 'P252 streaming consumers', name: 'the last element received is n - 1', ok: true,
         src: tc("""class C {
                        @Requires({ n >= 1 })
                        @Ensures({ result == n - 1 })
                        static int last(int n) {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(4)
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
                            int last = -1
                            int j = 0
                            @Invariant({ 0 <= j && j <= n && last == j - 1 })
                            @Decreases({ n - j })
                            while (j < n) {
                                last = out.first()
                                j = j + 1
                            }
                            return last
                        }
                    }""")],

        // ---------- the network: three looping processes ----------
        // GNumbers (a producer loop) → GSquares (a loop that receives AND sends: a stage as a process)
        // → GPrint (a collecting consumer loop): the printed list is the squares, for symbolic n.
        [group: 'P252 streaming consumers', name: 'GNumbers → GSquares → GPrint as three looping processes', ok: true,
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.size() == n && Forall.range(0, result.size(), { int k -> result[k] == k * k }) })
                        static List<Integer> network(int n) {
                            groovy.concurrent.AsyncChannel<Integer> nums = groovy.concurrent.AsyncChannel.create(4)
                            groovy.concurrent.AsyncChannel<Integer> sq = groovy.concurrent.AsyncChannel.create(4)
                            async {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    nums.send(i)
                                    i = i + 1
                                }
                                nums.close()
                            }
                            async {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    int v = nums.first()
                                    sq.send(v * v)
                                    i = i + 1
                                }
                                sq.close()
                            }
                            List<Integer> printed = []
                            int j = 0
                            @Invariant({ printed != null && 0 <= j && j <= n && printed.size() == j && Forall.range(0, printed.size(), { int k -> printed[k] == k * k }) })
                            @Decreases({ n - j })
                            while (j < n) {
                                int s = sq.first()
                                printed.add(s)
                                j = j + 1
                            }
                            return printed
                        }
                    }""")],

        // ---------- the boundary, loudly ----------
        [group: 'P252 streaming consumers', name: 'a receive in an unspecified loop is beyond the model', expect: 'outside a specified unit-counter consumer loop',
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int count(int n) {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(4)
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
                            int seen = 0
                            int j = 0
                            while (j < n) {
                                int v = out.first()
                                seen = seen + 1
                                j = j + 1
                            }
                            return seen
                        }
                    }""")],
    ]
}
