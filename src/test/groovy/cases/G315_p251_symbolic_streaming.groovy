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
 * 'P251 symbolic streaming' — the value half of the streaming frontier: a channel whose one send is the
 * send statement of a specified unit-counter loop is modelled as the LIST that loop builds, with the
 * sequence facts (size == counter − entry; the k-th element's value) injected into the loop's spec — so
 * a symbolic-count generator's drained list proves, with the user writing only the loop's own
 * @Invariant / @Decreases and never naming the shadow list.
 */
class G315_p251_symbolic_streaming {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 251 symbolic streaming (slice 11 of the SEQ/PAR ladder; the value half of the streaming frontier): a channel whose only send is the send statement of a unit-counter loop carrying @Invariant/@Decreases is modelled as the list that loop builds (send → append; a map stage appends its transform in lockstep; toList() reads the list; close() is the marker drains are scheduled behind). The sequence facts are INJECTED into the loop spec — `size == counter − entry` and, when the sent expression is a function of the counter and loop constants, `Forall.range(0, size, { k -> q[k] == E[i := entry + k] })` — so GNumbers(n) with symbolic n PROVES `result.size() == n` and `result[k] == k` (through GSquares: `k * k`), a wrong size refutes, a parameter start (int i = lo) proves `n - lo`, and the send-side channel contract is checked per iteration by the loop VC. Loud boundaries: a one-at-a-time receive on a streaming channel, a producer loop without a spec, a second send, a non-unit counter, a for-in drain (the loop engine\'s nested-loop skip — toList() is the drained-value spelling).'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // ---------- GNumbers(n): the drained list proves ----------
        [group: 'P251 symbolic streaming', name: 'GNumbers(n) drained: size == n', ok: true,
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.size() == n })
                        static List<Integer> numbers(int n) {
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
                            return out.toList()
                        }
                    }""")],
        [group: 'P251 symbolic streaming', name: 'GNumbers(n) drained: the k-th element is k', ok: true,
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.size() == n && Forall.range(0, result.size(), { int k -> result[k] == k }) })
                        static List<Integer> numbers(int n) {
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
                            return out.toList()
                        }
                    }""")],
        // GNumbers → GSquares: the map stage appends its transform in lockstep — the k-th square is k².
        [group: 'P251 symbolic streaming', name: 'GNumbers(n) → GSquares drained: the k-th element is k squared', ok: true,
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.size() == n && Forall.range(0, result.size(), { int k -> result[k] == k * k }) })
                        static List<Integer> squares(int n) {
                            groovy.concurrent.AsyncChannel<Integer> nums = groovy.concurrent.AsyncChannel.create(4)
                            groovy.concurrent.AsyncChannel<Integer> sq = nums.map { it * it }
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
                            return sq.toList()
                        }
                    }""")],
        [group: 'P251 symbolic streaming', name: 'a C-style producer in the body', ok: true,
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.size() == n && Forall.range(0, result.size(), { int k -> result[k] == 2 * k }) })
                        static List<Integer> evens(int n) {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(4)
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            for (int i = 0; i < n; i++) {
                                out.send(2 * i)
                            }
                            out.close()
                            return out.toList()
                        }
                    }""")],
        [group: 'P251 symbolic streaming', name: 'a parameter start: size == n - lo', ok: true,
         src: tc("""class C {
                        @Requires({ 0 <= lo && lo <= n })
                        @Ensures({ result.size() == n - lo && Forall.range(0, result.size(), { int k -> result[k] == lo + k }) })
                        static List<Integer> range(int lo, int n) {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(4)
                            async {
                                int i = lo
                                @Invariant({ lo <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    out.send(i)
                                    i = i + 1
                                }
                                out.close()
                            }
                            return out.toList()
                        }
                    }""")],
        [group: 'P251 symbolic streaming', name: 'a wrong drained size is refuted', expect: 'Cannot prove postcondition',
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.size() == n + 1 })
                        static List<Integer> numbers(int n) {
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
                            return out.toList()
                        }
                    }""")],

        // ---------- the channel contract, checked per iteration ----------
        [group: 'P251 symbolic streaming', name: 'the element contract holds under the loop invariant', ok: true,
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.size() == n })
                        static List<Integer> numbers(int n) {
                            groovy.concurrent.AsyncChannel<@PositiveOrZero Integer> out = groovy.concurrent.AsyncChannel.create(4)
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
                            return out.toList()
                        }
                    }""")],
        [group: 'P251 symbolic streaming', name: 'the element contract is refuted at the first iteration', expect: 'Assertion may not hold',
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.size() == n })
                        static List<Integer> numbers(int n) {
                            groovy.concurrent.AsyncChannel<@PositiveOrZero Integer> out = groovy.concurrent.AsyncChannel.create(4)
                            async {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    out.send(i - 1)
                                    i = i + 1
                                }
                                out.close()
                            }
                            return out.toList()
                        }
                    }""")],

        // ---------- the boundaries, loudly ----------
        [group: 'P251 symbolic streaming', name: 'a one-at-a-time receive on a stream is beyond the model', expect: 'one element at a time',
         src: tc("""class C {
                        @Requires({ n >= 1 })
                        @Ensures({ result == 0 })
                        static int firstOf(int n) {
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
                            return out.first()
                        }
                    }""")],
        [group: 'P251 symbolic streaming', name: 'a producer loop without a spec is beyond the model', expect: 'without an @Invariant',
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.size() == n })
                        static List<Integer> numbers(int n) {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(4)
                            async {
                                int i = 0
                                while (i < n) {
                                    out.send(i)
                                    i = i + 1
                                }
                                out.close()
                            }
                            return out.toList()
                        }
                    }""")],
        [group: 'P251 symbolic streaming', name: 'a non-unit counter is beyond the model', expect: 'no unit counter',
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.size() == n })
                        static List<Integer> numbers(int n) {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(4)
                            async {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    out.send(i)
                                    i = i + 2
                                }
                                out.close()
                            }
                            return out.toList()
                        }
                    }""")],
        // The accumulating for-in drain: the loop engine's own boundary (a loop after a list-building
        // loop), named — toList() is the drained-value spelling.
        [group: 'P251 symbolic streaming', name: 'an accumulating for-in drain of a stream is the loop engine\'s skip', expect: 'Skipped loop verification',
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
                            for (v in out) {
                                seen = seen + 1
                            }
                            return seen
                        }
                    }""")],
    ]
}
