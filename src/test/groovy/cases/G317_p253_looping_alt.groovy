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
 * 'P253 looping ALT' — the multiplexer: a specified unit-counter loop whose body takes one element per
 * iteration from whichever of its streaming inputs has one, via ChannelSelect. Each branch has a ghost
 * cursor; the choice ranges over the branches with an element left; the cursors together count the
 * iterations; and "no branch has an element left" is the block-forever obligation.
 */
class G317_p253_looping_alt {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 253 the looping ALT (slice 13 of the SEQ/PAR ladder): a specified unit-counter loop with one `Result r = await ChannelSelect.from(a, b).select()` per iteration over streaming inputs is the multiplexer. Each branch gets a ghost cursor (`a$c`), the per-iteration choice ranges over the branches with an element left (`$channelSelect.ready`), the value is the element at the chosen cursor (`valueAt`), the chosen cursor steps, and the injected invariant `0 <= a$c <= |a| && … && a$c + b$c == i − a₀` ties the cursors to the iterations — so the merged count PROVES (`result.size() == na + nb`), a forwarded element contract proves through the ALT, a multiplexer reading past both producers is refuted ("the ALT … may block forever — no branch may have an element left"), and an ORDER claim is honestly refuted (the interleaving is nondeterministic). Loud boundary: an ALT in a loop without a spec / unit counter, two ALTs per iteration, or a branch also received one at a time in the same loop.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final String PRODUCERS = """
                            AsyncChannel<Integer> a = AsyncChannel.create(4)
                            AsyncChannel<Integer> b = AsyncChannel.create(4)
                            async {
                                int i = 0
                                @Invariant({ 0 <= i && i <= na })
                                @Decreases({ na - i })
                                while (i < na) {
                                    a.send(i)
                                    i = i + 1
                                }
                                a.close()
                            }
                            async {
                                int i = 0
                                @Invariant({ 0 <= i && i <= nb })
                                @Decreases({ nb - i })
                                while (i < nb) {
                                    b.send(i + 100)
                                    i = i + 1
                                }
                                b.close()
                            }"""

    /** The same two producers with constant payloads (0s on a, 100s on b). */
    static final String PRODUCERS_CONST = PRODUCERS.replace('a.send(i)', 'a.send(0)').replace('b.send(i + 100)', 'b.send(100)')

    static final List<Map> CASES = [

        // ---------- the multiplexer ----------
        // Two producers, one merging loop: whichever input has an element is taken. The merged count is
        // the sum of the inputs' counts — proved for symbolic na, nb.
        [group: 'P253 looping ALT', name: 'the multiplexer merges every element: count == na + nb', ok: true,
         src: tc("""class C {
                        @Requires({ na >= 0 && nb >= 0 })
                        @Ensures({ result.size() == na + nb })
                        static List<Integer> merge(int na, int nb) {${PRODUCERS}
                            AsyncChannel<Integer> out = AsyncChannel.create(8)
                            int j = 0
                            @Invariant({ 0 <= j && j <= na + nb })
                            @Decreases({ na + nb - j })
                            while (j < na + nb) {
                                ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
                                int v = (int) r.value
                                out.send(v)
                                j = j + 1
                            }
                            out.close()
                            return out.toList()
                        }
                    }""")],
        // One iteration too many: at that point no branch has an element left — the ALT blocks forever.
        [group: 'P253 looping ALT', name: 'a multiplexer reading past both producers may block forever', expect: 'no branch may have an element left',
         src: tc("""class C {
                        @Requires({ na >= 0 && nb >= 0 })
                        @Ensures({ result.size() == na + nb + 1 })
                        static List<Integer> merge(int na, int nb) {${PRODUCERS}
                            AsyncChannel<Integer> out = AsyncChannel.create(8)
                            int j = 0
                            @Invariant({ 0 <= j && j <= na + nb + 1 })
                            @Decreases({ na + nb + 1 - j })
                            while (j < na + nb + 1) {
                                ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
                                int v = (int) r.value
                                out.send(v)
                                j = j + 1
                            }
                            out.close()
                            return out.toList()
                        }
                    }""")],
        // The element contract on the merged output holds because every input element satisfies it —
        // through the ALT's choice, whichever branch it takes.
        [group: 'P253 looping ALT', name: 'a forwarded element contract holds through the ALT', ok: true,
         src: tc("""class C {
                        @Requires({ na >= 0 && nb >= 0 })
                        @Ensures({ result.size() == na + nb })
                        static List<Integer> merge(int na, int nb) {${PRODUCERS}
                            AsyncChannel<@PositiveOrZero Integer> out = AsyncChannel.create(8)
                            int j = 0
                            @Invariant({ 0 <= j && j <= na + nb })
                            @Decreases({ na + nb - j })
                            while (j < na + nb) {
                                ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
                                int v = (int) r.value
                                out.send(v)
                                j = j + 1
                            }
                            out.close()
                            return out.toList()
                        }
                    }""")],
        // (Constant payloads: the refutation is a SAT search under the branches' element relations, and a
        // relation `a$q[k] == k` makes that model-building heavy enough to time out on a slow CI runner;
        // `a$q[k] == 0` carries the same point at a fraction of the cost.)
        [group: 'P253 looping ALT', name: 'a forwarded element contract an input violates is refuted', expect: 'Assertion may not hold',
         src: tc("""class C {
                        @Requires({ na >= 1 && nb >= 0 })
                        @Ensures({ result.size() == na + nb })
                        static List<Integer> merge(int na, int nb) {${PRODUCERS_CONST}
                            AsyncChannel<@Positive Integer> out = AsyncChannel.create(8)
                            int j = 0
                            @Invariant({ 0 <= j && j <= na + nb })
                            @Decreases({ na + nb - j })
                            while (j < na + nb) {
                                ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
                                int v = (int) r.value
                                out.send(v)
                                j = j + 1
                            }
                            out.close()
                            return out.toList()
                        }
                    }""")],
        // The interleaving is nondeterministic: an ORDER claim is honestly refuted.
        [group: 'P253 looping ALT', name: 'the merge order is nondeterministic: an order claim is refuted', expect: 'Cannot prove postcondition',
         src: tc("""class C {
                        @Requires({ na >= 1 && nb >= 1 })
                        @Ensures({ result.size() == na + nb && result[0] == 0 })
                        static List<Integer> merge(int na, int nb) {${PRODUCERS_CONST}
                            AsyncChannel<Integer> out = AsyncChannel.create(8)
                            int j = 0
                            @Invariant({ 0 <= j && j <= na + nb })
                            @Decreases({ na + nb - j })
                            while (j < na + nb) {
                                ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
                                int v = (int) r.value
                                out.send(v)
                                j = j + 1
                            }
                            out.close()
                            return out.toList()
                        }
                    }""")],

        // ---------- the boundary, loudly ----------
        [group: 'P253 looping ALT', name: 'an ALT in an unspecified loop is beyond the model', expect: 'not one-shot',
         src: tc("""class C {
                        @Requires({ na >= 0 && nb >= 0 })
                        @Ensures({ result.size() == na + nb })
                        static List<Integer> merge(int na, int nb) {${PRODUCERS}
                            AsyncChannel<Integer> out = AsyncChannel.create(8)
                            int j = 0
                            while (j < na + nb) {
                                ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
                                int v = (int) r.value
                                out.send(v)
                                j = j + 1
                            }
                            out.close()
                            return out.toList()
                        }
                    }""")],
    ]
}
