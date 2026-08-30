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
 * 'P266 delivered within' — the multi-hop service bound: @DeliveredWithin(value = n, from = 'c', to = 'd')
 * claims that once an element is next in line at every hop, it travels from c to d within n service steps —
 * one per plain stage, the branch count per held fair() ALT. The worst path decides; an unbounded hop
 * refutes with its own reason; queueing behind earlier elements is not claimed.
 */
class G330_p266_delivered_within {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 266 delivered within a bound (slice 26 of the SEQ/PAR ladder): @DeliveredWithin(value = n, from = \'c\', to = \'d\') claims the pipeline\'s END-TO-END SERVICE bound — once an element is next in line at every hop, it travels from c to d within n service steps. The checker builds the hop graph from the stream scan (a plain stage forwards its head in ONE iteration; an ALT hop costs its branch count under a held fair() — Phase 265\'s arithmetic — and is unbounded under priority, a fresh fair(), random(), or the racing select; a guarded reply leaves on its OWN branch\'s reply channel), sums the hops along every simple path from c to d, and certifies n >= the worst path — refuting with the path\'s arithmetic, with an unbounded hop\'s own reason, with \'no path\' (a reply channel of another client is unreachable by construction), or with an unknown channel name. LOUD BOUNDARY: the bound is head-of-line service, not queueing — an element behind a backlog waits its turn first, and the claim does not say otherwise.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static String pipeline(String ann) { """class C {
                        ${ann}
                        static void pipe() {
                            AsyncChannel<Integer> a = AsyncChannel.create(4)
                            AsyncChannel<Integer> b = AsyncChannel.create(4)
                            async {                                              // the generator
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    a.send(i)
                                    i = i + 1
                                }
                            }
                            async {                                              // the squarer
                                int j = 0
                                @Invariant({ j >= 0 })
                                while (true) {
                                    int x = a.first()
                                    b.send(x * x)
                                    j = j + 1
                                }
                            }
                            int m = 0
                            @Invariant({ m >= 0 })
                            while (true) {                                       // the reader
                                int y = b.first()
                                m = m + 1
                            }
                        }
                    }""" }

    static String muxPipe(String ann, String policy) { """class C {
                        ${ann}
                        static void pipe() {
                            AsyncChannel<Integer> a = AsyncChannel.create(4)
                            AsyncChannel<Integer> b = AsyncChannel.create(4)
                            AsyncChannel<Integer> merged = AsyncChannel.create(4)
                            AsyncChannel<Integer> out = AsyncChannel.create(4)
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
                                    b.send(i)
                                    i = i + 1
                                }
                            }
                            async {                                              // the merge
                                ${policy}
                                int j = 0
                                @Invariant({ j >= 0 })
                                while (true) {
                                    ChannelSelect.Result r = await alt.select()
                                    int v = (int) r.value
                                    merged.send(v)
                                    j = j + 1
                                }
                            }
                            async {                                              // the doubler
                                int k = 0
                                @Invariant({ k >= 0 })
                                while (true) {
                                    int x = merged.first()
                                    out.send(x + x)
                                    k = k + 1
                                }
                            }
                            int m = 0
                            @Invariant({ m >= 0 })
                            while (true) {
                                int y = out.first()
                                m = m + 1
                            }
                        }
                    }""" }

    static String fairServer(String ann) { """class C {
                        ${ann}
                        static void fairServer() {
                            AsyncChannel<Integer> reqA = AsyncChannel.create(4)
                            AsyncChannel<Integer> reqB = AsyncChannel.create(4)
                            AsyncChannel<Integer> replyA = AsyncChannel.create(4)
                            AsyncChannel<Integer> replyB = AsyncChannel.create(4)
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    reqA.send(i)
                                    int r = replyA.first()
                                    i = i + 1
                                }
                            }
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    reqB.send(i)
                                    int r = replyB.first()
                                    i = i + 1
                                }
                            }
                            ChannelSelect alt = ChannelSelect.from(reqA, reqB).fair()
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {
                                ChannelSelect.Result r = await alt.select()
                                int q = (int) r.value
                                if (r.index == 0) {
                                    replyA.send(q + 1)
                                }
                                if (r.index == 1) {
                                    replyB.send(q + 1)
                                }
                                j = j + 1
                            }
                        }
                    }""" }

    static final List<Map> CASES = [
        [group: 'P266 delivered within', name: 'one plain stage is one service step: certified', ok: true,
         src: tc(pipeline("@DeliveredWithin(value = 1, from = 'a', to = 'b')"))],
        [group: 'P266 delivered within', name: 'a bound below one hop is refuted with the path', expect: 'totals 1 service step',
         src: tc(pipeline("@DeliveredWithin(value = 0, from = 'a', to = 'b')"))],
        [group: 'P266 delivered within', name: 'a held fair() merge then a stage: two plus one, certified',
         *: (CLAIM_SELECT ? [ok: true] : [expect: 'Cannot find matching method']),
         src: tc(muxPipe("@DeliveredWithin(value = 3, from = 'a', to = 'out')", 'ChannelSelect alt = ChannelSelect.from(a, b).fair()'))],
        [group: 'P266 delivered within', name: 'the same path against a bound of two: the sum is named',
         *: (CLAIM_SELECT ? [expect: 'the claimed 2 is below it'] : [expect: 'Cannot find matching method']),
         src: tc(muxPipe("@DeliveredWithin(value = 2, from = 'a', to = 'out')", 'ChannelSelect alt = ChannelSelect.from(a, b).fair()'))],
        [group: 'P266 delivered within', name: 'a priority merge on the path: no bound, with the hop named', expect: 'no bound',
         src: tc(muxPipe("@DeliveredWithin(value = 3, from = 'a', to = 'out')", 'ChannelSelect alt = ChannelSelect.from(a, b)'))],
        [group: 'P266 delivered within', name: 'the fair server: a request is answered within two service steps',
         *: (CLAIM_SELECT ? [ok: true] : [expect: 'Cannot find matching method']),
         src: tc(fairServer("@DeliveredWithin(value = 2, from = 'reqA', to = 'replyA')"))],
        [group: 'P266 delivered within', name: 'another client\'s reply channel is unreachable by construction',
         *: (CLAIM_SELECT ? [expect: 'no path carries an element'] : [expect: 'Cannot find matching method']),
         src: tc(fairServer("@DeliveredWithin(value = 9, from = 'reqA', to = 'replyB')"))],
        [group: 'P266 delivered within', name: 'an unknown channel name is refused', expect: 'is not a channel',
         src: tc(pipeline("@DeliveredWithin(value = 1, from = 'zzz', to = 'b')"))],
    ]
}
