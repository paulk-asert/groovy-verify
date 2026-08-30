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
 * 'P265 served within' — starvation-freedom in the large, as a claim: @ServedWithin(n) says every ready
 * branch of the method's ALT is served within n selects. Certified only where the policy's arithmetic
 * gives the bound (a held fair() over k branches: n >= k); refuted with the policy's own reason otherwise.
 */
class G329_p265_served_within {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 265 served within a bound (slice 25 of the SEQ/PAR ladder): @ServedWithin(n) claims STARVATION-FREEDOM IN THE LARGE — every ready branch of the method\'s ALT is served within n selects, the quantitative half of the "eventually" weak fairness gives (Phases 255/257). Certified silently only where the selection policy\'s arithmetic gives the bound: a HELD fair() select over k branches takes every ready branch within k selects (GROOVY-12320\'s rotation from the last winner), so the claim holds iff n >= k. Refuted with the policy\'s own reason everywhere else: a priority select has no bound at all (a branch behind an always-ready one may wait forever), fair() on a fresh instance keeps no rotation state, random() is fair in expectation only, the racing select before Groovy 6.0.0-beta-4 re-sends losers, a claimed n below k is under the rotation\'s own worst case, and a method with no ALT has nothing to bound. The loop\'s and network\'s liveness are the other rungs\' verdicts on the same compile — this bound is the selection\'s.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static String mux(String ann, String select, String selectCall = 'alt') { """class C {
                        ${ann}
                        static void mux() {
                            AsyncChannel<Integer> a = AsyncChannel.create(4)
                            AsyncChannel<Integer> b = AsyncChannel.create(4)
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
                            ${select}
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {
                                ChannelSelect.Result r = await ${selectCall}.select()
                                int v = (int) r.value
                                j = j + 1
                            }
                        }
                    }""" }

    static final List<Map> CASES = [
        // The bound a held fair() gives: two branches, every ready one taken within two selects.
        [group: 'P265 served within', name: 'a held fair() over two branches: @ServedWithin(2) is certified',
         *: (CLAIM_SELECT ? [ok: true] : [expect: 'Cannot find matching method']),
         src: tc(mux('@ServedWithin(2)', 'ChannelSelect alt = ChannelSelect.from(a, b).fair()'))],
        [group: 'P265 served within', name: 'a claimed bound below the rotation\'s own worst case is refuted',
         *: (CLAIM_SELECT ? [expect: 'the claimed 1 is below it'] : [expect: 'Cannot find matching method']),
         src: tc(mux('@ServedWithin(1)', 'ChannelSelect alt = ChannelSelect.from(a, b).fair()'))],
        [group: 'P265 served within', name: 'a priority select has no bound at all', expect: 'no bound at all',
         *: (CLAIM_SELECT ? [:] : [expect: 'no bound exists']),
         src: tc(mux('@ServedWithin(2)', 'ChannelSelect alt = ChannelSelect.from(a, b)'))],
        [group: 'P265 served within', name: 'random() is fair in expectation only',
         *: (CLAIM_SELECT ? [expect: 'in expectation only'] : [expect: 'Cannot find matching method']),
         src: tc(mux('@ServedWithin(2)', 'ChannelSelect alt = ChannelSelect.from(a, b).random()'))],
        [group: 'P265 served within', name: 'fair() on a fresh instance each iteration keeps no rotation state',
         *: (CLAIM_SELECT ? [expect: 'keeps no rotation state'] : [expect: 'Cannot find matching method']),
         src: tc(mux('@ServedWithin(2)', '', 'ChannelSelect.from(a, b).fair()'))],
        [group: 'P265 served within', name: 'a method with no ALT has nothing to bound', expect: 'no ALT loop',
         src: tc("""class C {
                        @ServedWithin(2)
                        static void none() {
                            AsyncChannel<Integer> a = AsyncChannel.create(4)
                            a.send(1)
                            int x = a.first()
                        }
                    }""")],
    ]
}
