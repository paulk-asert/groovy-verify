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
 * 'P259 taken ghost' — `c.taken`, the elements the enclosing loop has taken from channel c so far, as a
 * list a loop @Invariant can quantify over. It is Phase 258's taken-ghost given a name: the fact a
 * token-ring closed form needs and no local carries. A Groovy extension property (verification.ChannelGhosts)
 * so the spec type-checks; rewritten to the ghost by the checker; an error if executed.
 */
class G323_p259_taken_ghost {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 259 the taken ghost (slice 19 of the SEQ/PAR ladder): `c.taken` — the list of elements the enclosing loop has taken from channel c so far (a stream it receives from a cycle partner, or a branch of its ALT) — is a verification ghost a loop @Invariant may quantify over (`Forall.range(0, i, { int k -> c.taken[k] == 2 * k + 1 })`, or the range sugar `(0..<i).every { … }`). It gives the rely/guarantee model of Phase 258 the one fact a closed form needs and no local carries: the primed two-process cycle proves `x == 2 * i + 1`, the three-process token ring proves `x == 3 * i + 2`, the fair server\'s client proves the history of what it was answered, and a wrong closed form is refuted at its base case. It is an extension property (verification.ChannelGhosts) so the spec type-checks, is rewritten to the ghost by the checker, and is an error if executed; naming it where the loop takes nothing from the channel is reported.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static String primed(String inv, String claim = 'assert x == 2 * i + 1') { """class C {
                        static void primed() {
                            AsyncChannel<Integer> aToB = AsyncChannel.create(4)
                            AsyncChannel<Integer> bToA = AsyncChannel.create(4)
                            async {                                              // A: one message ahead
                                aToB.send(0)
                                int i = 0
                                @Invariant({ ${inv} })
                                while (true) {
                                    int x = bToA.first()
                                    ${claim}
                                    aToB.send(x + 1)
                                    i = i + 1
                                }
                            }
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {                                       // B
                                int y = aToB.first()
                                bToA.send(y + 1)
                                j = j + 1
                            }
                        }
                    }""" }

    static final List<Map> CASES = [
        // ---------- the primed cycle's closed form: what A reads is 2i + 1 ----------
        [group: 'P259 taken ghost', name: 'the primed cycle: what A has taken is 2k + 1, so what it reads is 2i + 1 (proved)', ok: true,
         src: tc(primed('i >= 0 && Forall.range(0, i, { int k -> bToA.taken[k] == 2 * k + 1 })'))],
        [group: 'P259 taken ghost', name: 'the same closed form in range sugar: (0..<i).every', ok: true,
         src: tc(primed('i >= 0 && (0..<i).every { int k -> bToA.taken[k] == 2 * k + 1 }'))],
        // The wrong closed form is refuted at its base case: the priming element is 0, so the first reply is 1, not 0.
        [group: 'P259 taken ghost', name: 'a wrong closed form is refuted at its base case', expect: 'Cannot prove loop invariant',
         src: tc(primed('i >= 0 && Forall.range(0, i, { int k -> bToA.taken[k] == 2 * k })', ''))],
        // ---------- the three-process token ring ----------
        [group: 'P259 taken ghost', name: 'the token ring: what A reads is 3i + 2 (proved through B and C)', ok: true,
         src: tc("""class C {
                        static void ring() {
                            AsyncChannel<Integer> ab = AsyncChannel.create(4)
                            AsyncChannel<Integer> bc = AsyncChannel.create(4)
                            AsyncChannel<Integer> ca = AsyncChannel.create(4)
                            async {                                              // B
                                int j = 0
                                @Invariant({ j >= 0 })
                                while (true) {
                                    int y = ab.first()
                                    bc.send(y + 1)
                                    j = j + 1
                                }
                            }
                            async {                                              // C
                                int m = 0
                                @Invariant({ m >= 0 })
                                while (true) {
                                    int z = bc.first()
                                    ca.send(z + 1)
                                    m = m + 1
                                }
                            }
                            ab.send(0)                                           // A: the token goes round
                            int i = 0
                            @Invariant({ i >= 0 && Forall.range(0, i, { int k -> ca.taken[k] == 3 * k + 2 }) })
                            while (true) {
                                int x = ca.first()
                                assert x == 3 * i + 2
                                ab.send(x + 1)
                                i = i + 1
                            }
                        }
                    }""")],
        // ---------- the fair server's client: the history of what it was answered ----------
        [group: 'P259 taken ghost', name: 'the fair server: a client proves the history of its replies (claim-based select)',
         *: (CLAIM_SELECT ? [ok: true] : [expect: 'Cannot find matching method']),
         src: tc("""class C {
                        static void fairServer() {
                            AsyncChannel<Integer> reqA = AsyncChannel.create(4)
                            AsyncChannel<Integer> reqB = AsyncChannel.create(4)
                            AsyncChannel<Integer> replyA = AsyncChannel.create(4)
                            AsyncChannel<Integer> replyB = AsyncChannel.create(4)
                            async {                                              // client A
                                int i = 0
                                @Invariant({ i >= 0 && Forall.range(0, i, { int k -> replyA.taken[k] == k + 1 }) })
                                while (true) {
                                    reqA.send(i)
                                    int r = replyA.first()
                                    i = i + 1
                                }
                            }
                            async {                                              // client B
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
                    }""")],
        // ---------- misuse, named ----------
        [group: 'P259 taken ghost', name: 'taken on a channel the loop sends to, not takes from: names nothing', expect: 'names nothing here',
         src: tc(primed('i >= 0 && Forall.range(0, i, { int k -> aToB.taken[k] == 2 * k + 1 })'))],
        [group: 'P259 taken ghost', name: 'taken in a loop that receives from no stream: names nothing', expect: 'names nothing here',
         src: tc("""class C {
                        static void producer() {
                            AsyncChannel<Integer> c = AsyncChannel.create(4)
                            int i = 0
                            @Invariant({ i >= 0 && c.taken.size() == 0 })
                            while (true) {
                                c.send(i)
                                i = i + 1
                            }
                        }
                    }""")],
    ]
}
