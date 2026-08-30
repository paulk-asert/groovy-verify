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
 * 'P260 sent ghost' — `c.sent`, the elements the enclosing loop's process has sent on channel c so far
 * (priming sends included): the producer's own exact history, named. Where a send's value is loop-written
 * the checker derives no element law (Phase 251's relation needs the counter or a receive alias); with
 * `c.sent` the producer states its own law and a consumer — across a pipeline or a cycle — proves against it.
 */
class G324_p260_sent_ghost {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 260 the sent ghost (slice 20 of the SEQ/PAR ladder): `c.sent` — the list of elements the enclosing loop\'s process has sent on channel c so far, priming sends included — is a verification ghost a producer loop\'s @Invariant may quantify over, the twin of Phase 259\'s `c.taken`. It gives a send whose value is LOOP-WRITTEN — an accumulator, a Fibonacci generator — the element law the checker cannot derive: the producer states it, bounded by the ghost\'s own size so it holds at every point of the body and a reader mid-cycle may rely on it (`Forall.range(0, reply.sent.size(), { int k -> reply.sent[k] == 2 * (k + 1) })`, `c.sent[k] == Fib.of(k)`), and a consumer proves against it across a pipeline (the Fibonacci stream reads `Fib.of(i)`) or a cycle (the accumulating server\'s client proves `r == i + 1` — Phase 258\'s refuted shape, now specified). A wrong law is refuted at the send; naming `sent` on a channel the loop does not produce a stream on is reported. An extension property (verification.ChannelGhosts); the checker rewrites it to the producer\'s exact shadow list; an error if executed.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    // The server's reply is loop-written (acc steps by two — by one it would read as a second counter, Phase 254's rule).
    // The law is bounded by `reply.sent.size()`, not `j`: a reader observes the server at any point of its body,
    // and only a law over the list's own size holds there (a rely assumes a partner's append-stable facts only).
    static String accServer(String inv, String claim = 'assert r == 2 * (i + 1)') { """class C {
                        static void clientServer() {
                            AsyncChannel<Integer> request = AsyncChannel.create(4)
                            AsyncChannel<Integer> reply = AsyncChannel.create(4)
                            async {                                              // the server counts its answers
                                int j = 0
                                int acc = 0
                                @Invariant({ ${inv} })
                                while (true) {
                                    int q = request.first()
                                    acc = acc + 2
                                    reply.send(acc)
                                    j = j + 1
                                }
                            }
                            int i = 0
                            @Invariant({ i >= 0 })
                            while (true) {                                       // the client
                                request.send(i)
                                int r = reply.first()
                                ${claim}
                                i = i + 1
                            }
                        }
                    }""" }

    static final List<Map> CASES = [
        // ---------- a loop-written reply, its law stated by the producer ----------
        [group: 'P260 sent ghost', name: 'the counting server states what it has sent; its client proves each reply (across the cycle)', ok: true,
         src: tc(accServer('j >= 0 && acc == 2 * j && Forall.range(0, reply.sent.size(), { int k -> reply.sent[k] == 2 * (k + 1) })'))],
        [group: 'P260 sent ghost', name: 'a wrong sent law is refuted at the send', expect: 'Cannot prove loop invariant',
         src: tc(accServer('j >= 0 && acc == 2 * j && Forall.range(0, reply.sent.size(), { int k -> reply.sent[k] == 2 * k })', ''))],
        // Without the law the same client claim has nothing to stand on (Phase 258's boundary, kept).
        [group: 'P260 sent ghost', name: 'without the sent law the client claim is refuted', expect: 'Assertion may not hold',
         src: tc(accServer('j >= 0 && acc == 2 * j'))],
        // ---------- a pipeline: the Fibonacci generator ----------
        [group: 'P260 sent ghost', name: 'the Fibonacci generator states its stream; a consumer reads Fib.of(i)', ok: true,
         src: tc("""class C {
                        static void fib() {
                            AsyncChannel<Integer> c = AsyncChannel.create(4)
                            async {                                              // the generator
                                int a = 0
                                int b = 1
                                int i = 0
                                @Invariant({ i >= 0 && a == Fib.of(i) && b == Fib.of(i + 1) && Forall.range(0, c.sent.size(), { int k -> c.sent[k] == Fib.of(k) }) })
                                while (true) {
                                    c.send(a)
                                    int t = a + b
                                    a = b
                                    b = t
                                    i = i + 1
                                }
                            }
                            int n = 0
                            @Invariant({ n >= 0 })
                            while (true) {                                       // the reader
                                int x = c.first()
                                assert x == Fib.of(n)
                                n = n + 1
                            }
                        }
                    }""")],
        // ---------- misuse, named ----------
        [group: 'P260 sent ghost', name: 'sent on a channel the loop receives from: names nothing', expect: 'names nothing here',
         src: tc(accServer('j >= 0 && acc == 2 * j && Forall.range(0, request.sent.size(), { int k -> request.sent[k] == k })', ''))],
        [group: 'P260 sent ghost', name: 'sent in a loop that only reads the stream: names nothing', expect: 'names nothing here',
         src: tc("""class C {
                        static void reader() {
                            AsyncChannel<Integer> c = AsyncChannel.create(4)
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    c.send(i)
                                    i = i + 1
                                }
                            }
                            int n = 0
                            @Invariant({ n >= 0 && c.sent.size() == n })
                            while (true) {
                                int x = c.first()
                                n = n + 1
                            }
                        }
                    }""")],
    ]
}
