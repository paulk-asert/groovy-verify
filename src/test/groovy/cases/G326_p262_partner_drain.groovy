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
 * 'P262 drain of a partner stream' — the shape that ENDS cleanly: a bounded client that closes its request
 * channel after its loop, and a server that drains it — `for (q in request) { reply.send(q + 1) }` — until
 * the close. The drain is rebuilt as the counter loop the cycle model reads (`while (request$d < n)`), so
 * the drain's reads are partner reads and its replies a stream of exactly n elements: the client's claims
 * prove, its reads lie below that total, and the drain's termination is the client's close.
 */
class G326_p262_partner_drain {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 262 the drain of a partner stream (slice 22 of the SEQ/PAR ladder): a server that DRAINS its bounded client — `for (q in request) { reply.send(q + 1) }` in one process, `while (i < n) { request.send(i); … reply.first() … }; request.close()` in another — is the client–server cycle that ends cleanly, and Phase 261 left it as the next rung. The drain of a cycle partner\'s stream is rebuilt (arms rebuilt, never mutated) as the counter loop the cycle model reads directly — `int request$d = 0; while (request$d < n) { int q = request.first(); …; request$d = request$d + 1 }` with a synthesized invariant and variant, `while (true)` for a non-terminating producer — provided the producer is a unit-counter loop with a static total that closes the channel after its loop, and the drain replies on a channel the producer reads (the cycle). Then the drain\'s reads are partner reads (rely views, taken-ghost) whose read-below-total obligation the guard meets, its replies a stream of exactly the total, and the client\'s request–reply claim proves with its reads below that total. Without the close, or over a producer of another shape, the drain is left to Phase 251\'s model and its loud skip.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static String draining(String close, String claim = 'assert r == i + 1', String clientGuard = 'i < n', String clientSpec = '@Invariant({ 0 <= i && i <= n })\n                            @Decreases({ n - i })') { """class C {
                        @Requires({ n >= 0 })
                        static void clientServer(int n) {
                            AsyncChannel<Integer> request = AsyncChannel.create(4)
                            AsyncChannel<Integer> reply = AsyncChannel.create(4)
                            async {                                              // the server drains until the close
                                for (int q in request) {
                                    reply.send(q + 1)
                                }
                            }
                            int i = 0
                            ${clientSpec}
                            while (${clientGuard}) {                             // the client
                                request.send(i)
                                int r = reply.first()
                                ${claim}
                                i = i + 1
                            }
                            ${close}
                        }
                    }""" }

    static final List<Map> CASES = [
        [group: 'P262 drain of a partner stream', name: 'a bounded client and a draining server: each reply proves, the drain ends at the close', ok: true,
         src: tc(draining('request.close()'))],
        [group: 'P262 drain of a partner stream', name: 'the same with a wrong reply claim: refuted', expect: 'Assertion may not hold',
         src: tc(draining('request.close()', 'assert r == i + 2'))],
        [group: 'P262 drain of a partner stream', name: 'the drain in the main body, the client in the arm: the same cycle', ok: true,
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        static void clientServer(int n) {
                            AsyncChannel<Integer> request = AsyncChannel.create(4)
                            AsyncChannel<Integer> reply = AsyncChannel.create(4)
                            async {                                              // the client
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    request.send(i)
                                    int r = reply.first()
                                    assert r == i + 1
                                    i = i + 1
                                }
                                request.close()
                            }
                            for (int q in request) {                             // the server drains until the close
                                reply.send(q + 1)
                            }
                        }
                    }""")],
        // A forever client is never closed: the drain never finishes BY DESIGN — a non-terminating drain, said as
        // such (not a deadlock), the replies still proved.
        [group: 'P262 drain of a partner stream', name: 'a forever client and a draining server: a non-terminating drain, the replies still prove', expect: 'non-terminating drain', refute: 'Assertion may not hold',
         src: tc(draining('', 'assert r == i + 1', 'true', '@Invariant({ i >= 0 })'))],
        // ---------- the loud boundary ----------
        [group: 'P262 drain of a partner stream', name: 'without the close the drain is not rebuilt: Phase 251 skips it loudly', expect: 'Skipped channel verification',
         src: tc(draining(''))],
    ]
}
