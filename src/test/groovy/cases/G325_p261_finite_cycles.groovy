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
 * 'P261 finite cycles' — a cycle with a TERMINATING member. The rely assumes a partner's append-stable facts,
 * so a partner's exit is not its business; what a finite partner changes is EXISTENCE: element k of its
 * stream exists eventually iff k < its total, an obligation the reader must discharge ("may block forever"
 * otherwise, with the total named) — while "the partner gets there" stays the liveness assumption.
 */
class G325_p261_finite_cycles {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 261 finite cycles (slice 21 of the SEQ/PAR ladder): a cycle of loops with a TERMINATING member — a client and a server both bounded, a bounded fair server — and a forever server outliving its bounded client, whose last read is a TRUE block (refuted, the client\'s total named). The rely assumes a partner\'s append-stable facts only (Phase 260), so a partner\'s exit fact is not needed; what a finite partner changes is EXISTENCE. A finite producer\'s total is read off its guard (`counter < bound`, `<=` adds one, priming sends added) and at a read from it the reader must show it reads BELOW that total — `k < m` — or the receive "may block forever", the total named; the ALT of a bounded server over bounded clients must select below their totals in all. The total is also a stable upper bound a rely may assume. A finite partner whose count is not static (a guard of another shape) is skipped loudly. Request–reply claims prove as before; a mismatch (a client asking more than its server answers, a server waiting for more than its clients ask) is refuted at the read that would block.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static String pair(String requires, String serverGuard, String serverInv) { """class C {
                        ${requires}
                        static void clientServer(int n, int m) {
                            AsyncChannel<Integer> request = AsyncChannel.create(4)
                            AsyncChannel<Integer> reply = AsyncChannel.create(4)
                            async {                                              // the server
                                int j = 0
                                @Invariant({ ${serverInv} })
                                while (${serverGuard}) {
                                    int q = request.first()
                                    reply.send(q + 1)
                                    j = j + 1
                                }
                            }
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) {                                      // the client
                                request.send(i)
                                int r = reply.first()
                                assert r == i + 1
                                i = i + 1
                            }
                        }
                    }""" }

    static final List<Map> CASES = [
        // A forever server of a bounded client is a TRUE finding: after the n-th request it waits forever for one
        // more — the read that blocks is named, with the client's total. (A server that drains until the client
        // closes is the shape for that — the drain of a partner stream is a rung not built.)
        [group: 'P261 finite cycles', name: 'a forever server outlives its bounded client: its next read blocks forever (refuted, the total named)', expect: 'sends n - 0 element(s) in all',
         src: tc(pair('@Requires({ n >= 0 })', 'true', 'j >= 0'))],
        [group: 'P261 finite cycles', name: 'a bounded client and a bounded server, matched (n == m): both sides prove', ok: true,
         src: tc(pair('@Requires({ n == m && n >= 0 })', 'j < m', '0 <= j && j <= m'))],
        [group: 'P261 finite cycles', name: 'unmatched bounds: the read that would block forever is refuted, the total named', expect: 'may block forever',
         src: tc(pair('', 'j < m', '0 <= j && j <= m'))],
        // The @Requires hint is for an assert the AUTHOR wrote, whose text pastes into a contract; a
        // synthesized block-forever obligation prints prose ("the receive on 'request' … may block
        // forever — …"), so the nudge is withheld rather than suggesting an English sentence as a contract.
        [group: 'P261 finite cycles', name: 'a server bounded above its clients waits forever for a request: refuted', expect: 'may block forever',
         refute: 'declare it as @Requires',
         src: tc(pair('@Requires({ 0 <= n && n < m })', 'j < m', '0 <= j && j <= m'))],
        // ---------- a bounded fair server ----------
        [group: 'P261 finite cycles', name: 'a bounded fair server over two bounded clients: every reply proves (claim-based select)',
         *: (CLAIM_SELECT ? [ok: true] : [expect: 'Cannot find matching method']),
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        static void fairServer(int n) {
                            AsyncChannel<Integer> reqA = AsyncChannel.create(4)
                            AsyncChannel<Integer> reqB = AsyncChannel.create(4)
                            AsyncChannel<Integer> replyA = AsyncChannel.create(4)
                            AsyncChannel<Integer> replyB = AsyncChannel.create(4)
                            async {                                              // client A
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    reqA.send(i)
                                    int r = replyA.first()
                                    assert r == i + 1
                                    i = i + 1
                                }
                            }
                            async {                                              // client B
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    reqB.send(i)
                                    int r = replyB.first()
                                    assert r == i + 1
                                    i = i + 1
                                }
                            }
                            ChannelSelect alt = ChannelSelect.from(reqA, reqB).fair()
                            int j = 0
                            @Invariant({ 0 <= j && j <= 2 * n })
                            @Decreases({ 2 * n - j })
                            while (j < 2 * n) {                                  // the server: one answer per request
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
        // ---------- the loud boundary ----------
        [group: 'P261 finite cycles', name: 'a terminating partner whose element count is not static is skipped loudly', expect: 'element count is not static',
         src: tc(pair('@Requires({ n == m && n >= 0 })', 'j != m', '0 <= j && j <= m'))],
    ]
}
