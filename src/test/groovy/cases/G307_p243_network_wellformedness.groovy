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

/** 'P243 network well-formedness' — deadlock-freedom as well-foundedness (slice 4 of the SEQ/PAR ladder). */
class G307_p243_network_wellformedness {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 243 network well-formedness: in the one-element fragment a method\'s channel network is an exact wait-for system — blocking receives need their root channel\'s send executed, ops need their process\'s earlier blocking points passed (arms additionally their fork), joins need the whole arm — and the network is deadlock-free exactly when that order is well-founded (the @Decreases / resource-hierarchy argument, fourth appearance). A circular wait is a GUARANTEED deadlock and errors with the cycle spelled out (receive-before-send in one process, await-the-consumer-then-send, receive-then-fork-the-producer, a two-task mutual receive cycle); a receive whose root channel is never sent to errors as never-satisfiable (including through a pipeline derivation). Conditional channel ops make the network uncertifiable (loud skip). Escaping channels and channel params carry no claim (served elsewhere — the modular assumption); a well-ordered request-reply network is certified silently and its value proves.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // ---------- circular waits: guaranteed deadlocks, spelled out ----------
        // The receive blocks the process that owns the only send: sequential self-deadlock.
        [group: 'P243 network well-formedness', name: 'receive before the send in one process', expect: 'Process-network deadlock',
         src: tc("""class C {
                        static int selfWait() {
                            AsyncChannel<Integer> src = AsyncChannel.create(1)
                            int v = src.first()
                            src.send(5)
                            return v
                        }
                    }""")],
        // Main awaits the consumer task, whose receive needs the send main would only run afterwards.
        [group: 'P243 network well-formedness', name: 'awaiting the consumer before the send', expect: 'Process-network deadlock',
         src: tc("""class C {
                        static int joinWait() {
                            AsyncChannel<Integer> src = AsyncChannel.create(1)
                            def t = async { src.first() }
                            await t
                            src.send(1)
                            return 0
                        }
                    }""")],
        // Main blocks at the receive BEFORE the producer task is ever forked.
        [group: 'P243 network well-formedness', name: 'receiving before the producer is forked', expect: 'Process-network deadlock',
         src: tc("""class C {
                        static int forkLate() {
                            AsyncChannel<Integer> src = AsyncChannel.create(1)
                            int v = src.first()
                            async { src.send(1) }
                            return v
                        }
                    }""")],
        // The classic: two tasks each receive first from the other — a mutual circular wait.
        [group: 'P243 network well-formedness', name: 'two tasks in a mutual receive cycle', expect: 'Process-network deadlock',
         src: tc("""class C {
                        static int mutual() {
                            AsyncChannel<Integer> c1 = AsyncChannel.create(1)
                            AsyncChannel<Integer> c2 = AsyncChannel.create(1)
                            async { int x = c2.first(); c1.send(x) }
                            async { int y = c1.first(); c2.send(y) }
                            return 0
                        }
                    }""")],
        // A receive through a pipeline stage still needs a send on the ROOT channel — none exists.
        [group: 'P243 network well-formedness', name: 'a derived receive with no send on its source', expect: 'can never be satisfied',
         src: tc("""class C {
                        static int noSource() {
                            AsyncChannel<Integer> src = AsyncChannel.create(1)
                            AsyncChannel<Integer> out = src.map { it + 1 }
                            return out.first()
                        }
                    }""")],

        // ---------- outside the certificate: loud skip, no claim ----------
        // A conditional send may or may not run. Since Phase 250 the send itself no longer voids the
        // certificate (it never blocks) — but the RECEIVE served by it cannot be paired with a send
        // (the count is not static), so the network skip is still the named outcome.
        [group: 'P243 network well-formedness', name: 'a conditional send is uncertifiable', expect: 'Skipped network well-formedness',
         src: tc("""class C {
                        static int maybeSend(int x) {
                            AsyncChannel<Integer> src = AsyncChannel.create(1)
                            if (x > 0) {
                                src.send(x)
                            }
                            return src.first()
                        }
                    }""")],

        // ---------- well-ordered networks: certified silently, values prove ----------
        // Request-reply done right: send the request (non-blocking), fork the replier, then block.
        // The wait-for order is well-founded, and the reply's value proves end to end.
        [group: 'P243 network well-formedness', name: 'request-reply in the right order proves', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x + 1 })
                        static int reqReply(int x) {
                            AsyncChannel<Integer> q = AsyncChannel.create(1)
                            AsyncChannel<Integer> r = AsyncChannel.create(1)
                            q.send(x)
                            async { int v = q.first(); r.send(v + 1) }
                            return r.first()
                        }
                    }""")],
        // A channel handed to another method may be served there — the modular assumption: no local
        // send, but no deadlock claim either (and no error).
        [group: 'P243 network well-formedness', name: 'an escaping channel carries no deadlock claim', ok: true,
         src: tc("""class C {
                        static void feed(AsyncChannel<Integer> ch) {
                        }
                        static int escaped() {
                            AsyncChannel<Integer> src = AsyncChannel.create(1)
                            feed(src)
                            int v = src.first()
                            return v
                        }
                    }""")],
    ]
}
