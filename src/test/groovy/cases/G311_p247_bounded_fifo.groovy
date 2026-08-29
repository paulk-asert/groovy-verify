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
 * 'P247 bounded FIFO' — the channel model widens from one in-flight element to a BOUNDED FIFO: the
 * k-th send declares element k, the k-th receive on a stream reads it, and a drain (toList / collect /
 * for-in) unrolls over the whole known sequence. Exact when one process owns each end and every op is
 * one-shot — the guard's verdicts — so multi-message traffic PROVES FIFO-true values where Phase 241
 * could only refuse.
 */
class G311_p247_bounded_fifo {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 247 bounded-FIFO channel traffic (slice 7 of the SEQ/PAR ladder): the k-th send on a channel declares its k-th element and the k-th receive on a stream reads it, so multi-message exchanges PROVE FIFO-true values (first-in-first-out, not last-write-wins), through map stages, per subscriber of a broadcast, and across a two-round request-reply. Drains yield the sent sequence: toList()/collect{} become the element list, for (v in ch) unrolls over the sequence with the loop body copied per element (an accumulating drain proves its sum). The wait-for graph pairs the j-th receive with the j-th send, so a receive past the last send is a NAMED deadlock ("the 2nd receive … can never be satisfied — only 1 send"). Beyond the model — conditional traffic, an end used by two processes, two consumer families, a drain through filter/split/merge/tap, an each{} drain — skips loudly with the channel and the reason named.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // ---------- FIFO values prove ----------
        // Phase 241 refused this shape (its one-element model would have proved 2); now the FIFO
        // pairing proves the first-sent value.
        [group: 'P247 bounded FIFO', name: 'two sequential sends: the first receive is the first send', ok: true,
         src: tc("""class C {
                        @Ensures({ result == 1 })
                        static int twoSends() {
                            AsyncChannel<Integer> src = AsyncChannel.create(2)
                            src.send(1)
                            src.send(2)
                            return src.first()
                        }
                    }""")],
        // The last-write-wins claim is refuted, with a counterexample — the FIFO-false value never proves.
        [group: 'P247 bounded FIFO', name: 'last-write-wins is refuted', expect: 'Cannot prove postcondition',
         src: tc("""class C {
                        @Ensures({ result == 2 })
                        static int twoSends() {
                            AsyncChannel<Integer> src = AsyncChannel.create(2)
                            src.send(1)
                            src.send(2)
                            return src.first()
                        }
                    }""")],
        // Two receives read two DISTINCT elements, in order.
        [group: 'P247 bounded FIFO', name: 'two receives read the two elements in order', ok: true,
         src: tc("""class C {
                        @Ensures({ result == 10 * x + y })
                        static int twoReceives(int x, int y) {
                            AsyncChannel<Integer> src = AsyncChannel.create(2)
                            async { src.send(x); src.send(y); src.close() }
                            int a = src.first()
                            int b = src.first()
                            return 10 * a + b
                        }
                    }""")],
        // Through a map stage: each element runs through the transform in turn.
        [group: 'P247 bounded FIFO', name: 'two elements through a map stage', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x * x + y * y })
                        static int squares(int x, int y) {
                            AsyncChannel<Integer> nums = AsyncChannel.create(2)
                            AsyncChannel<Integer> sq = nums.map { it * it }
                            async { nums.send(x); nums.send(y); nums.close() }
                            int a = sq.first()
                            int b = sq.first()
                            return a + b
                        }
                    }""")],
        // Broadcast: every subscriber has its OWN cursor over the same sequence.
        [group: 'P247 bounded FIFO', name: 'each broadcast subscriber reads the whole sequence', ok: true,
         src: tc("""class C {
                        @Ensures({ result == 2 * (x + y) })
                        static int fanOut(int x, int y) {
                            def b = BroadcastChannel.<Integer>create()
                            AsyncChannel<Integer> s1 = b.subscribe()
                            AsyncChannel<Integer> s2 = b.subscribe()
                            async { b.send(x); b.send(y); b.close() }
                            int a1 = s1.first()
                            int a2 = s1.first()
                            int b1 = s2.first()
                            int b2 = s2.first()
                            return a1 + a2 + b1 + b2
                        }
                    }""")],
        // Two rounds of request-reply: the server answers in order, the client reads in order —
        // certified deadlock-free (each j-th reply waits for the j-th request) AND both values prove.
        [group: 'P247 bounded FIFO', name: 'two-round request-reply: certified and proved', ok: true,
         src: tc("""class C {
                        @Ensures({ result == 10 * (x + 1) + (y + 1) })
                        static int twoRounds(int x, int y) {
                            AsyncChannel<Integer> request = AsyncChannel.create(2)
                            AsyncChannel<Integer> reply = AsyncChannel.create(2)
                            request.send(x)
                            request.send(y)
                            async {
                                int r1 = request.first()
                                reply.send(r1 + 1)
                                int r2 = request.first()
                                reply.send(r2 + 1)
                            }
                            int a = reply.first()
                            int b = reply.first()
                            return 10 * a + b
                        }
                    }""")],

        // The consumer task textually AHEAD of its producer (the CSP habit of listing the reader
        // first): the value model schedules the flattened statements by dataflow — a process's
        // next statement runs once the elements it reads are declared — not by textual position.
        [group: 'P247 bounded FIFO', name: 'a consumer task ahead of its producer still proves', ok: true,
         src: tc("""class C {
                        @Ensures({ result == 10 * x + y })
                        static int readerFirst(int x, int y) {
                            AsyncChannel<Integer> src = AsyncChannel.create(2)
                            AsyncChannel<Integer> out = AsyncChannel.create(1)
                            async { int a = src.first(); int b = src.first(); out.send(10 * a + b) }
                            async { src.send(x); src.send(y); src.close() }
                            return out.first()
                        }
                    }""")],

        // ---------- drains yield the sequence ----------
        [group: 'P247 bounded FIFO', name: 'toList() is the sent sequence', ok: true,
         src: tc("""class C {
                        @Ensures({ result.size() == 2 && result[0] == x && result[1] == y })
                        static List<Integer> drained(int x, int y) {
                            AsyncChannel<Integer> src = AsyncChannel.create(2)
                            src.send(x)
                            src.send(y)
                            src.close()
                            return src.toList()
                        }
                    }""")],
        [group: 'P247 bounded FIFO', name: 'collect{} maps the sent sequence', ok: true,
         src: tc("""class C {
                        @Ensures({ result.size() == 2 && result[0] == x + 1 && result[1] == y + 1 })
                        static List<Integer> collected(int x, int y) {
                            AsyncChannel<Integer> src = AsyncChannel.create(2)
                            async { src.send(x); src.send(y); src.close() }
                            return src.collect { it + 1 }
                        }
                    }""")],
        // The accumulating drain — `for (v in ch) sum += v` — unrolls over the sequence, so the
        // sum proves with no loop invariant (exact for a closed bounded stream).
        [group: 'P247 bounded FIFO', name: 'an accumulating for-in drain proves its sum', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x + y + z })
                        static int total(int x, int y, int z) {
                            AsyncChannel<Integer> src = AsyncChannel.create(4)
                            async { src.send(x); src.send(y); src.send(z); src.close() }
                            int sum = 0
                            for (v in src) {
                                int d = v
                                sum = sum + d
                            }
                            return sum
                        }
                    }""")],
        [group: 'P247 bounded FIFO', name: 'a wrong drained sum is refuted', expect: 'Cannot prove postcondition',
         src: tc("""class C {
                        @Ensures({ result == x + y })
                        static int total(int x, int y, int z) {
                            AsyncChannel<Integer> src = AsyncChannel.create(4)
                            async { src.send(x); src.send(y); src.send(z); src.close() }
                            int sum = 0
                            for (v in src) {
                                sum = sum + v
                            }
                            return sum
                        }
                    }""")],
        // A drain through a map stage: the i-th drained value is the transform of the i-th sent.
        [group: 'P247 bounded FIFO', name: 'a for-in drain through a map stage', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x * x + y * y })
                        static int sumSquares(int x, int y) {
                            AsyncChannel<Integer> nums = AsyncChannel.create(2)
                            AsyncChannel<Integer> sq = nums.map { it * it }
                            async { nums.send(x); nums.send(y); nums.close() }
                            int sum = 0
                            for (v in sq) {
                                sum = sum + v
                            }
                            return sum
                        }
                    }""")],

        // ---------- the over-receive is a named deadlock ----------
        // Phase 241 could only say "beyond the model"; the FIFO pairing knows the 2nd receive has no
        // 2nd send to match — the process blocks forever.
        [group: 'P247 bounded FIFO', name: 'a receive past the last send can never be satisfied', expect: '2nd receive',
         src: tc("""class C {
                        static int overReceive(int x) {
                            AsyncChannel<Integer> src = AsyncChannel.create(2)
                            async { src.send(x); src.close() }
                            int a = src.first()
                            int b = src.first()
                            return a + b
                        }
                    }""")],

        // ---------- beyond the model: loud, with the reason ----------
        [group: 'P247 bounded FIFO', name: 'a conditional send is beyond the model', expect: 'not one-shot',
         src: tc("""class C {
                        @Ensures({ result == 1 })
                        static int conditional(boolean flag) {
                            AsyncChannel<Integer> src = AsyncChannel.create(2)
                            if (flag) src.send(0)
                            src.send(1)
                            src.close()
                            return src.first()
                        }
                    }""")],
        [group: 'P247 bounded FIFO', name: 'sends from two processes are beyond the model', expect: 'sends from more than one process',
         src: tc("""class C {
                        @Ensures({ result == 1 })
                        static int splitSenders() {
                            AsyncChannel<Integer> src = AsyncChannel.create(2)
                            src.send(1)
                            def t = async { src.send(2) }
                            await t
                            return src.first()
                        }
                    }""")],
        [group: 'P247 bounded FIFO', name: 'a drain through a filter stage is beyond the model', expect: 'element count unknown',
         src: tc("""class C {
                        @Ensures({ result.size() == 2 })
                        static List<Integer> filtered(int x, int y) {
                            AsyncChannel<Integer> src = AsyncChannel.create(2)
                            AsyncChannel<Integer> pos = src.filter { it > 0 }
                            async { src.send(x); src.send(y); src.close() }
                            return pos.toList()
                        }
                    }""")],
    ]
}
