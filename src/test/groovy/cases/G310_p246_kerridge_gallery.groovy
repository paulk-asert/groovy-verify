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
 * 'P246 Kerridge gallery' — ports of the teaching shapes from Jon Kerridge's "Using Concurrency and
 * Parallelism Effectively" i & ii (bookboon.com; sources at github.com/JonKerridge/UCaPE) and the
 * groovy_jcsp plugAndPlay process vocabulary, re-spelled for Groovy 6 groovy.concurrent and run under
 * the SEQ/PAR ladder (Phases 240-245). INSPIRED BY his examples, written ourselves — his repo carries
 * no licence and JCSP is LGPL, so the shapes are ported, never the sources (the jcstress-gallery rule).
 */
class G310_p246_kerridge_gallery {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The Kerridge gallery: UCaPE / groovy_jcsp plugAndPlay teaching shapes ported to groovy.concurrent and run under the SEQ/PAR ladder. The one-shot shapes VERIFY end to end (the c02 hello-world exchange; GSquares as a map stage; GPlus joining two channels; GDelta as BroadcastChannel fan-out; the client-server request-reply certified deadlock-free; GPrint\'s drain-until-close). The classic student mistakes are NAMED COMPILE ERRORS (the mutual-receive deadlock exercise with its circular wait spelled out; the missing end-of-stream close; two producers racing one channel). Since Phase 247 the literal two-write ProduceHW / ConsumeHW pair PROVES in order (and the wrong order is refuted), since Phase 248 c03\'s GNumbers → GSquares → GPrint pipeline with a literal trip count proves its sum, since Phase 249 the one-shot ALT (ChannelSelect) proves a choice among the ready producers, since Phase 251 the SYMBOLIC c03 pipeline — GNumbers(n) → GSquares with n a parameter — proves its drained list element by element, and since Phase 252 c03 as the book writes it — a PAR of three LOOPING processes, GSquares receiving and sending — proves the printed squares for symbolic n. The honest boundary is LOUD: the unbounded streaming GNumbers generator skips — the streaming frontier is the ladder\'s recorded next rung, not a claim.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // ---------- the one-shot shapes: verified end to end ----------
        // c02 RunHelloWorld, one message: ProduceHW writes, ConsumeHello reads — PAR of two
        // processes over a one2one channel. Here the producer is the async task, the channel is
        // the AsyncChannel, and the exchanged value PROVES.
        [group: 'P246 Kerridge gallery', name: 'c02 hello world: the one-message exchange proves', ok: true,
         src: tc("""class C {
                        @Ensures({ result == 'Hello' })
                        static String helloWorld() {
                            groovy.concurrent.AsyncChannel<String> connect = groovy.concurrent.AsyncChannel.create(1)
                            async { connect.send('Hello'); connect.close() }
                            return connect.first()
                        }
                    }""")],
        // plugAndPlay GSquares: a squaring stage between generator and printer (c03's pipeline,
        // one element at a time). The stage is a map; the per-element transform proves.
        [group: 'P246 Kerridge gallery', name: 'GSquares: the squaring stage proves per element', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x * x })
                        static int squares(int x) {
                            groovy.concurrent.AsyncChannel<Integer> n2s = groovy.concurrent.AsyncChannel.create(1)
                            groovy.concurrent.AsyncChannel<Integer> s2p = n2s.map { it * it }
                            async { n2s.send(x); n2s.close() }
                            return s2p.first()
                        }
                    }""")],
        // plugAndPlay GPlus: a joining process reading one value from EACH of two input channels
        // and emitting their sum — two producers, each on its OWN channel (the legal fan-in).
        [group: 'P246 Kerridge gallery', name: 'GPlus: joining two channels proves the sum', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x + y })
                        static int plus(int x, int y) {
                            groovy.concurrent.AsyncChannel<Integer> inA = groovy.concurrent.AsyncChannel.create(1)
                            groovy.concurrent.AsyncChannel<Integer> inB = groovy.concurrent.AsyncChannel.create(1)
                            async { inA.send(x); inA.close() }
                            async { inB.send(y); inB.close() }
                            return inA.first() + inB.first()
                        }
                    }""")],
        // plugAndPlay GDelta: copy each input to every output branch. groovy.concurrent's native
        // delta is BroadcastChannel — every subscriber sees every element, and the fan-out proves.
        [group: 'P246 Kerridge gallery', name: 'GDelta: broadcast fan-out proves both branches', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x + x })
                        static int delta(int x) {
                            def b = groovy.concurrent.BroadcastChannel.<Integer>create()
                            groovy.concurrent.AsyncChannel<Integer> branch1 = b.subscribe()
                            groovy.concurrent.AsyncChannel<Integer> branch2 = b.subscribe()
                            async { b.send(x); b.close() }
                            int r1 = branch1.first()
                            int r2 = branch2.first()
                            return r1 + r2
                        }
                    }""")],
        // The client-server exchange (the Welch/Martin design-rule tradition his books teach):
        // request non-blocking, fork the server, then block on the reply. Certified deadlock-free
        // by well-foundedness of the wait-for order (Phase 243) AND the reply value proves.
        [group: 'P246 Kerridge gallery', name: 'client-server request-reply: certified and proved', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x + 1 })
                        static int clientServer(int x) {
                            groovy.concurrent.AsyncChannel<Integer> request = groovy.concurrent.AsyncChannel.create(1)
                            groovy.concurrent.AsyncChannel<Integer> reply = groovy.concurrent.AsyncChannel.create(1)
                            request.send(x)
                            async { int r = request.first(); reply.send(r + 1) }
                            return reply.first()
                        }
                    }""")],
        // GPrint / GParPrint drains its input until the stream ends. End-of-stream in the books is
        // a poison pill or a formally-derived termination; in groovy.concurrent it is close(), and
        // the drain's completion is part of the deadlock-freedom certificate (Phase 245).
        [group: 'P246 Kerridge gallery', name: 'GPrint: drain-until-close is certified to finish', ok: true,
         src: tc("""class C {
                        static int gPrint() {
                            groovy.concurrent.AsyncChannel<Integer> toPrint = groovy.concurrent.AsyncChannel.create(4)
                            toPrint.send(1)
                            toPrint.close()
                            async {
                                int seen = 0
                                for (v in toPrint) {
                                    seen = seen + 1
                                }
                            }
                            return 0
                        }
                    }""")],

        // ---------- the classic student mistakes: named compile errors ----------
        // The deadlock exercise: two processes each read from the other before writing. In the
        // books this hangs at runtime and the class discusses why; here the circular wait is a
        // compile error with the cycle spelled out.
        [group: 'P246 Kerridge gallery', name: 'the deadlock exercise: a mutual receive cycle is refuted', expect: 'Process-network deadlock',
         src: tc("""class C {
                        static int deadlockExercise() {
                            groovy.concurrent.AsyncChannel<Integer> aToB = groovy.concurrent.AsyncChannel.create(1)
                            groovy.concurrent.AsyncChannel<Integer> bToA = groovy.concurrent.AsyncChannel.create(1)
                            async { int x = bToA.first(); aToB.send(x) }
                            async { int y = aToB.first(); bToA.send(y) }
                            return 0
                        }
                    }""")],
        // The missing poison pill: a consumer drains a stream nobody ever ends.
        [group: 'P246 Kerridge gallery', name: 'the missing end-of-stream: an unclosed drain is refuted', expect: 'can never finish',
         src: tc("""class C {
                        static int missingPoison() {
                            groovy.concurrent.AsyncChannel<Integer> stream = groovy.concurrent.AsyncChannel.create(4)
                            stream.send(1)
                            async {
                                int seen = 0
                                for (v in stream) {
                                    seen = seen + 1
                                }
                            }
                            return 0
                        }
                    }""")],
        // Two producers on ONE one2one channel — the shape a one2one forbids and JCSP polices at
        // runtime; here the racing send-end is a compile error.
        [group: 'P246 Kerridge gallery', name: 'two producers race a one2one channel: refuted', expect: 'Channel linearity',
         src: tc("""class C {
                        static int notOne2One() {
                            groovy.concurrent.AsyncChannel<Integer> connect = groovy.concurrent.AsyncChannel.create(2)
                            async { connect.send(1) }
                            async { connect.send(2) }
                            return connect.first()
                        }
                    }""")],

        // ---------- the literal ProduceHW: two messages, FIFO-true (Phase 247) ----------
        // The LITERAL c02 ProduceHW writes TWO messages ("Hello", then "World") down one channel and
        // ConsumeHW reads both. Phase 246 could only refuse it (one in-flight element); the bounded
        // FIFO of Phase 247 proves the exchange end to end, in order.
        [group: 'P246 Kerridge gallery', name: 'the literal two-write ProduceHW / ConsumeHW proves in order', ok: true,
         src: tc("""class C {
                        @Ensures({ result == 'Hello World' })
                        static String produceHW() {
                            groovy.concurrent.AsyncChannel<String> connect = groovy.concurrent.AsyncChannel.create(2)
                            async { connect.send('Hello'); connect.send('World'); connect.close() }
                            String first = connect.first()
                            String second = connect.first()
                            return first + ' ' + second
                        }
                    }""")],
        [group: 'P246 Kerridge gallery', name: 'ConsumeHW read in the wrong order is refuted', expect: 'Cannot prove postcondition',
         src: tc("""class C {
                        @Ensures({ result == 'Hello World' })
                        static String produceHW() {
                            groovy.concurrent.AsyncChannel<String> connect = groovy.concurrent.AsyncChannel.create(2)
                            async { connect.send('Hello'); connect.send('World'); connect.close() }
                            String first = connect.first()
                            String second = connect.first()
                            return second + ' ' + first
                        }
                    }""")],

        // ---------- c03's pipeline, bounded (Phase 248) ----------
        // The book's first plugAndPlay network — GNumbers → GSquares → GPrint — with the generator's
        // trip count a literal: the loops unroll, the stages compose, and the printed sum proves,
        // with the network certified deadlock-free (the drain's close dependency is satisfiable).
        [group: 'P246 Kerridge gallery', name: 'c03 GNumbers → GSquares → GPrint, bounded: the sum proves', ok: true,
         src: tc("""class C {
                        @Ensures({ result == 14 })
                        static int squaresPipeline() {
                            groovy.concurrent.AsyncChannel<Integer> n2s = groovy.concurrent.AsyncChannel.create(4)
                            groovy.concurrent.AsyncChannel<Integer> s2p = n2s.map { it * it }
                            async {
                                for (n in 1..3) {
                                    n2s.send(n)
                                }
                                n2s.close()
                            }
                            int printed = 0
                            for (v in s2p) {
                                printed = printed + v
                            }
                            return printed
                        }
                    }""")],

        // ---------- c03's pipeline, symbolic (Phase 251) ----------
        // GNumbers as the book means it — a counter loop with a symbolic bound — through GSquares to a
        // drain: the drained list's size and every element prove, with the user writing only the
        // generator loop's own @Invariant / @Decreases (the channel's sequence facts are injected).
        [group: 'P246 Kerridge gallery', name: 'c03 GNumbers(n) → GSquares, symbolic: the k-th square proves', ok: true,
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.size() == n && Forall.range(0, result.size(), { int k -> result[k] == (k + 1) * (k + 1) }) })
                        static List<Integer> squares(int n) {
                            groovy.concurrent.AsyncChannel<Integer> n2s = groovy.concurrent.AsyncChannel.create(4)
                            groovy.concurrent.AsyncChannel<Integer> s2p = n2s.map { it * it }
                            async {
                                int i = 1
                                @Invariant({ 1 <= i && i <= n + 1 })
                                @Decreases({ n + 1 - i })
                                while (i <= n) {
                                    n2s.send(i)
                                    i = i + 1
                                }
                                n2s.close()
                            }
                            return s2p.toList()
                        }
                    }""")],

        // ---------- c03 as the book writes it: a PAR of three looping processes (Phase 252) ----------
        // GNumbers, GSquares and GPrint are each a process with its own loop — GSquares receives AND
        // sends. The printed list is the squares, for symbolic n; each process's loop carries only its
        // own @Invariant / @Decreases (the channels' sequence facts and the block-forever obligations
        // are the checker's).
        [group: 'P246 Kerridge gallery', name: 'c03 as three looping processes, symbolic: the printed squares prove', ok: true,
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.size() == n && Forall.range(0, result.size(), { int k -> result[k] == (k + 1) * (k + 1) }) })
                        static List<Integer> network(int n) {
                            groovy.concurrent.AsyncChannel<Integer> n2s = groovy.concurrent.AsyncChannel.create(4)
                            groovy.concurrent.AsyncChannel<Integer> s2p = groovy.concurrent.AsyncChannel.create(4)
                            async {                                              // GNumbers
                                int i = 1
                                @Invariant({ 1 <= i && i <= n + 1 })
                                @Decreases({ n + 1 - i })
                                while (i <= n) {
                                    n2s.send(i)
                                    i = i + 1
                                }
                                n2s.close()
                            }
                            async {                                              // GSquares
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    int v = n2s.first()
                                    s2p.send(v * v)
                                    i = i + 1
                                }
                                s2p.close()
                            }
                            List<Integer> printed = []                           // GPrint
                            int j = 0
                            @Invariant({ printed != null && 0 <= j && j <= n && printed.size() == j && Forall.range(0, printed.size(), { int k -> printed[k] == (k + 1) * (k + 1) }) })
                            @Decreases({ n - j })
                            while (j < n) {
                                int s = s2p.first()
                                printed.add(s)
                                j = j + 1
                            }
                            return printed
                        }
                    }""")],

        // ---------- ALT (Phase 249) ----------
        // The book's ALT: a process that takes whichever of two inputs is ready — occam's alternation,
        // JCSP's Alternative, here ChannelSelect. One-shot: the choice is nondeterministic over the
        // ready branches, so the spec must cover both producers' values.
        [group: 'P246 Kerridge gallery', name: 'ALT: take whichever producer is ready', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x || result == y })
                        static int alt(int x, int y) {
                            groovy.concurrent.AsyncChannel<Integer> left = groovy.concurrent.AsyncChannel.create(1)
                            groovy.concurrent.AsyncChannel<Integer> right = groovy.concurrent.AsyncChannel.create(1)
                            async { left.send(x); left.close() }
                            async { right.send(y); right.close() }
                            groovy.concurrent.ChannelSelect.Result chosen = await groovy.concurrent.ChannelSelect.from(left, right).select()
                            int v = (int) chosen.value
                            return v
                        }
                    }""")],

        // ---------- the honest boundary, loudly ----------
        // GNumbers is an infinite generator loop — the streaming frontier. The value claim skips
        // loudly (loop traffic never half-rewrites); certifying streaming networks is the ladder's
        // recorded next rung, not a claim made here.
        [group: 'P246 Kerridge gallery', name: 'GNumbers: the streaming generator skips (the frontier)', expect: 'Skipped verification',
         src: tc("""class C {
                        @Ensures({ result == 0 })
                        static int gNumbers() {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(4)
                            int n = 0
                            while (n < 3) {
                                out.send(n)
                                n = n + 1
                            }
                            out.close()
                            return out.first()
                        }
                    }""")],
    ]
}
