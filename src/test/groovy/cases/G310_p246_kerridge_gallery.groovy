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
    static final String DESCRIPTION = 'The Kerridge gallery: UCaPE / groovy_jcsp plugAndPlay teaching shapes ported to groovy.concurrent and run under the SEQ/PAR ladder. The one-shot shapes VERIFY end to end (the c02 hello-world exchange; GSquares as a map stage; GPlus joining two channels; GDelta as BroadcastChannel fan-out; the client-server request-reply certified deadlock-free; GPrint\'s drain-until-close). The classic student mistakes are NAMED COMPILE ERRORS (the mutual-receive deadlock exercise with its circular wait spelled out; the missing end-of-stream close; two producers racing one channel). The honest boundaries are LOUD: the literal two-write ProduceHW exceeds the one-in-flight-element model, and the streaming GNumbers generator skips — the streaming frontier is the ladder\'s recorded next rung, not a claim.'

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

        // ---------- the honest boundaries, loudly ----------
        // The LITERAL c02 ProduceHW writes TWO messages ("Hello", then "World") down one channel:
        // beyond the one-in-flight-element model, so it skips loudly with the channel named —
        // refused, never mis-proved.
        [group: 'P246 Kerridge gallery', name: 'the literal two-write ProduceHW exceeds the model (loud)', expect: 'single in-flight element',
         src: tc("""class C {
                        static String produceHW() {
                            groovy.concurrent.AsyncChannel<String> connect = groovy.concurrent.AsyncChannel.create(2)
                            async { connect.send('Hello'); connect.send('World'); connect.close() }
                            return connect.first()
                        }
                    }""")],
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
