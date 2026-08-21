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

/** 'P241 channel linearity' — channel-end linearity + the one-element model made honest (slice 2 of the SEQ/PAR ladder). */
class G305_p241_channel_linearity {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 241 channel-end linearity: a point-to-point AsyncChannel has one live process per end, checked over the Phase 240 fork-join windows — two concurrent senders, two concurrent receivers, a send into a pipeline-derived channel, and a subscribe while a sender is live all error as "Channel linearity violation" (each previously PROVED a scheduler-dependent value or surfaced only as accidental noise). Sequential over-use of the one-in-flight-element model (a second send or consumer by the same process) skips loudly with the channel named, and desugarChannels\' guard refuses the scalar rewrite so nothing downstream proves a FIFO-false value. BroadcastChannel is modelled (create/send/close; subscribe() is the identity stage — every subscriber sees every element), so legal fan-out PROVES: two subscribers each read the broadcast element, and a subscriber feeds an ordinary map pipeline.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // ---------- concurrent same-end users: ERRORS (races, previously mis-modelled) ----------
        // Before this phase the flatten-order PROVED result == 2; the runtime element order is a race.
        [group: 'P241 channel linearity', name: 'two concurrent senders race the element order', expect: 'Channel linearity',
         src: tc("""class C {
                        @Ensures({ result == 2 })
                        static int race() {
                            groovy.concurrent.AsyncChannel<Integer> src = groovy.concurrent.AsyncChannel.create(2)
                            async { src.send(1) }
                            async { src.send(2) }
                            return src.first()
                        }
                    }""")],
        // The body's send lands strictly inside the producer task's fork-join window — same race,
        // main-vs-arm. (Previously surfaced only as accidental null-obligation noise.)
        [group: 'P241 channel linearity', name: 'the body sends while a producer task is live', expect: 'Channel linearity',
         src: tc("""class C {
                        static int mixed() {
                            groovy.concurrent.AsyncChannel<Integer> src = groovy.concurrent.AsyncChannel.create(2)
                            def t = async { src.send(5) }
                            src.send(7)
                            await t
                            return src.first()
                        }
                    }""")],
        // Two live receivers split the stream — each element is delivered to only one of them.
        [group: 'P241 channel linearity', name: 'two concurrent receivers split the stream', expect: 'Channel linearity',
         src: tc("""class C {
                        static int splitStream(int x) {
                            groovy.concurrent.AsyncChannel<Integer> src = groovy.concurrent.AsyncChannel.create(2)
                            async { src.send(x); src.close() }
                            async { src.first() }
                            async { src.first() }
                            return 0
                        }
                    }""")],
        // A derived channel's send-end belongs to the stage that produces it.
        [group: 'P241 channel linearity', name: 'sending into a pipeline-derived channel', expect: 'Channel linearity',
         src: tc("""class C {
                        @Ensures({ result == 9 })
                        static int intoDerived(int x) {
                            groovy.concurrent.AsyncChannel<Integer> src = groovy.concurrent.AsyncChannel.create(1)
                            groovy.concurrent.AsyncChannel<Integer> out = src.map { it + 1 }
                            out.send(9)
                            return out.first()
                        }
                    }""")],
        // A subscriber joining while a sender is live may miss elements — subscribe first.
        [group: 'P241 channel linearity', name: 'subscribing while a sender is live', expect: 'Channel linearity',
         src: tc("""class C {
                        static int lateSubscribe(int x) {
                            def b = groovy.concurrent.BroadcastChannel.<Integer>create()
                            async { b.send(x); b.close() }
                            groovy.concurrent.AsyncChannel<Integer> s1 = b.subscribe()
                            return s1.first()
                        }
                    }""")],

        // ---------- sequential over-use: the one-element model SKIPS loudly ----------
        // Before this phase the scalar rewrite PROVED result == 2 (last write wins) where the
        // runtime first() is 1 (FIFO). Not a race — the code is fine — so it skips, not errors.
        [group: 'P241 channel linearity', name: 'two sequential sends exceed the one-element model', expect: 'single in-flight element',
         src: tc("""class C {
                        @Ensures({ result == 2 })
                        static int twoSends() {
                            groovy.concurrent.AsyncChannel<Integer> src = groovy.concurrent.AsyncChannel.create(2)
                            src.send(1)
                            src.send(2)
                            return src.first()
                        }
                    }""")],
        // Before this phase both reads resolved to the same scalar and result == x + x PROVED;
        // the runtime second first() has no second element to take.
        [group: 'P241 channel linearity', name: 'two receives exceed the one-element model', expect: 'single in-flight element',
         src: tc("""class C {
                        @Ensures({ result == x + x })
                        static int twoReceives(int x) {
                            groovy.concurrent.AsyncChannel<Integer> src = groovy.concurrent.AsyncChannel.create(2)
                            async { src.send(x); src.close() }
                            int a = src.first()
                            int b = src.first()
                            return a + b
                        }
                    }""")],

        // ---------- legal networks stay green — and broadcast fan-out now PROVES ----------
        // One-to-many delivery is what BroadcastChannel is FOR: every subscriber sees every element,
        // so subscribe() is the identity stage and two subscribers each read the broadcast value.
        // (Subscribes happen before the sender forks — the legal twin of the late-subscribe error.)
        [group: 'P241 channel linearity', name: 'broadcast fan-out: every subscriber sees the element', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x + x })
                        static int fanOut(int x) {
                            def b = groovy.concurrent.BroadcastChannel.<Integer>create()
                            groovy.concurrent.AsyncChannel<Integer> s1 = b.subscribe()
                            groovy.concurrent.AsyncChannel<Integer> s2 = b.subscribe()
                            async { b.send(x); b.close() }
                            int r1 = s1.first()
                            int r2 = s2.first()
                            return r1 + r2
                        }
                    }""")],
        // Fan-out done right on point-to-point channels: each producer owns its own channel.
        [group: 'P241 channel linearity', name: 'independent producers on independent channels', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x + x + 1 })
                        static int twoChannels(int x) {
                            groovy.concurrent.AsyncChannel<Integer> c1 = groovy.concurrent.AsyncChannel.create(1)
                            groovy.concurrent.AsyncChannel<Integer> c2 = groovy.concurrent.AsyncChannel.create(1)
                            async { c1.send(x); c1.close() }
                            async { c2.send(x + 1); c2.close() }
                            int a = c1.first()
                            int b = c2.first()
                            return a + b
                        }
                    }""")],
        // A subscriber channel is an ordinary channel: it feeds a map pipeline and composes.
        [group: 'P241 channel linearity', name: 'broadcast subscriber feeds a map pipeline', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x * 2 })
                        static int broadcastPipeline(int x) {
                            def b = groovy.concurrent.BroadcastChannel.<Integer>create()
                            groovy.concurrent.AsyncChannel<Integer> s1 = b.subscribe()
                            groovy.concurrent.AsyncChannel<Integer> out = s1.map { it * 2 }
                            async { b.send(x); b.close() }
                            return out.first()
                        }
                    }""")],
    ]
}
