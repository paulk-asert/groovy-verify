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
 * 'P495 null sends' — a channel holds no null: {@code c.send(null)} throws a NullPointerException at the call (measured
 * on Groovy 6.0.0: "channel does not support null values"; a {@code BroadcastChannel}'s "value must not be null"; a
 * {@code ChannelSelect.send(c, null)} offer's as it is made). A send on a channel parameter carries the registry spec's
 * {@code @ThrowsIf}; one the channel engine rewrites carries {@code assert v != null}, reported as the send's
 * exception. So a received value is never null. Two comparisons with null read better with it: a primitive's is false,
 * and a callee's {@code result} is its own declaration's at its call, not the caller's.
 */
class G536_p495_null_send {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 495: `c.send(null)` throws — an AsyncChannel's, a BroadcastChannel's and a ChannelSelect send offer's value must not be null, so a received value never is."

    static final List<Map> CASES = [

        // ---------- a local channel's send (rewritten) ----------
        [group: "P495 null sends", name: "a null sent", expect: ['Possible NullPointerException: c.send(null) throws when null == null'],
         src: tc('''class C {
                        static int f() {
                            AsyncChannel<Integer> c = AsyncChannel.create(2)
                            c.send(null)
                            1
                        }
                    }''')],
        [group: "P495 null sends", name: "a value that may be null", expect: ['Possible NullPointerException: c.send(v) throws when v == null', 'fails on: f(null)'],
         src: tc('''class C {
                        static int f(Integer v) {
                            AsyncChannel<Integer> c = AsyncChannel.create(1)
                            c.send(v)
                            int x = c.first()
                            x
                        }
                    }''')],
        [group: "P495 null sends", name: "… none when it isn't", ok: true,
         src: tc('''class C {
                        @Requires({ v != null })
                        static int f(Integer v) {
                            AsyncChannel<Integer> c = AsyncChannel.create(1)
                            c.send(v)
                            int x = c.first()
                            x
                        }
                    }''')],
        [group: "P495 null sends", name: "… nor for an int", ok: true,
         src: tc('''class C {
                        static int f(int v) {
                            AsyncChannel<Integer> c = AsyncChannel.create(1)
                            c.send(v)
                            int x = c.first()
                            x
                        }
                    }''')],
        [group: "P495 null sends", name: "a null element sent", expect: ['Possible NullPointerException: c.send(xs[0]) throws when xs[0] == null', 'fails on: f([null])'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        static void f(List<Integer> xs) {
                            AsyncChannel<Integer> c = AsyncChannel.create(2)
                            c.send(xs[0])
                        }
                    }''')],
        [group: "P495 null sends", name: "an awaited send", expect: ['Possible NullPointerException: c.send(v) throws when v == null'],
         src: tc('''class C {
                        static int f(Integer v) {
                            AsyncChannel<Integer> c = AsyncChannel.create(1)
                            await c.send(v)
                            int x = c.first()
                            x
                        }
                    }''')],
        [group: "P495 null sends", name: "what's received isn't null", expect: ['c.send(v) throws when v == null'], refute: 'Assertion may not hold',
         src: tc('''class C {
                        static void f(Integer v) {
                            AsyncChannel<Integer> c = AsyncChannel.create(1)
                            c.send(v)
                            Integer x = c.first()
                            assert x != null
                        }
                    }''')],

        // ---------- a channel parameter's send (the registry spec) ----------
        [group: "P495 null sends", name: "a channel parameter's send", expect: ['Possible NullPointerException: c.send(s) throws when s == null', 'obligation: !(s == null)'],
         src: tc('''class C {
                        @Requires({ c != null })
                        static void f(AsyncChannel<String> c, String s) { c.send(s) }
                    }''')],
        [group: "P495 null sends", name: "… guarded", ok: true,
         src: tc('''class C {
                        @Requires({ c != null && s != null })
                        static void f(AsyncChannel<String> c, String s) { c.send(s) }
                    }''')],
        [group: "P495 null sends", name: "… of an int, which a primitive's comparison with null knows", ok: true,
         src: tc('''class C {
                        @Requires({ c != null })
                        static void f(AsyncChannel<Integer> c, int s) { c.send(s) }
                    }''')],
        [group: "P495 null sends", name: "… of a literal null", expect: ['c.send(null) throws when null == null'],
         src: tc('''class C {
                        @Requires({ c != null })
                        static void f(AsyncChannel<Integer> c) { c.send(null) }
                    }''')],

        // ---------- a broadcast, and a select's offer ----------
        [group: "P495 null sends", name: "a broadcast's send", expect: ['Possible NullPointerException: b.send(v) throws when v == null', 'fails on: f(null)'],
         src: tc('''class C {
                        static void f(Integer v) {
                            BroadcastChannel<Integer> b = BroadcastChannel.create()
                            AsyncChannel<Integer> s = b.subscribe()
                            b.send(v)
                            int x = s.first()
                        }
                    }''')],
        [group: "P495 null sends", name: "… a broadcast parameter's", expect: ['Possible NullPointerException: b.send(v) throws when v == null'],
         src: tc('''class C {
                        @Requires({ b != null })
                        static void f(BroadcastChannel<Integer> b, Integer v) { b.send(v) }
                    }''')],
        [group: "P495 null sends", name: "a select's send offer", expect: ['Possible NullPointerException: ChannelSelect.send(c, v) throws when v == null'],
         src: tc('''class C {
                        static void f(Integer v) {
                            AsyncChannel<Integer> c = AsyncChannel.create(1)
                            AsyncChannel<Integer> d = AsyncChannel.create(1)
                            ChannelSelect.Result r = await ChannelSelect.offers(ChannelSelect.send(c, v), ChannelSelect.receive(d)).select()
                        }
                    }''')],

        // ---------- a callee's result, at its call ----------
        [group: "P495 null sends", name: "a callee's result is its own declaration's", expect: ['Cannot prove postcondition'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result == xs[0] })
                        static Integer h(List<Integer> xs) { xs[0] }
                        @Requires({ xs != null && xs.size() > 0 && xs[0] == null })
                        @Ensures({ result == 5 })
                        static int f(List<Integer> xs) { Integer b = h(xs); 4 }
                    }''')],
        [group: "P495 null sends", name: "… and its null promise isn't the caller's int", expect: ['Cannot prove postcondition'],
         src: tc('''class C {
                        @Ensures({ result == null })
                        static Integer h() { null }
                        @Ensures({ result == 5 })
                        static int f() { Integer b = h(); 4 }
                    }''')],
    ]
}
