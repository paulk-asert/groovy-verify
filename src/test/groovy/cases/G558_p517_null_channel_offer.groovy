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
 * 'P517 null channel offer' — {@code ChannelSelect.send(c, v)} throws a NullPointerException for a null channel too,
 * before its value is looked at (measured on Groovy 6.0.0: "channel must not be null", whatever {@code v} is). Its
 * registry spec's {@code @ThrowsIf} said {@code value == null} alone, exhaustively, so a null channel parameter's offer
 * compiled cleanly. The spec audit's own run said so, and had no channel receivers for the instance sends' specs.
 */
class G558_p517_null_channel_offer {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 517: a ChannelSelect send offer's channel must not be null either."

    static final List<Map> CASES = [
        [group: "P517 null channel offer", name: "a channel parameter, maybe null", expect: ['Possible NullPointerException', 'fails on: f(null)'],
         src: tc('''class C {
                        static void f(AsyncChannel<Integer> c) {
                            AsyncChannel<Integer> d = AsyncChannel.create(1)
                            ChannelSelect.Result r = await ChannelSelect.offers(ChannelSelect.send(c, 1), ChannelSelect.receive(d)).select()
                        }
                    }''')],
        [group: "P517 null channel offer", name: "… not null", ok: true,
         src: tc('''class C {
                        @Requires({ c != null })
                        static void f(AsyncChannel<Integer> c) {
                            AsyncChannel<Integer> d = AsyncChannel.create(1)
                            ChannelSelect.Result r = await ChannelSelect.offers(ChannelSelect.send(c, 1), ChannelSelect.receive(d)).select()
                        }
                    }''')],
        [group: "P517 null channel offer", name: "a channel created here", ok: true,
         src: tc('''class C {
                        static void f() {
                            AsyncChannel<Integer> c = AsyncChannel.create(1)
                            AsyncChannel<Integer> d = AsyncChannel.create(1)
                            ChannelSelect.Result r = await ChannelSelect.offers(ChannelSelect.send(c, 1), ChannelSelect.receive(d)).select()
                        }
                    }''')],
        [group: "P517 null channel offer", name: "a null channel and a null value, either", expect: ['Possible NullPointerException', 'fails on: f(null, '],
         src: tc('''class C {
                        @Requires({ v != null })
                        static void f(AsyncChannel<Integer> c, Integer v) {
                            AsyncChannel<Integer> d = AsyncChannel.create(1)
                            ChannelSelect.Result r = await ChannelSelect.offers(ChannelSelect.send(c, v), ChannelSelect.receive(d)).select()
                        }
                    }''')],
        [group: "P517 null channel offer", name: "… an offer alone", ok: true,
         src: tc('''class C {
                        static Object f() {
                            AsyncChannel<Integer> c = AsyncChannel.create(1)
                            ChannelSelect.send(c, 1)
                        }
                    }''')],
    ]
}
