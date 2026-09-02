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
 * 'P273 guarded ALT' — Kerridge c05's precondition mask, as far as this API can carry it. JCSP writes
 * `qAlt.priSelect(preCon)` with `preCon[PUT] = counter < elements`: a guard is masked OFF while keeping its
 * index. `ChannelSelect.from(…)` is positional and has no mask, so the mask spells as a condition choosing
 * the argument list — and the checker now reads that shape. Three outcomes: it is a ChannelSelect (no bogus
 * null-deref on the result of a conditional build — the false positive this phase removes); its branch
 * positions must AGREE across the arms or `r.index` names different channels in different arms, refused with
 * that reason; and a spec over the union of the arms proves. What is NOT modelled here is the guard's own
 * restriction — the branch set is over-approximated by the union — so a claim that leans on a branch being
 * masked off is honestly not proved.
 */
class G335_p273_guarded_alt {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 273 guarded ALT (slice 34 of the SEQ/PAR ladder): Kerridge c05\'s ALT precondition mask (`priSelect(preCon)`, `preCon[PUT] = counter < elements`) ported as far as a positional select allows. A select built by a condition — `counter == 0 ? ChannelSelect.from(put) : ChannelSelect.from(put, get)` — is recognised as a ChannelSelect, which removes a FALSE POSITIVE: before this phase a conditionally-built select was an opaque object and its `.select()` raised a "Cannot invoke method select() on null object" obligation nothing could discharge. Every arm\'s `from()` is sanctioned, so the channels are not flagged as escaping the supported shapes. The branch POSITIONS must agree across the arms — a guarded ALT may drop a branch only from the END — because `r.index` is positional and would otherwise name a different channel per arm; the mismatch is refused naming the API gap (JCSP\'s select(preCon) masks a guard while KEEPING its index; ChannelSelect has no equivalent). A spec over the UNION of the arms proves and is not vacuous (a stronger single-branch claim refutes). The guard\'s own restriction is deliberately NOT modelled: the branch set is over-approximated by the union, sound for proving and incomplete for refuting, so c05\'s bounded-buffer invariant (which needs the masked branch to be excluded) is not claimed here.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    // A guarded ALT that drops its LAST branch: positions agree, so r.index still names what it always did.
    // The spec is over the union of the arms — which is what the model carries — and it proves.
    // `refute:` pins the false positive this phase removes: no null-deref obligation on a conditional build.
    static final List<Map> CASES = [
        [group: 'P273 guarded ALT', name: 'a guarded ALT dropping its last branch is a ChannelSelect, and the union spec proves', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x || result == y })
                        static int guarded(int x, int y, boolean both) {
                            AsyncChannel<Integer> left = AsyncChannel.create(1)
                            AsyncChannel<Integer> right = AsyncChannel.create(1)
                            async { left.send(x); left.close() }
                            async { right.send(y); right.close() }
                            ChannelSelect alt = both ? ChannelSelect.from(left, right) : ChannelSelect.from(left)
                            ChannelSelect.Result chosen = await alt.select()
                            int v = (int) chosen.value
                            return v
                        }
                    }""")],
        // Not vacuous: the stronger claim does not follow from the union model, and refutes.
        [group: 'P273 guarded ALT', name: 'the union model is not vacuous: a single-branch claim refutes', expect: 'Cannot prove postcondition',
         refute: 'NullPointerException',
         src: tc("""class C {
                        @Ensures({ result == x })
                        static int guarded(int x, int y, boolean both) {
                            AsyncChannel<Integer> left = AsyncChannel.create(1)
                            AsyncChannel<Integer> right = AsyncChannel.create(1)
                            async { left.send(x); left.close() }
                            async { right.send(y); right.close() }
                            ChannelSelect alt = both ? ChannelSelect.from(left, right) : ChannelSelect.from(left)
                            ChannelSelect.Result chosen = await alt.select()
                            int v = (int) chosen.value
                            return v
                        }
                    }""")],
        // c05's Queue as the book writes it: PUT is masked off when the buffer is full and GET when it is
        // empty. Masking the FIRST guard moves every later branch's index, which `from(…)` cannot express —
        // refused with the API gap named, rather than silently reasoning about the wrong channel.
        [group: 'P273 guarded ALT', name: 'c05\'s bounded buffer masks its first guard: refused, the index would move', expect: 'branch POSITIONS differ',
         refute: 'NullPointerException',
         src: tc("""class C {
                        @Requires({ elements >= 1 })
                        static void queue(int elements) {
                            AsyncChannel<Integer> put = AsyncChannel.create(4)
                            AsyncChannel<Integer> get = AsyncChannel.create(4)
                            int counter = 0
                            @Invariant({ 0 <= counter && counter <= elements })
                            while (true) {
                                ChannelSelect alt = counter == 0 ? ChannelSelect.from(put) : counter == elements ? ChannelSelect.from(get) : ChannelSelect.from(put, get)
                                ChannelSelect.Result r = await alt.select()
                                if (r.index == 0) {
                                    counter = counter + 1
                                }
                                if (r.index == 1) {
                                    counter = counter - 1
                                }
                            }
                        }
                    }""")],

        // ---------- GROOVY-12324's mask, modelled: c05's Queue proves (Phase 275) ----------
        // The book's bounded circular buffer, at last spellable AND provable. PUT is offered only while
        // there is room and GET only while there is content, so the buffer can neither overflow nor
        // underflow — `0 <= counter <= elements` is preserved because the checker knows the committed
        // branch is one whose flag holds. Everything the two refutations below turn on is that fact.
        [group: 'P273 guarded ALT', name: 'c05\'s bounded buffer: the guards make the invariant hold',
         *: (GUARDED_SELECT ? [ok: true] : [expect: 'Cannot find matching method']),
         src: tc("""class C {
                        @Requires({ elements >= 1 })
                        static void queue(int elements) {
                            AsyncChannel<Integer> put = AsyncChannel.create(4)
                            AsyncChannel<Integer> get = AsyncChannel.create(4)
                            ChannelSelect alt = ChannelSelect.from(put, get)
                            int counter = 0
                            @Invariant({ 0 <= counter && counter <= elements })
                            while (true) {
                                ChannelSelect.Result r = await alt.select(counter < elements, counter > 0)
                                if (r.index == 0) {
                                    counter = counter + 1
                                }
                                if (r.index == 1) {
                                    counter = counter - 1
                                }
                            }
                        }
                    }""")],
        // Not vacuous, twice over. Leave PUT always enabled and the buffer overflows; leave GET always
        // enabled and it underflows. Each is refuted at the arm the missing guard would have blocked —
        // which is exactly the lesson c05 teaches, now mechanical.
        [group: 'P273 guarded ALT', name: 'without the PUT guard the buffer overflows: refuted',
         *: (GUARDED_SELECT ? [expect: 'Cannot prove loop invariant'] : [expect: 'Cannot find matching method']),
         src: tc("""class C {
                        @Requires({ elements >= 1 })
                        static void queue(int elements) {
                            AsyncChannel<Integer> put = AsyncChannel.create(4)
                            AsyncChannel<Integer> get = AsyncChannel.create(4)
                            ChannelSelect alt = ChannelSelect.from(put, get)
                            int counter = 0
                            @Invariant({ 0 <= counter && counter <= elements })
                            while (true) {
                                ChannelSelect.Result r = await alt.select(true, counter > 0)
                                if (r.index == 0) {
                                    counter = counter + 1
                                }
                                if (r.index == 1) {
                                    counter = counter - 1
                                }
                            }
                        }
                    }""")],
        [group: 'P273 guarded ALT', name: 'without the GET guard the buffer underflows: refuted',
         *: (GUARDED_SELECT ? [expect: 'Cannot prove loop invariant'] : [expect: 'Cannot find matching method']),
         src: tc("""class C {
                        @Requires({ elements >= 1 })
                        static void queue(int elements) {
                            AsyncChannel<Integer> put = AsyncChannel.create(4)
                            AsyncChannel<Integer> get = AsyncChannel.create(4)
                            ChannelSelect alt = ChannelSelect.from(put, get)
                            int counter = 0
                            @Invariant({ 0 <= counter && counter <= elements })
                            while (true) {
                                ChannelSelect.Result r = await alt.select(counter < elements, true)
                                if (r.index == 0) {
                                    counter = counter + 1
                                }
                                if (r.index == 1) {
                                    counter = counter - 1
                                }
                            }
                        }
                    }""")],

        // ---------- GROOVY-12326: the same buffer, guarded per offer (Phase 276) ----------
        // The idiomatic spelling: each guard is written ON the branch it guards, so nothing has to be
        // counted, and the closure is consulted at every select so the instance can still be held (which
        // is what keeps a fair() rotation alive). Same certificate as the positional mask above — that
        // equivalence is the point of pinning both.
        [group: 'P273 guarded ALT', name: 'c05\'s bounded buffer, guarded per offer: the same invariant proves',
         *: (WHEN_GUARD ? [ok: true] : [expect: 'Cannot find matching method']),
         src: tc("""class C {
                        @Requires({ elements >= 1 })
                        static void queue(int elements) {
                            AsyncChannel<Integer> put = AsyncChannel.create(4)
                            AsyncChannel<Integer> get = AsyncChannel.create(4)
                            int counter = 0
                            ChannelSelect alt = ChannelSelect.offers(ChannelSelect.receive(put).when { counter < elements },
                                                                     ChannelSelect.receive(get).when { counter > 0 })
                            @Invariant({ 0 <= counter && counter <= elements })
                            while (true) {
                                ChannelSelect.Result r = await alt.select()
                                if (r.index == 0) {
                                    counter = counter + 1
                                }
                                if (r.index == 1) {
                                    counter = counter - 1
                                }
                            }
                        }
                    }""")],
        // Drop the PUT guard in this spelling too, and the same overflow is refuted at the same arm.
        [group: 'P273 guarded ALT', name: 'per-offer guards are not vacuous either: dropping the PUT guard overflows',
         *: (WHEN_GUARD ? [expect: 'Cannot prove loop invariant'] : [expect: 'Cannot find matching method']),
         src: tc("""class C {
                        @Requires({ elements >= 1 })
                        static void queue(int elements) {
                            AsyncChannel<Integer> put = AsyncChannel.create(4)
                            AsyncChannel<Integer> get = AsyncChannel.create(4)
                            int counter = 0
                            ChannelSelect alt = ChannelSelect.offers(ChannelSelect.receive(put),
                                                                     ChannelSelect.receive(get).when { counter > 0 })
                            @Invariant({ 0 <= counter && counter <= elements })
                            while (true) {
                                ChannelSelect.Result r = await alt.select()
                                if (r.index == 0) {
                                    counter = counter + 1
                                }
                                if (r.index == 1) {
                                    counter = counter - 1
                                }
                            }
                        }
                    }""")],
    ]
}
