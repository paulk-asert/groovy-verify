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
 * 'P290 timer' — GROOVY-12343's deadline as a BRANCH of the choice, and the last member of JCSP's guard
 * family (input, output, boolean, timer) that Groovy's select was missing.
 *
 * <p>The interesting certificate is not the value but the LIVENESS. Every other branch of an ALT waits for
 * some other process to send; a timer waits for the clock, which always arrives. So a select carrying a
 * timer offer is satisfiable unconditionally — it waits on no one, and can be a member of no wait-for
 * cycle. The pair below is the whole point: the same select refuted without a deadline and certified with
 * one, the fix being the deadline rather than a rearrangement of the network.
 */
class G340_p290_timer {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 290 timer (GROOVY-12343, the last of JCSP\'s four guard kinds): a deadline as a branch of a ChannelSelect rather than an exception thrown around it. Both spellings are modelled — the timer OFFER `ChannelSelect.after(millis)`, re-armed each select so a HELD instance keeps its fair() rotation, and the timer CHANNEL `AsyncChannel.after(millis)`, whose clock starts at creation and is therefore one fixed deadline shared by every round. A timer branch names no channel, so it occupies its POSITION (r.index stays positional) while being inert to the linearity and FIFO passes. The certificate it buys is liveness: a timer always fires, so an ALT carrying one waits on no other process — the select that "can never be satisfied — no send left on any of its channels" is certified once a deadline is added, and a timed ALT is excluded from the wait-for cycle search rather than given an empty alternative set. Sampling loops (c17\'s Sniffer, c14\'s hand-eye test) then carry their @Invariant through both arms.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [
        // ── the control: an ALT whose only branch nothing serves is the Phase 249 refutation.
        [group: 'P290 timer', name: 'a select nothing sends to can never be satisfied',
         expect: 'can never be satisfied',
         src: tc("""class C {
                        static int quiet() {
                            AsyncChannel<Integer> work = AsyncChannel.create(4)
                            ChannelSelect.Result r = await ChannelSelect.from(work).select()
                            return r.index
                        }
                    }""")],

        // ── …and the same network with a deadline added. Nothing else changes: the fix is the timer.
        [group: 'P290 timer', name: 'a deadline makes the same select satisfiable',
         *: (TIMER_OFFER ? [ok: true] : [expect: 'Cannot find matching method']),
         refute: ['can never be satisfied', 'Process-network deadlock', 'Cannot invoke method select'],
         src: tc("""class C {
                        static int deadline() {
                            AsyncChannel<Integer> work = AsyncChannel.create(4)
                            ChannelSelect.Result r = await ChannelSelect.offers(ChannelSelect.receive(work),
                                                                                ChannelSelect.after(100)).select()
                            return r.index
                        }
                    }""")],

        // ── c17's Sniffer / c14's hand-eye test: a held select sampling on a deadline, its invariant
        //    carried through BOTH arms. The channel model is honestly withheld (a while (true) reader),
        //    and `refute:` pins that the LOOP was verified rather than passed over.
        [group: 'P290 timer', name: 'the sampling loop: a held select with a timer offer',
         *: (TIMER_OFFER ? [expect: 'Skipped channel verification'] : [expect: 'Cannot find matching method']),
         refute: ['Skipped loop verification', 'Cannot invoke method select', 'Cannot prove loop invariant'],
         src: tc("""class C {
                        static void sniffer() {
                            AsyncChannel<Integer> input = AsyncChannel.create(4)
                            int samples = 0
                            ChannelSelect alt = ChannelSelect.offers(ChannelSelect.receive(input),
                                                                     ChannelSelect.after(100)).fair()
                            @Invariant({ samples >= 0 })
                            while (true) {
                                ChannelSelect.Result r = await alt.select()
                                if (r.index == 0) {
                                    samples = samples + 1
                                }
                                if (r.index == 1) {
                                    samples = 0
                                }
                            }
                        }
                    }""")],

        // ── the invariant is not vacuous: claim the counter only ever grows and the timer arm refutes it,
        //    because the sample arm is exactly where a sampler RESETS.
        [group: 'P290 timer', name: 'the sampling invariant is not vacuous: the reset arm refutes a growth claim',
         *: (TIMER_OFFER ? [expect: 'Cannot prove loop invariant'] : [expect: 'Cannot find matching method']),
         src: tc("""class C {
                        static void sniffer() {
                            AsyncChannel<Integer> input = AsyncChannel.create(4)
                            int samples = 1
                            ChannelSelect alt = ChannelSelect.offers(ChannelSelect.receive(input),
                                                                     ChannelSelect.after(100)).fair()
                            @Invariant({ samples >= 1 })
                            while (true) {
                                ChannelSelect.Result r = await alt.select()
                                if (r.index == 0) {
                                    samples = samples + 1
                                }
                                if (r.index == 1) {
                                    samples = 0
                                }
                            }
                        }
                    }""")],

        // ── the CHANNEL form: one fixed deadline for the whole conversation rather than per round.
        [group: 'P290 timer', name: 'the timer channel is a fixed deadline, and is a branch like any other',
         *: (TIMER_OFFER ? [ok: true] : [expect: 'Cannot find matching method']),
         refute: ['can never be satisfied', 'Process-network deadlock'],
         src: tc("""class C {
                        static int fixed() {
                            AsyncChannel<Integer> work = AsyncChannel.create(4)
                            ChannelSelect.Result r = await ChannelSelect.from(work, AsyncChannel.after(100)).select()
                            return r.index
                        }
                    }""")],

        // ── a guarded timer: the deadline itself may be masked off, and then it is not a way forward.
        //    Pinned so the liveness exemption is not read as "any select mentioning after() never blocks".
        [group: 'P290 timer', name: 'a timer offer composes with a when guard',
         *: (TIMER_OFFER ? [expect: 'Skipped channel verification'] : [expect: 'Cannot find matching method']),
         refute: ['Skipped loop verification', 'Cannot invoke method select'],
         src: tc("""class C {
                        static void guardedTimer() {
                            AsyncChannel<Integer> input = AsyncChannel.create(4)
                            int samples = 0
                            ChannelSelect alt = ChannelSelect.offers(ChannelSelect.receive(input),
                                                                     ChannelSelect.after(100).when { samples > 0 })
                            @Invariant({ samples >= 0 })
                            while (true) {
                                ChannelSelect.Result r = await alt.select()
                                if (r.index == 0) {
                                    samples = samples + 1
                                }
                                if (r.index == 1) {
                                    assert samples > 0
                                    samples = 0
                                }
                            }
                        }
                    }""")],
    ]
}
