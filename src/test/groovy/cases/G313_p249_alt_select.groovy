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
 * 'P249 ALT select' — occam/JCSP's ALT as groovy.concurrent's ChannelSelect: a one-shot
 * `await ChannelSelect.from(a, b).select()` is a nondeterministic choice among the branches with an
 * element left (index + value, exactly correlated), and an OR node in the wait-for graph (it proceeds
 * on ANY ready branch — the deadlock certificate becomes a completion fixpoint).
 */
class G313_p249_alt_select {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 249 ALT as ChannelSelect (slice 9 of the SEQ/PAR ladder): a one-shot `def r = await ChannelSelect.from(a, b).select()` binds r.index to a nondeterministic choice among the branches with an element left and r.value to the matching head element (index and value exactly correlated, so branch-wise claims prove) — the spec must hold for EVERY possibly-ready branch (a single-branch over-claim is refuted with a counterexample). In the wait-for graph the ALT is an OR node: deadlock-freedom becomes a completion fixpoint (an ALT completes when ANY alternative can), so a cycle through an ALT is a deadlock only when every branch is stuck ("the ALT over \'a\', \'b\' … which waits for …"), an ALT with a free branch certifies, and an ALT no branch of which is ever sent to "can never be satisfied". Beyond the model, loudly: a receive after an ALT on the same channel (a one-shot ALT must be the last receive on each branch), two ALTs over one channel, a ChannelSelect held in a variable or used beyond r.index / r.value.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // ---------- the choice proves ----------
        // One branch has an element, the other never will: the ALT can only take the first.
        [group: 'P249 ALT select', name: 'an ALT with one ready branch takes it', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x })
                        static int oneReady(int x) {
                            AsyncChannel<Integer> a = AsyncChannel.create(1)
                            AsyncChannel<Integer> b = AsyncChannel.create(1)
                            async { a.send(x); a.close() }
                            ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
                            int v = (int) r.value
                            return v
                        }
                    }""")],
        // Both branches ready: the spec must cover every branch.
        [group: 'P249 ALT select', name: 'an ALT with two ready branches: the spec covers both', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x || result == y })
                        static int either(int x, int y) {
                            AsyncChannel<Integer> a = AsyncChannel.create(1)
                            AsyncChannel<Integer> b = AsyncChannel.create(1)
                            async { a.send(x); a.close() }
                            async { b.send(y); b.close() }
                            ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
                            int v = (int) r.value
                            return v
                        }
                    }""")],
        [group: 'P249 ALT select', name: 'a single-branch over-claim is refuted', expect: 'Cannot prove postcondition',
         src: tc("""class C {
                        @Ensures({ result == x })
                        static int either(int x, int y) {
                            AsyncChannel<Integer> a = AsyncChannel.create(1)
                            AsyncChannel<Integer> b = AsyncChannel.create(1)
                            async { a.send(x); a.close() }
                            async { b.send(y); b.close() }
                            ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
                            int v = (int) r.value
                            return v
                        }
                    }""")],
        // index and value are exactly correlated: a branch-wise claim proves.
        [group: 'P249 ALT select', name: 'index and value are correlated: a branch-wise claim proves', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x + 1 || result == y - 1 })
                        static int branchwise(int x, int y) {
                            AsyncChannel<Integer> a = AsyncChannel.create(1)
                            AsyncChannel<Integer> b = AsyncChannel.create(1)
                            async { a.send(x); a.close() }
                            async { b.send(y); b.close() }
                            ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
                            int v = (int) r.value
                            if (r.index == 0) {
                                return v + 1
                            }
                            return v - 1
                        }
                    }""")],
        [group: 'P249 ALT select', name: 'the getters read the same shadows, through a map stage', ok: true,
         src: tc("""class C {
                        @Ensures({ result == x * x || result == y })
                        static int getters(int x, int y) {
                            AsyncChannel<Integer> a = AsyncChannel.create(1)
                            AsyncChannel<Integer> sq = a.map { it * it }
                            AsyncChannel<Integer> b = AsyncChannel.create(1)
                            async { a.send(x); a.close() }
                            async { b.send(y); b.close() }
                            ChannelSelect.Result r = await ChannelSelect.from(sq, b).select()
                            int v = (int) r.getValue()
                            int i = r.getIndex()
                            return i >= 0 ? v : -1
                        }
                    }""")],

        // ---------- the OR node in the wait-for graph ----------
        // Every branch of the ALT waits (transitively) on main passing the ALT: a deadlock, spelled out.
        [group: 'P249 ALT select', name: 'a cycle through an ALT with every branch stuck is a deadlock', expect: 'ALT over',
         src: tc("""class C {
                        static int stuck() {
                            AsyncChannel<Integer> a = AsyncChannel.create(1)
                            AsyncChannel<Integer> b = AsyncChannel.create(1)
                            AsyncChannel<Integer> c = AsyncChannel.create(1)
                            async { int v = c.first(); a.send(v); b.send(v) }
                            ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
                            c.send(1)
                            return 0
                        }
                    }""")],
        // The same shape with one branch served independently: the ALT proceeds on it — certified,
        // and the value model's readiness is exact: 'a' can only be served after main passes the ALT,
        // so the ALT takes 'b' — result == 2 proves (not merely 1 || 2).
        [group: 'P249 ALT select', name: 'an ALT with one free branch is certified, and takes it', ok: true,
         src: tc("""class C {
                        @Ensures({ result == 2 })
                        static int freeBranch() {
                            AsyncChannel<Integer> a = AsyncChannel.create(1)
                            AsyncChannel<Integer> b = AsyncChannel.create(1)
                            AsyncChannel<Integer> c = AsyncChannel.create(1)
                            async { int v = c.first(); a.send(v) }
                            async { b.send(2) }
                            ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
                            c.send(1)
                            int v = (int) r.value
                            return v
                        }
                    }""")],
        [group: 'P249 ALT select', name: 'an ALT no branch of which is ever sent to can never be satisfied', expect: 'no send left on any of its channels',
         src: tc("""class C {
                        static int never() {
                            AsyncChannel<Integer> a = AsyncChannel.create(1)
                            AsyncChannel<Integer> b = AsyncChannel.create(1)
                            ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
                            return 0
                        }
                    }""")],

        // ---------- beyond the model, loudly ----------
        [group: 'P249 ALT select', name: 'a receive after an ALT on the same channel is beyond the model', expect: 'after an ALT',
         src: tc("""class C {
                        @Ensures({ result == x + y })
                        static int afterAlt(int x, int y) {
                            AsyncChannel<Integer> a = AsyncChannel.create(2)
                            AsyncChannel<Integer> b = AsyncChannel.create(1)
                            async { a.send(x); a.send(y); a.close() }
                            ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
                            int v = (int) r.value
                            int w = a.first()
                            return v + w
                        }
                    }""")],
        [group: 'P249 ALT select', name: 'a ChannelSelect held in a variable is beyond the model', expect: 'outside the supported shape',
         src: tc("""class C {
                        @Ensures({ result == x })
                        static int held(int x) {
                            AsyncChannel<Integer> a = AsyncChannel.create(1)
                            AsyncChannel<Integer> b = AsyncChannel.create(1)
                            async { a.send(x); a.close() }
                            def sel = ChannelSelect.from(a, b)
                            ChannelSelect.Result r = await sel.select()
                            int v = (int) r.value
                            return v
                        }
                    }""")],
    ]
}
