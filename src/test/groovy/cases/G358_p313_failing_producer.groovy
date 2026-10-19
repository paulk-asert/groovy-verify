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
 * 'P313 failing producer' — a drain waits for its channel's close, and a producer that throws before
 * that close never sends it (GROOVY-12459): the drain hangs. The drain certificate is withheld, loudly,
 * when the closing process can throw first — unless a finally, or a catch twinned with the normal
 * close, closes the channel on the failure path too.
 */
class G358_p313_failing_producer {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 313 failing producer (a soundness fix to the Phase 245 drain discipline; GROOVY-12459): a drain (for-in / toList) waits for its channel\'s close, and a producer that THROWS before the close never sends it — the drain hangs and the failure stays on the discarded task handle. The drain certificate is now withheld, loudly, when the closing process can throw before its close: an explicit throw, or a call to a method of the class that throws, declares a throws clause, or carries @ThrowsIf (library calls are assumed to return normally; the implicit throw-sites — division, parsing, dereference — are already proof obligations). A close in a finally, or a catch close twinned with the normal close (try { …; c.close() } catch (e) { c.close() }), covers the failure path and certifies; a close ONLY in a catch is a conditional close, now on the arm side too.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // GROOVY-12459's own shape: the producer calls something that can throw on the way to its close.
        [group: 'P313 failing producer', name: 'a producer that can throw before its close withholds the drain', expect: 'is not reached if someCall',
         src: tc("""class C {
                        static void someCall(int i) {
                            if (i == 2) throw new IllegalStateException('boom')
                        }
                        static int run() {
                            AsyncChannel<Integer> out = AsyncChannel.create(2)
                            async {
                                for (int i = 1; i <= 3; i++) {
                                    someCall(i)
                                    out.send(i * i)
                                }
                                out.close()
                            }
                            int seen = 0
                            for (v in out) {
                                seen = seen + 1
                            }
                            return seen
                        }
                    }""")],
        // One-shot: the value sent is computed by a call that always throws — at runtime this hangs every time.
        [group: 'P313 failing producer', name: 'a one-shot producer whose send argument throws withholds the drain', expect: 'is not reached if boom',
         src: tc("""class C {
                        static int boom() { throw new IllegalStateException('boom') }
                        static int run() {
                            AsyncChannel<Integer> out = AsyncChannel.create(2)
                            async {
                                out.send(boom())
                                out.close()
                            }
                            int seen = 0
                            for (v in out) {
                                seen = seen + 1
                            }
                            return seen
                        }
                    }""")],
        // The throw a level down: the producer's callee calls a thrower.
        [group: 'P313 failing producer', name: 'a transitive thrower withholds the drain', expect: 'is not reached if load',
         src: tc("""class C {
                        static int check(int v) {
                            if (v < 0) throw new IllegalArgumentException('negative')
                            return v
                        }
                        static int load(int v) { return check(v) + 1 }
                        static List<Integer> run(int v) {
                            AsyncChannel<Integer> out = AsyncChannel.create(2)
                            async {
                                out.send(load(v))
                                out.close()
                            }
                            return out.toList()
                        }
                    }""")],
        // An explicit throw in the producer itself.
        [group: 'P313 failing producer', name: 'an explicit throw before the close withholds the drain', expect: 'is not reached if the throw',
         src: tc("""class C {
                        static int run(int k) {
                            AsyncChannel<Integer> out = AsyncChannel.create(2)
                            async {
                                if (k < 0) throw new IllegalArgumentException('k')
                                out.send(k)
                                out.close()
                            }
                            int seen = 0
                            for (v in out) {
                                seen = seen + 1
                            }
                            return seen
                        }
                    }""")],
        // A declared checked exception is a throw the signature admits.
        [group: 'P313 failing producer', name: 'a callee declaring throws withholds the drain', expect: 'declares throws IOException',
         src: tc("""class C {
                        static int read() throws IOException { return 1 }
                        static int run() {
                            AsyncChannel<Integer> out = AsyncChannel.create(2)
                            async {
                                out.send(read())
                                out.close()
                            }
                            int seen = 0
                            for (v in out) {
                                seen = seen + 1
                            }
                            return seen
                        }
                    }""")],
        // An exceptional contract says, in so many words, that the callee can throw.
        [group: 'P313 failing producer', name: 'a callee carrying @ThrowsIf withholds the drain', expect: 'check carries @ThrowsIf',
         src: tc("""class C {
                        @ThrowsIf(value = { v < 0 }, type = IllegalArgumentException)
                        static int check(int v) {
                            if (v < 0) throw new IllegalArgumentException('negative')
                            return v
                        }
                        static List<Integer> run(int v) {
                            AsyncChannel<Integer> out = AsyncChannel.create(2)
                            async {
                                out.send(check(v))
                                out.close()
                            }
                            return out.toList()
                        }
                    }""")],
        // The fix GROOVY-12459 recommends: close on every path. A finally does it.
        [group: 'P313 failing producer', name: 'a close in a finally certifies the drain', expect: 'Skipped channel verification', refute: 'network',
         src: tc("""class C {
                        static int boom() { throw new IllegalStateException('boom') }
                        static int run() {
                            AsyncChannel<Integer> out = AsyncChannel.create(2)
                            async {
                                try {
                                    out.send(boom())
                                } finally {
                                    out.close()
                                }
                            }
                            int seen = 0
                            for (v in out) {
                                seen = seen + 1
                            }
                            return seen
                        }
                    }""")],
        // …and so does a catch close twinned with the normal close (the JIRA's try / catch shape).
        [group: 'P313 failing producer', name: 'a catch close twinned with the normal close certifies the drain', expect: 'Skipped channel verification', refute: 'network',
         src: tc("""class C {
                        static void someCall(int i) {
                            if (i == 2) throw new IllegalStateException('boom')
                        }
                        static int run() {
                            AsyncChannel<Integer> out = AsyncChannel.create(2)
                            async {
                                try {
                                    for (int i = 1; i <= 3; i++) {
                                        someCall(i)
                                        out.send(i * i)
                                    }
                                    out.close()
                                } catch (Exception failure) {
                                    out.close()
                                }
                            }
                            int seen = 0
                            for (v in out) {
                                seen = seen + 1
                            }
                            return seen
                        }
                    }""")],
        // A close ONLY in a catch runs only on the failure path: a conditional close (the arm side used to miss this).
        [group: 'P313 failing producer', name: 'a close only in a catch is a conditional close', expect: 'is conditional',
         src: tc("""class C {
                        static int run() {
                            AsyncChannel<Integer> out = AsyncChannel.create(2)
                            async {
                                try {
                                    out.send(1)
                                } catch (Exception failure) {
                                    out.close()
                                }
                            }
                            int seen = 0
                            for (v in out) {
                                seen = seen + 1
                            }
                            return seen
                        }
                    }""")],
        // No false withholding: a producer calling a method that cannot throw still certifies.
        [group: 'P313 failing producer', name: 'a producer calling a total method still certifies', ok: true,
         src: tc("""class C {
                        static int square(int v) { return v * v }
                        static List<Integer> run(int v) {
                            AsyncChannel<Integer> out = AsyncChannel.create(2)
                            async {
                                out.send(square(v))
                                out.close()
                            }
                            return out.toList()
                        }
                    }""")],
        // A throw caught inside the producer does not reach the close's path.
        [group: 'P313 failing producer', name: 'a throw the producer catches itself still certifies', ok: true,
         src: tc("""class C {
                        static int boom() { throw new IllegalStateException('boom') }
                        static List<Integer> run() {
                            AsyncChannel<Integer> out = AsyncChannel.create(2)
                            async {
                                int v = 0
                                try {
                                    v = boom()
                                } catch (Exception e) {
                                    v = -1
                                }
                                out.send(v)
                                out.close()
                            }
                            return out.toList()
                        }
                    }""")],
    ]
}
