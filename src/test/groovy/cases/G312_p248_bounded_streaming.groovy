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
 * 'P248 bounded streaming' — literal-bounded loops that carry channel traffic unroll BEFORE the
 * structural walk, so a generator loop / consumer loop / pipeline with a static trip count becomes
 * one-shot traffic that Phases 243/245/247 certify exactly. A symbolic bound stays a loop — the
 * streaming frontier proper — and skips loudly.
 */
class G312_p248_bounded_streaming {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 248 bounded streaming (slice 8 of the SEQ/PAR ladder): a loop with a LITERAL bound that carries channel traffic — for (i in 0..<3), for (i in 1..3), for (int i = 0; i < 3; i++), nested — is unrolled before the structural walk (body copied per iteration, the index frozen to its constant, the body\'s locals renamed apart; async arms rebuilt, never mutated), so a generator loop, a consumer loop and a whole generator → map → drain pipeline certify end to end: values PROVE (the drained list, the pipeline sum), a wrong sum is refuted, and a count mismatch between a producer loop and a consumer loop is a NAMED deadlock ("the 3rd receive … only 2 sends"). Honest boundary: literal bounds only, up to 32 iterations — a symbolic bound (0..<n) stays a loop and skips loudly (since Phase 251 with the streaming model\'s reason: a range for-in is not the unit-counter while / C-style loop the symbolic model rides).'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // ---------- generator loops ----------
        [group: 'P248 bounded streaming', name: 'a literal-range generator: the drained list is 0, 1, 2', ok: true,
         src: tc("""class C {
                        @Ensures({ result.size() == 3 && result[0] == 0 && result[2] == 2 })
                        static List<Integer> numbers() {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(4)
                            for (i in 0..<3) {
                                out.send(i)
                            }
                            out.close()
                            return out.toList()
                        }
                    }""")],
        [group: 'P248 bounded streaming', name: 'the index in the sent expression', ok: true,
         src: tc("""class C {
                        @Ensures({ result.size() == 3 && result[1] == 2 && result[2] == 4 })
                        static List<Integer> evens() {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(4)
                            for (i in 0..<3) {
                                int twice = i * 2
                                out.send(twice)
                            }
                            out.close()
                            return out.toList()
                        }
                    }""")],
        [group: 'P248 bounded streaming', name: 'a C-style generator loop drains to its sum', ok: true,
         src: tc("""class C {
                        @Ensures({ result == 6 })
                        static int cStyle() {
                            groovy.concurrent.AsyncChannel<Integer> src = groovy.concurrent.AsyncChannel.create(4)
                            async {
                                for (int i = 1; i <= 3; i++) {
                                    src.send(i)
                                }
                                src.close()
                            }
                            int sum = 0
                            for (v in src) {
                                sum = sum + v
                            }
                            return sum
                        }
                    }""")],
        [group: 'P248 bounded streaming', name: 'nested literal loops: four elements in order', ok: true,
         src: tc("""class C {
                        @Ensures({ result.size() == 4 && result[1] == 1 && result[3] == 11 })
                        static List<Integer> nested() {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(4)
                            for (i in 0..<2) {
                                for (j in 0..<2) {
                                    out.send(10 * i + j)
                                }
                            }
                            out.close()
                            return out.toList()
                        }
                    }""")],

        // ---------- the whole pipeline ----------
        // generator → map stage → accumulating drain: the pipeline sum proves, and the network is
        // certified deadlock-free (the drain's close dependency is satisfiable).
        [group: 'P248 bounded streaming', name: 'generator → squares → drain: the pipeline sum proves', ok: true,
         src: tc("""class C {
                        @Ensures({ result == 5 })
                        static int pipeline() {
                            groovy.concurrent.AsyncChannel<Integer> nums = groovy.concurrent.AsyncChannel.create(4)
                            groovy.concurrent.AsyncChannel<Integer> squares = nums.map { it * it }
                            async {
                                for (i in 0..<3) {
                                    nums.send(i)
                                }
                                nums.close()
                            }
                            int sum = 0
                            for (v in squares) {
                                sum = sum + v
                            }
                            return sum
                        }
                    }""")],
        [group: 'P248 bounded streaming', name: 'a wrong pipeline sum is refuted', expect: 'Cannot prove postcondition',
         src: tc("""class C {
                        @Ensures({ result == 6 })
                        static int pipeline() {
                            groovy.concurrent.AsyncChannel<Integer> nums = groovy.concurrent.AsyncChannel.create(4)
                            groovy.concurrent.AsyncChannel<Integer> squares = nums.map { it * it }
                            async {
                                for (i in 0..<3) {
                                    nums.send(i)
                                }
                                nums.close()
                            }
                            int sum = 0
                            for (v in squares) {
                                sum = sum + v
                            }
                            return sum
                        }
                    }""")],

        // ---------- consumer loops ----------
        [group: 'P248 bounded streaming', name: 'a literal consumer loop reads the elements in order', ok: true,
         src: tc("""class C {
                        @Ensures({ result == 10 * x + y })
                        static int consumer(int x, int y) {
                            groovy.concurrent.AsyncChannel<Integer> src = groovy.concurrent.AsyncChannel.create(2)
                            async { src.send(x); src.send(y); src.close() }
                            int acc = 0
                            for (i in 0..<2) {
                                acc = 10 * acc + src.first()
                            }
                            return acc
                        }
                    }""")],
        // A producer loop of 2 against a consumer loop of 3: the FIFO pairing names the hang.
        [group: 'P248 bounded streaming', name: 'a count mismatch between loops is a named deadlock', expect: '3rd receive',
         src: tc("""class C {
                        static int mismatch() {
                            groovy.concurrent.AsyncChannel<Integer> src = groovy.concurrent.AsyncChannel.create(4)
                            async {
                                for (i in 0..<2) {
                                    src.send(i)
                                }
                                src.close()
                            }
                            int acc = 0
                            for (i in 0..<3) {
                                acc = acc + src.first()
                            }
                            return acc
                        }
                    }""")],

        // ---------- the frontier, loudly ----------
        // A symbolic bound does not unroll. (Since Phase 251 the loud reason is the streaming model's: a
        // range for-in is not the unit-counter loop it rides — write `while (i < n) … i = i + 1` with an
        // @Invariant / @Decreases and the symbolic stream PROVES.)
        [group: 'P248 bounded streaming', name: 'a symbolic bound stays a loop: the streaming frontier skips', expect: 'streaming model takes a while / C-style',
         src: tc("""class C {
                        @Ensures({ result.size() == n })
                        static List<Integer> symbolic(int n) {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(4)
                            for (i in 0..<n) {
                                out.send(i)
                            }
                            out.close()
                            return out.toList()
                        }
                    }""")],
        [group: 'P248 bounded streaming', name: 'a bound over the unrolling limit skips', expect: 'streaming model takes a while / C-style',
         src: tc("""class C {
                        @Ensures({ result.size() == 40 })
                        static List<Integer> big() {
                            groovy.concurrent.AsyncChannel<Integer> out = groovy.concurrent.AsyncChannel.create(64)
                            for (i in 0..<40) {
                                out.send(i)
                            }
                            out.close()
                            return out.toList()
                        }
                    }""")],
    ]
}
