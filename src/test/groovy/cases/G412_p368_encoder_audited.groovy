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
 * 'P368 the encoder audited' — most of what the verifier assumes about Groovy is the encoder's own translation, never
 * checked against the runtime. EncoderAuditTest now runs ~130 built-in expressions (arithmetic and its wrap, %, mod,
 * intdiv, shifts, bitwise ops, casts, ranges, Groovy truth, list / array / string methods) on an edge-value grid,
 * and asks the verifier, pinned to each point, to prove the runtime's value wrong. It found: a cast was transparent,
 * so `x as boolean` meant the int `x` (wrong at every non-zero x); and under @CheckOverflow, `intdiv`, `<<` and a
 * narrowing cast wrapped with no obligation. Also `last()` on an empty list had no obligation. The default math-int
 * model's divergence is confirmed to be exactly the JVM's wrap — the documented assumption.
 */
class G412_p368_encoder_audited {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 368 the encoder audited against the runtime: x as boolean is Groovy truth and an integer as String its decimal text; under @CheckOverflow intdiv, a left shift and a narrowing cast are overflow obligations; last() on a possibly-empty list is one too.'

    static final List<Map> CASES = [

        // Before: verified — the cast was transparent, so `x as boolean` stood for the int `x` itself.
        [group: "P368 the encoder audited", name: "x as boolean is Groovy truth",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        @Requires({ x == 7 })
                        @Ensures({ result != true })
                        static boolean g(int x) { x as boolean }
                    }''')],

        [group: "P368 the encoder audited", name: "… which proves what it is", ok: true,
         src: tc('''final class A {
                        @Requires({ x != 0 })
                        @Ensures({ result })
                        static boolean g(int x) { x as boolean }
                    }''')],

        // Before: refuted — over-strict, the int stood in for the boolean.
        [group: "P368 the encoder audited", name: "… and zero is false", ok: true,
         src: tc('''final class A {
                        @Ensures({ result == (x != 0) })
                        static boolean g(int x) { x as boolean }
                    }''')],

        // Before: skipped — the int was compared with a string.
        [group: "P368 the encoder audited", name: "x as String of an integer is its decimal text", ok: true,
         src: tc('''final class A {
                        @Requires({ x == -7 })
                        @Ensures({ result == '-7' })
                        static String g(int x) { x as String }
                    }''')],

        // Before: verified under @CheckOverflow — `MIN_VALUE.intdiv(-1)` wraps as `MIN_VALUE / -1` does, but had no obligation.
        [group: "P368 the encoder audited", name: "@CheckOverflow: intdiv overflows at MIN_VALUE / -1",
         expect: "division overflows 32-bit signed range",
         src: tc('''@verification.CheckOverflow
                    final class A {
                        static int g(int x, int y) { y == 0 ? 0 : x.intdiv(y) }
                    }''')],

        // Before: verified under @CheckOverflow — a left shift is a multiply, and wraps.
        [group: "P368 the encoder audited", name: "@CheckOverflow: a left shift overflows",
         expect: "left shift overflows 32-bit signed range",
         src: tc('''@verification.CheckOverflow
                    final class A {
                        static int g(int x) { x << 1 }
                    }''')],

        [group: "P368 the encoder audited", name: "… within range it proves", ok: true,
         src: tc('''@verification.CheckOverflow
                    final class A {
                        @Requires({ -1000 < x && x < 1000 })
                        @Ensures({ result == 2 * x })
                        static int g(int x) { x << 1 }
                    }''')],

        // Before: verified under @CheckOverflow — `(int) l` was the identity, though it wraps outside int range.
        [group: "P368 the encoder audited", name: "@CheckOverflow: a narrowing cast overflows",
         expect: "narrowing cast to int overflows",
         src: tc('''@verification.CheckOverflow
                    final class A {
                        static int g(long l) { (int) l }
                    }''')],

        [group: "P368 the encoder audited", name: "… and a cast that fits is fine", ok: true,
         src: tc('''@verification.CheckOverflow
                    final class A {
                        @Requires({ 0 <= l && l < 100 })
                        @Ensures({ result == l })
                        static int g(long l) { (int) l }
                    }''')],

        // Before: silent — `last()` throws on an empty list, and only first/head/pop carried the obligation.
        [group: "P368 the encoder audited", name: "last() on a possibly-empty list is an obligation",
         expect: "Possible IndexOutOfBoundsException",
         src: tc('''final class A {
                        @Requires({ xs != null })
                        static int g(List<Integer> xs) { xs.last() }
                    }''')],

        [group: "P368 the encoder audited", name: "… discharged by non-emptiness", ok: true,
         src: tc('''final class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int g(List<Integer> xs) { xs.last() }
                    }''')],
    ]
}
