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
 * 'P354 compound assignment in a helper and a body' — Phase 353's fold refused `x op= e`, `n++` and `--x`, leaving
 * such a helper an uninterpreted function. They now fold as `x = x op e` and `x = x ± 1` (every arithmetic, power,
 * bitwise and shift compound), while an expression that still assigns or increments (`return n++`) refuses. Found on
 * the way: Groovy 6 spells `%=` REMAINDER_EQUAL, which the method-body desugar didn't know, so `r %= 3` skipped any
 * method or loop that used it; the body desugar now takes the same operators as the fold.
 */
class G398_p354_compound_assign {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 354 compound assignment in a helper and a body: a contract-free helper using `x op= e` (arithmetic, power, bitwise, shift) or `n++` / `--x` as a statement is folded into its defining expression, while `return n++` and other effectful values leave the call opaque; and `%=` (Groovy 6 REMAINDER_EQUAL), `**=`, the bitwise and the shift compounds now desugar in method and loop bodies, where `r %= 3` used to skip the method.'

    static final List<Map> CASES = [

        // Phase 353 refused any compound assignment, leaving the call an uninterpreted function.
        [group: "P354 compound assignment in a helper and a body", name: "`n += 2` in a helper unfolds", ok: true,
         src: tc('''class A {
                        static int inc(int x) { int n = x; n += 2; return n }
                        @Ensures({ result == k + 2 })
                        static int f(int k) { inc(k) }
                    }''')],
        [group: "P354 compound assignment in a helper and a body", name: "… and a wrong claim refutes", expect: ["Cannot prove postcondition of f", "fails on: f("],
         src: tc('''class A {
                        static int inc(int x) { int n = x; n += 2; return n }
                        @Ensures({ result == k + 3 })
                        static int f(int k) { inc(k) }
                    }''')],
        [group: "P354 compound assignment in a helper and a body", name: "`x *= 3` on the parameter", ok: true,
         src: tc('''class A {
                        static int tri(int x) { x *= 3; return x }
                        @Ensures({ result == 3 * k })
                        static int f(int k) { tri(k) }
                    }''')],
        [group: "P354 compound assignment in a helper and a body", name: "`n++` and `--x` as statements", ok: true,
         src: tc('''class A {
                        static int net(int x) { int n = x; n++; n++; --n; return n }
                        @Ensures({ result == k + 1 })
                        static int f(int k) { net(k) }
                    }''')],
        [group: "P354 compound assignment in a helper and a body", name: "a compound assignment in a branch", ok: true,
         src: tc('''class A {
                        static int absv(int x) { int r = x; if (r < 0) { r *= -1 }; return r }
                        @Ensures({ result >= 0 })
                        static int f(int k) { absv(k) }
                    }''')],
        [group: "P354 compound assignment in a helper and a body", name: "`%=` in a helper", ok: true,
         src: tc('''class A {
                        static int m3(int x) { int r = x; r %= 3; return r }
                        @Requires({ k >= 0 })
                        @Ensures({ result >= 0 && result < 3 })
                        static int f(int k) { m3(k) }
                    }''')],
        [group: "P354 compound assignment in a helper and a body", name: "`&=` in a helper", ok: true,
         src: tc('''class A {
                        static int low(int x) { int r = x; r &= 1; return r }
                        @Ensures({ result == 0 || result == 1 })
                        static int f(int k) { low(k) }
                    }''')],
        [group: "P354 compound assignment in a helper and a body", name: "`+=` on a String", ok: true,
         src: tc('''class A {
                        static String bang(String s) { String r = s; r += "!"; return r }
                        @Requires({ s != null })
                        @Ensures({ result.length() == s.length() + 1 })
                        static String f(String s) { bang(s) }
                    }''')],
        // Folding `n++` into a value would need its evaluation-order semantics; the fold refuses any expression that still
        // assigns or increments, so the call is uninterpreted (sound, here incomplete — the claim is true).
        [group: "P354 compound assignment in a helper and a body", name: "`return n++` is not a pure value: the call stays opaque", expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        static int pinc(int x) { int n = x; return n++ }
                        @Ensures({ result == k })
                        static int f(int k) { pinc(k) }
                    }''')],
        // Fixed: Groovy 6 spells `%=` REMAINDER_EQUAL (as `%` is REMAINDER, Phase 343), which the body's compound desugar
        // didn't know — `r %= 3` was a 'statement with no modelled effect' and the method skipped.
        [group: "P354 compound assignment in a helper and a body", name: "`%=` in a method body", ok: true,
         src: tc('''class A {
                        @Requires({ k >= 0 })
                        @Ensures({ result >= 0 && result < 3 })
                        static int f(int k) { int r = k; r %= 3; return r }
                    }''')],
        [group: "P354 compound assignment in a helper and a body", name: "`&=` in a method body", ok: true,
         src: tc('''class A {
                        @Ensures({ result == 0 || result == 1 })
                        static int f(int k) { int r = k; r &= 1; return r }
                    }''')],
        [group: "P354 compound assignment in a helper and a body", name: "`%=` in a loop body", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 && result < 7 })
                        static int f(int n) {
                            int acc = 0
                            @Invariant({ 0 <= i && i <= n && acc >= 0 && acc < 7 })
                            for (int i in 0..<n) { acc = acc + 3; acc %= 7 }
                            return acc
                        }
                    }''')],
        [group: "P354 compound assignment in a helper and a body", name: "… and a wrong bound refutes", expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 && result < 5 })
                        static int f(int n) {
                            int acc = 0
                            @Invariant({ 0 <= i && i <= n && acc >= 0 && acc < 7 })
                            for (int i in 0..<n) { acc = acc + 3; acc %= 7 }
                            return acc
                        }
                    }''')],
    ]
}
