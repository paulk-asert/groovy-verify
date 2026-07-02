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

/** 'P50 groovy div/mod' — 10 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G094_p50_groovy_div_mod {

    static final List<Map> CASES = [

        // ---------- Phase 50: Groovy-faithful division / modulo semantics ----------
        // `%` operator is the sign-of-dividend remainder: -5 % 2 == -1 (NOT the Euclidean +1).
        [group: 'P50 groovy div/mod', name: 'percent is sign-of-dividend remainder', ok: true,
         src: tc('''class C {
                        @Requires({ a == -5 })
                        @Ensures({ result == -1 })
                        static int f(int a) { a % 2 }
                    }''')],
        // Soundness regression guard: the old Euclidean `mkMod` wrongly "verified" this
        // (`a % 3 >= 0`); with sign-of-dividend semantics it correctly refutes (a = -7 → -1).
        [group: 'P50 groovy div/mod', name: 'negative modulo can be negative (refutes)',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result >= 0 })
                        static int f(int a) { a % 3 }
                    }''')],
        // `intdiv()` is truncate-toward-zero integer division.
        [group: 'P50 groovy div/mod', name: 'intdiv truncates toward zero', ok: true,
         src: tc('''class C {
                        @Requires({ a == -7 })
                        @Ensures({ result == -3 })
                        static int f(int a) { a.intdiv(2) }
                    }''')],
        // `(int)(a / b)` is the other truncating-int-div idiom (BigDecimal division then narrow).
        [group: 'P50 groovy div/mod', name: 'int-cast of division truncates', ok: true,
         src: tc('''class C {
                        @Requires({ a == 5 && b == 2 })
                        @Ensures({ result == 2 })
                        static int f(int a, int b) { (int)(a / b) }
                    }''')],
        // `.mod()` is BigInteger.mod — always non-negative (differs from `%` / `.remainder()`).
        [group: 'P50 groovy div/mod', name: 'mod is non-negative', ok: true,
         src: tc('''class C {
                        @Requires({ a == -5 })
                        @Ensures({ result == 1 })
                        static int f(int a) { a.mod(2) }
                    }''')],
        // `.remainder()` matches the `%` operator (sign of dividend).
        [group: 'P50 groovy div/mod', name: 'remainder is sign-of-dividend', ok: true,
         src: tc('''class C {
                        @Requires({ a == -5 })
                        @Ensures({ result == -1 })
                        static int f(int a) { a.remainder(2) }
                    }''')],
        // `.mod()` throws unless the modulus is positive — a Groovy-specific implicit obligation.
        [group: 'P50 groovy div/mod', name: 'mod requires positive modulus (refutes)',
         expect: 'modulus not positive',
         src: tc('class C { static int f(int a, int b) { a.mod(b) } }')],
        [group: 'P50 groovy div/mod', name: 'mod with positive divisor verified', ok: true,
         src: tc('''class C {
                        @Requires({ b > 0 })
                        @Ensures({ result >= 0 })
                        static int f(int a, int b) { a.mod(b) }
                    }''')],
        // The bare `/` operator yields a BigDecimal — outside the integer fragment, skipped loudly.
        [group: 'P50 groovy div/mod', name: 'bare division is BigDecimal (skipped)',
         expect: 'Skipped verification of postcondition',
         src: tc('''class C {
                        @Ensures({ result == 2 })
                        static int f(int a, int b) { a / b }
                    }''')],
        // intdiv divide-by-zero is still caught.
        [group: 'P50 groovy div/mod', name: 'intdiv by zero refutes',
         expect: 'Division by zero',
         src: tc('class C { static int f(int a, int b) { a.intdiv(b) } }')],
    ]
}
