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

/** 'P99 range membership' — 10 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G141_p99_range_membership {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The in operator over an integer range (i in 1..3, exclusive ..<) gives bounds facts.'

    static final List<Map> CASES = [
        // Phase 99 — integer range membership: `i in lo..hi` and `(lo..hi).contains(i)` lower to the
        // order-/exclusivity-aware bounds (reusing translateContainsWithinBounds), exact for `..` and `..<`.
        // Sound: gated to integer ranges + an Int-sorted value (a decimal value, or a char/String range,
        // skips loudly — `'A'..'Z'` below). The user's switch/`.next()` examples still skip on the *body*,
        // but the precondition now translates (it was the first blocker before).
        [group: 'P99 range membership', name: 'i in 1..3 gives bounds', ok: true,
         src: tc('''class C {
                        @Requires({ i in 1..3 })
                        @Ensures({ result >= 1 && result <= 3 })
                        static int f(int i) { i }
                    }''')],
        [group: 'P99 range membership', name: '(1..3).contains(i) precondition', ok: true,
         src: tc('''class C {
                        @Requires({ (1..3).contains(i) })
                        @Ensures({ result >= 1 && result <= 3 })
                        static int f(int i) { i }
                    }''')],
        [group: 'P99 range membership', name: 'exclusive i in 0..<3 gives < 3', ok: true,
         src: tc('''class C {
                        @Requires({ i in 0..<3 })
                        @Ensures({ result <= 2 })
                        static int f(int i) { i }
                    }''')],
        [group: 'P99 range membership', name: 'soundness: i in 1..3 then result<=2 refutes (i=3)', ok: false, expect: 'postcondition',
         src: tc('''class C {
                        @Requires({ i in 1..3 })
                        @Ensures({ result <= 2 })
                        static int f(int i) { i }
                    }''')],
        [group: 'P99 range membership', name: 'i !in 1..3 means outside the bounds', ok: true,
         src: tc('''class C {
                        @Requires({ i !in 1..3 && i >= 0 })
                        @Ensures({ result == 0 || result >= 4 })
                        static int f(int i) { i }
                    }''')],
        // Phase 99b — single-char String range membership: `s in 'A'..'Z'` IS the regex class [A-Z], so it
        // lowers to str.in_re(s, re.range('A','Z')) — reusing the Phase 47 regex engine. re.range matches
        // exactly one char in the code-point interval, so multi-char/empty s is a non-member for free;
        // direction and ..</<.. exclusivity are constant code-point arithmetic. Char/decimal value or
        // multi-char endpoints skip loudly.
        [group: 'P99 range membership', name: 'string range: literal M in A..Z proves', ok: true,
         src: tc('''class C {
                        @Ensures({ result in 'A'..'Z' })
                        static String f() { 'M' }
                    }''')],
        [group: 'P99 range membership', name: 'string range soundness: lowercase m not in A..Z refutes', ok: false, expect: 'postcondition',
         src: tc('''class C {
                        @Ensures({ result in 'A'..'Z' })
                        static String f() { 'm' }
                    }''')],
        [group: 'P99 range membership', name: 'string range precond+postcond identity proves', ok: true,
         src: tc('''class C {
                        @Requires({ s in 'A'..'Z' })
                        @Ensures({ result in 'A'..'Z' })
                        static String f(String s) { s }
                    }''')],
        [group: 'P99 range membership', name: 'string range exclusive A..<C includes B', ok: true,
         src: tc('''class C {
                        @Ensures({ result in 'A'..<'C' })
                        static String f() { 'B' }
                    }''')],
        [group: 'P99 range membership', name: 'string range digit 5 in 0..9 proves', ok: true,
         src: tc('''class C {
                        @Ensures({ result in '0'..'9' })
                        static String f() { '5' }
                    }''')],
    ]
}
