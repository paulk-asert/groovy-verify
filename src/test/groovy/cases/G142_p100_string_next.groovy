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

/** 'P100 string next' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G142_p100_string_next {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A user String.next() example over A..Z proves the letter-advance; stepping off the range refutes.'

    static final List<Map> CASES = [
        // Phase 100 — `s.next(i)` / `s.next()` (Groovy 6: last char incremented by i, default 1). First slice:
        // single-char receivers, ASCII, no wraparound. Modelled as a fresh single-char string with code
        // charAt(s,0)+i (conditioned on s single-char); range membership bridges to that code in Z3. So the
        // user's `'A'.next(i)` for `i in 0..25` proves `result in 'A'..'Z'`; widening to 0..30 escapes and
        // refutes. (Param receivers need an explicit `s != null` — range membership doesn't yet imply non-null.)
        [group: 'P100 string next', name: 'user example: A.next(i) for i in 0..25 in A..Z', ok: true,
         src: tc('''class C {
                        @Requires({ i in 0..25 })
                        @Ensures({ result in 'A'..'Z' })
                        static String letter(int i) { 'A'.next(i) }
                    }''')],
        [group: 'P100 string next', name: 'soundness: i in 0..30 escapes A..Z refutes', ok: false, expect: 'postcondition',
         src: tc('''class C {
                        @Requires({ i in 0..30 })
                        @Ensures({ result in 'A'..'Z' })
                        static String letter(int i) { 'A'.next(i) }
                    }''')],
        [group: 'P100 string next', name: 'next() no-arg on param A..Y gives B..Z', ok: true,
         src: tc('''class C {
                        @Requires({ s in 'A'..'Y' })
                        @Ensures({ result in 'B'..'Z' })
                        static String f(String s) { s.next() }
                    }''')],
        [group: 'P100 string next', name: 'soundness: A..Z .next() escapes B..Z at Z refutes', ok: false, expect: 'postcondition',
         src: tc('''class C {
                        @Requires({ s in 'A'..'Z' })
                        @Ensures({ result in 'B'..'Z' })
                        static String f(String s) { s.next() }
                    }''')],
    ]
}
