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

/** 'P-shift-power' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G138_p_shift_power {

    static final List<Map> CASES = [
        // `1 << n == 2 ** n` proved for the whole range 0..30 at once — the verification analog of the
        // runtime `(0..10).each { assert 1 << n == 2 ** n }`, and stronger (every n, not sampled points).
        // n <= 30 is the genuinely-true range: at n >= 31 the 32-bit `1 << n` wraps negative while `2 ** n`
        // (an unbounded BigInteger) does not, so they really differ (see ROADMAP). The off-by-one control
        // confirms the proof is not vacuous.
        [group: 'P-shift-power', name: 'shift equals power of two: 1 << n == 2 ** n for n in 0..30', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && n <= 30 })
                        @Ensures({ (1 << n) == (2 ** n).intValue() })
                        static void shiftIsPowerOfTwo(int n) {}   // ✓ holds for all 31 values
                    }''')],
        [group: 'P-shift-power', name: 'shift/power off-by-one is held to account', ok: false, expect: 'postcondition',
         src: tc('''class C {
                        @Requires({ n >= 0 && n <= 30 })
                        @Ensures({ (1 << n) == (2 ** n).intValue() + 1 })
                        static void bad(int n) {}
                    }''')],
    ]
}
