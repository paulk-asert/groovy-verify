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

/** 'P-abs minvalue' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G167_p_abs_minvalue {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The Math.abs(Integer.MIN_VALUE) gotcha: abs\'s body `n < 0 ? -n : n` has `-n` overflow at MIN_VALUE under @CheckOverflow, so the `result >= 0` claim refutes (counterexample n = Integer.MIN_VALUE); excluding MIN_VALUE verifies.'

    static final List<Map> CASES = [

        // ---------- The Math.abs(Integer.MIN_VALUE) gotcha — "absolute value is non-negative" is false ----------
        // The JDK's `Math.abs(int)` is `n < 0 ? -n : n`, and `-Integer.MIN_VALUE` overflows (there is no
        // +2^31 in a signed int), so `Math.abs(Integer.MIN_VALUE) == Integer.MIN_VALUE` — negative. Under
        // @CheckOverflow the `result >= 0` claim refutes with the one counterexample, n = Integer.MIN_VALUE;
        // excluding it (`n > Integer.MIN_VALUE`, the honest precondition) verifies.
        [group: 'P-abs minvalue', name: 'abs claims non-negative but overflows at MIN_VALUE',
         expect: 'negation overflows 32-bit signed range',
         src: tc('''class C {
                        @CheckOverflow
                        @Ensures({ result >= 0 })          // "the absolute value is non-negative" — false at MIN_VALUE
                        static int abs(int n) { n < 0 ? -n : n }
                    }''')],
        [group: 'P-abs minvalue', name: 'abs verifies once MIN_VALUE is excluded', ok: true,
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ n > Integer.MIN_VALUE })   // the one input where -n overflows
                        @Ensures({ result >= 0 })
                        static int abs(int n) { n < 0 ? -n : n }
                    }''')],
    ]
}
