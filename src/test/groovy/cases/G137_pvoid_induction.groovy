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

/** 'Pvoid induction' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G137_pvoid_induction {

    static final List<Map> CASES = [

        // ===== Genuine inductive `**` facts, unlocked by void-lemma enforcement =====
        // A self-induction void lemma (@Decreases recursion supplies the IH; the pow$ step axiom does the
        // arithmetic) now PROVES a symbolic-exponent value fact — and the negative control is held to
        // account at the base case (no longer a vacuous pass). This is the rung above the one-step
        // doubling recurrence.
        [group: 'Pvoid induction', name: '2 ** n >= 1 proves by self-induction (genuine)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ (2 ** n).intValue() >= 1 })
                        @Decreases({ n })
                        static void pow2pos(int n) { if (n > 0) pow2pos(n - 1) }
                    }''')],
        [group: 'Pvoid induction', name: '2 ** n >= 2 is held to account (fails at base case n=0)', ok: false, expect: 'postcondition',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ (2 ** n).intValue() >= 2 })
                        @Decreases({ n })
                        static void bad(int n) { if (n > 0) bad(n - 1) }
                    }''')],
    ]
}
