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

/** 'P70 decimal sum' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G192_p70_decimal_sum {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'List<BigDecimal> sum and N-account conservation via old.bal.sum(); a skim fails the build.'

    static final List<Map> CASES = [

        // ---------- Phase 70: List<BigDecimal>.sum() via Real-element arrays ----------
        // A decimal list's contents are now an `Array Int Real` and `.sum()` a Real-codomain aggregation,
        // so its base/step axioms unfold: the sum of a 2-element list is the sum of its elements.
        [group: 'P70 decimal sum', name: 'List<BigDecimal> sum of two equals their sum', ok: true,
         src: tc('''class C {
                       @Requires({ xs.size() == 2 })
                       @Ensures({ xs.sum() == xs[0] + xs[1] })
                       static void check(List<BigDecimal> xs) { }
                   }''')],
        // The capstone: "no money is lost" over a *dynamic* list of BigDecimal balances — the decimal
        // analogue of the Phase 69 int-cents proof, via the Real sum-under-store law.
        [group: 'P70 decimal sum', name: 'List<BigDecimal> transfer conserves total', ok: true,
         src: tc('''class Fund {
                       List<BigDecimal> bal
                       @Requires({ 0 <= i && i < bal.size() && 0 <= j && j < bal.size() && i != j })
                       @Ensures({ bal.sum() == old.bal.sum() })
                       void transfer(int i, int j, BigDecimal amt) { bal[i] = bal[i] - amt; bal[j] = bal[j] + amt }
                   }''')],
        // Not vacuous: skimming a cent off the credited side breaks conservation. As with the int sum,
        // refuting a sum-aggregated equality is the weak direction, so it fails the build as a loud
        // "could not decide" rather than a witnessed counterexample — never a silent pass.
        [group: 'P70 decimal sum', name: 'List<BigDecimal> skim fails the build (could not decide)',
         expect: 'Could not decide postcondition',
         src: tc('''class Fund {
                       List<BigDecimal> bal
                       @Requires({ 0 <= i && i < bal.size() && 0 <= j && j < bal.size() && i != j })
                       @Ensures({ bal.sum() == old.bal.sum() })
                       void transfer(int i, int j, BigDecimal amt) { bal[i] = bal[i] - amt; bal[j] = bal[j] + amt - 0.01 }
                   }''')],
    ]
}
