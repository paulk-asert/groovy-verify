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

/** 'P69 sum-under-store' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G191_p69_sum_under_store {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'N-account conservation via old.bal.sum() across an array store; a skim fails the build (could not decide).'

    static final List<Map> CASES = [

        // ---------- Phase 69: sum-under-store law → N-account conservation ----------
        // "No money is lost across N accounts": a transfer between any two cells of an int[] of
        // balances (cents) conserves the total. The per-store sum law makes the two compensating
        // stores cancel, so `bal.sum()` is invariant — stated here against the entry total.
        [group: 'P69 sum-under-store', name: 'N-account transfer conserves total (precondition)', ok: true,
         src: tc('''class Bank {
                       int[] bal
                       @Requires({ 0 <= i && i < bal.length && 0 <= j && j < bal.length && i != j && bal.sum() == 100 })
                       @Ensures({ bal.sum() == 100 })
                       void transfer(int i, int j, int amt) { bal[i] = bal[i] - amt; bal[j] = bal[j] + amt }
                   }''')],
        // The natural "no money lost" form: the total after equals the total before, via old.bal.sum().
        [group: 'P69 sum-under-store', name: 'N-account conservation via old.bal.sum()', ok: true,
         src: tc('''class Bank {
                       int[] bal
                       @Requires({ 0 <= i && i < bal.length && 0 <= j && j < bal.length && i != j })
                       @Ensures({ bal.sum() == old.bal.sum() })
                       void transfer(int i, int j, int amt) { bal[i] = bal[i] - amt; bal[j] = bal[j] + amt }
                   }''')],
        // Not vacuous: a transfer that skims a cent is caught — the build still fails, though as a loud
        // "could not decide" rather than a witnessed counterexample. Refuting a sum-aggregated equality is
        // the weak direction (Z3 must construct a model of the quantified sum axioms → timeout), and the
        // integer-only PBT fallback can't evaluate the array. So the conservation VERIFIES cleanly while a
        // violation fails as UNKNOWN — honest (never a silent pass), if without a counterexample.
        [group: 'P69 sum-under-store', name: 'N-account skim fails the build (could not decide)',
         expect: 'Could not decide postcondition',
         src: tc('''class Bank {
                       int[] bal
                       @Requires({ 0 <= i && i < bal.length && 0 <= j && j < bal.length && i != j })
                       @Ensures({ bal.sum() == old.bal.sum() })
                       void transfer(int i, int j, int amt) { bal[i] = bal[i] - amt; bal[j] = bal[j] + amt - 1 }
                   }''')],
    ]
}
