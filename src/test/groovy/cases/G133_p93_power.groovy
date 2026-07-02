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

/** 'P93 power' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G133_p93_power {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The ** operator via an axiomatised pow primitive: a literal exponent folds and the doubling recurrence proves for symbolic n (a false value soft-fails).'

    static final List<Map> CASES = [
        [group: 'P93 power', name: 'result == (2**n).intValue() proves by congruence', ok: true,
         src: tc(''' class C {
                        @Ensures({ result == (2 ** n).intValue() })
                        static int f(int n) { (2 ** n).intValue() }
                    }''')],
        // A false *symbolic*-exponent value claim soft-fails to "could not decide" rather than a crisp
        // counterexample: the recurrence step axiom (Phase 93b) makes `pow$` refute-hostile on symbolic
        // arguments — e-matching unfolds `pow(2, n) -> pow(2, n-1) -> ...` and exhausts the per-VC timeout
        // before a model is found. Honest (never a false proof), and the same trade the bit-blasted
        // bitwise/FP fragments make. The literal and recurrence cases below are what the axioms buy.
        [group: 'P93 power', name: 'false symbolic power value soft-fails to could-not-decide (refute-hostile)', ok: false, expect: 'Could not decide',
         src: tc(''' class C {
                        @Ensures({ result == 5 })
                        static int f(int n) { (2 ** n).intValue() }
                    }''')],
    ]
}
