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

/** 'P93b power axioms' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G134_p93b_power_axioms {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Literal 2 ** k unfolds to its value (and base case 2 ** 0 == 1); a wrong value refutes.'

    static final List<Map> CASES = [
        // Phase 93b — `pow$` now carries base+step defining axioms (minted by powOf), mirroring fib/gcd.
        // Tier 1: a *literal* exponent unfolds to a concrete value (`2 ** 3` e-matches to 2*2*2*1 == 8).
        [group: 'P93b power axioms', name: 'literal 2 ** 3 unfolds to 8', ok: true,
         src: tc(''' class C {
                        @Ensures({ result == 8 })
                        static int f() { (2 ** 3).intValue() }
                    }''')],
        [group: 'P93b power axioms', name: 'literal 2 ** 3 is not 9 (refutes with the unfolded value)', ok: false, expect: 'Cannot prove',
         src: tc(''' class C {
                        @Ensures({ result == 9 })
                        static int f() { (2 ** 3).intValue() }
                    }''')],
        [group: 'P93b power axioms', name: 'base case 2 ** 0 == 1', ok: true,
         src: tc(''' class C {
                        @Ensures({ result == 1 })
                        static int f() { (2 ** 0).intValue() }
                    }''')],
        [group: 'P93b power axioms', name: 'literal 3 ** 2 unfolds to 9 (non-base-2)', ok: true,
         src: tc(''' class C {
                        @Ensures({ result == 9 })
                        static int f() { (3 ** 2).intValue() }
                    }''')],
        // Tier 2: the doubling recurrence proves for *symbolic* n from the step axiom — the `1 << n` essence,
        // expressed in `**`. This is strictly stronger than the runtime `(0..10).each { assert 1<<n == 2**n }`.
        [group: 'P93b power axioms', name: 'doubling recurrence 2 ** (n+1) == 2 * (2 ** n) proves symbolically', ok: true,
         src: tc(''' class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == 2 * (2 ** n).intValue() })
                        static int f(int n) { (2 ** (n + 1)).intValue() }
                    }''')],
    ]
}
