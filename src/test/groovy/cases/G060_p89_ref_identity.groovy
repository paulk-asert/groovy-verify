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

/** 'P89 ref-identity' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G060_p89_ref_identity {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Reference identity (a.is(b) / a===b) ⇒ the two handles\' fields coincide; no identity ⇒ they need not (refutes).'

    static final List<Map> CASES = [

        // ---------- Phase 89 (slice 1): reference identity + identity-keyed field reads ----------
        // Two same-class object params are "alias-modelled": their Int fields read through a per-(class,field)
        // heap map indexed by object identity, so `a.is(b)`/`a === b` (identity equality) makes the fields
        // provably coincide. Here `a.is(b)` ⇒ a.balance == b.balance ⇒ a.balance + b.balance == 2 * a.balance.
        [group: 'P89 ref-identity', name: 'a.is(b) ⇒ fields coincide (identity model)', ok: true,
         src: tc('''class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class C {
                        @Requires({ a.is(b) })
                        @Ensures({ result == 2 * a.balance })
                        static int twice(Account a, Account b) { a.balance + b.balance }
                    }''')],
        // The `===` operator form, as a pure model tautology: equal identities ⇒ equal field reads.
        [group: 'P89 ref-identity', name: 'a === b ==> a.balance == b.balance', ok: true,
         src: tc('''class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class C {
                        @Ensures({ (a === b) ==> (a.balance == b.balance) })
                        static void f(Account a, Account b) { }
                    }''')],
        // Without the identity assumption the two references may differ — so `result == 2 * a.balance`
        // is NOT provable (b.balance is unconstrained relative to a.balance). Refutes.
        [group: 'P89 ref-identity', name: 'no identity ⇒ fields need not coincide (refuted)',
         expect: 'Cannot prove postcondition',
         src: tc('''class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class C {
                        @Ensures({ result == 2 * a.balance })
                        static int twice(Account a, Account b) { a.balance + b.balance }
                    }''')],
    ]
}
