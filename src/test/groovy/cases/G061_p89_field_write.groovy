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

/** 'P89 field-write' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G061_p89_field_write {

    static final List<Map> CASES = [

        // ---------- Phase 89 (slice 2): field WRITES through object references ----------
        // `a.balance = v` stores into the identity-keyed heap map, so a post-state read sees it.
        [group: 'P89 field-write', name: 'write seen through the same reference', ok: true,
         src: tc('''class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class C {
                        @Ensures({ a.balance == 100 })
                        static void setHundred(Account a, Account b) { a.balance = 100 }
                    }''')],
        // THE HEADLINE: a write through `a` is observed through `b` *exactly when* they alias. With
        // `a.is(b)` the store at id(a) is read back at id(b) — "mutate via one handle, observe via another".
        [group: 'P89 field-write', name: 'aliased write observed through the other reference', ok: true,
         src: tc('''class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class C {
                        @Requires({ a.is(b) })
                        @Ensures({ b.balance == 100 })
                        static void setHundred(Account a, Account b) { a.balance = 100 }
                    }''')],
        // Without the alias assumption the write to `a` need NOT be visible through `b` — refuted.
        [group: 'P89 field-write', name: 'write not observed through a non-aliased reference (refuted)',
         expect: 'Cannot prove postcondition',
         src: tc('''class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class C {
                        @Ensures({ b.balance == 100 })
                        static void setHundred(Account a, Account b) { a.balance = 100 }
                    }''')],
        // The aliasing bug-catch: setBoth *looks* correct, but if a === b the second write wins
        // (a.balance ends at 200, not 100) — the verifier refuses it and the counterexample is a === b.
        [group: 'P89 field-write', name: 'setBoth refuted under aliasing (forgot a !== b)', expect: 'Cannot prove postcondition',
         src: tc('''class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class C {
                        @Ensures({ a.balance == 100 && b.balance == 200 })
                        static void setBoth(Account a, Account b) { a.balance = 100; b.balance = 200 }
                    }''')],
        // The distinctness precondition `a !== b` (the identity operator) makes it verify.
        [group: 'P89 field-write', name: 'setBoth verifies with a !== b', ok: true,
         src: tc('''class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class C {
                        @Requires({ a !== b })
                        @Ensures({ a.balance == 100 && b.balance == 200 })
                        static void setBoth(Account a, Account b) { a.balance = 100; b.balance = 200 }
                    }''')],
    ]
}
