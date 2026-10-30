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

/**
 * 'P480 identity and nullity' — Phase 89 read {@code a.is(b)} / {@code a === b} as the two references' identities being
 * equal, which said nothing of their nullity: under {@code a != null && a.is(b)}, {@code b.balance} still carried a null
 * obligation (Phase 479), and P89's alias cases had to state {@code b != null} too. At runtime {@code a.is(b)} holds when
 * both are null ({@code null.is(b)} is {@code b == null}) or both are the same object: that is its encoding now.
 */
class G521_p480_identity_nullity {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 480: `a.is(b)` / `a === b` holds when both are null or both are one object — so with `a != null` it gives `b != null` (identity alone said nothing of nullity)."

    static final List<Map> CASES = [

        // ---------- a.is(b): both null, or one object ----------
        [group: "P480 identity and nullity", name: "one non-null makes the other non-null", ok: true,
         src: tc('''final class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class C {
                        @Requires({ a != null && a.is(b) })
                        static int f(Account a, Account b) { b.balance }
                    }''')],
        [group: "P480 identity and nullity", name: "… the operator form", ok: true,
         src: tc('''final class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class C {
                        @Requires({ a != null && a === b })
                        static int f(Account a, Account b) { b.balance }
                    }''')],
        [group: "P480 identity and nullity", name: "… the other way round", ok: true,
         src: tc('''final class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class C {
                        @Requires({ b != null && a.is(b) })
                        static int f(Account a, Account b) { a.balance }
                    }''')],
        [group: "P480 identity and nullity", name: "… in a guard", ok: true,
         src: tc('''final class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class C {
                        static int f(Account a, Account b) { a != null && a.is(b) ? b.balance : 0 }
                    }''')],
        [group: "P480 identity and nullity", name: "identity alone leaves both maybe null", expect: ["Cannot get property 'balance' on null object", "obligation: b != null"],
         src: tc('''final class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class C {
                        @Requires({ a.is(b) })
                        static int f(Account a, Account b) { b.balance }
                    }''')],
        [group: "P480 identity and nullity", name: "one null makes the other null", ok: true,
         src: tc('''final class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class C {
                        @Requires({ a == null && a.is(b) })
                        @Ensures({ result == 1 })
                        static int f(Account a, Account b) { b == null ? 1 : 0 }
                    }''')],
        [group: "P480 identity and nullity", name: "… so its property throws", expect: ["Cannot get property 'balance' on null object", "obligation: b != null"],
         src: tc('''final class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class C {
                        @Requires({ a == null && a.is(b) })
                        static int f(Account a, Account b) { b.balance }
                    }''')],

        // ---------- a !== b ----------
        [group: "P480 identity and nullity", name: "distinct says nothing of the other's nullity", expect: ["Cannot get property 'balance' on null object", "obligation: b != null"],
         src: tc('''final class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class C {
                        @Requires({ a != null && a !== b })
                        static int f(Account a, Account b) { b.balance }
                    }''')],
        [group: "P480 identity and nullity", name: "a null and a non-null are distinct", ok: true,
         src: tc('''final class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class C {
                        @Requires({ a == null && b != null })
                        @Ensures({ result == 1 })
                        static int f(Account a, Account b) { a !== b ? 1 : 0 }
                    }''')],
    ]
}
