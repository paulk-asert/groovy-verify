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

/** 'nested static (GROOVY-12066)' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G198_nested_static_groovy_12066 {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A static nested class\'s @Invariant is established by its constructor (GROOVY-12066); unestablished refutes.'

    static final List<Map> CASES = [

        // ---------- GROOVY-12066: contracts on a *static nested* class (upstream fix) ----------
        // `@Invariant`/`@Requires`/`@Ensures` on a static nested class used to NPE at compile time in
        // groovy-contracts' DynamicSetterInjectionVisitor (upstream, independent of groovy-verify). Now
        // fixed; these confirm the class compiles AND the verifier engages on the nested class normally.
        [group: 'nested static (GROOVY-12066)', name: 'static nested @Invariant established by ctor verifies', ok: true,
         src: HDR + '''
            class Outer {
                @TypeChecked(extensions = 'verification.VerifyChecker')
                @Invariant({ balance >= 0 })
                static class Account {
                    int balance
                    @Requires({ b >= 0 })
                    Account(int b) { balance = b }
                }
            }
         '''.stripIndent()],
        // The same nested class without the precondition cannot establish the invariant (b may be < 0).
        [group: 'nested static (GROOVY-12066)', name: 'static nested @Invariant unestablished refutes', expect: 'invariant',
         src: HDR + '''
            class Outer {
                @TypeChecked(extensions = 'verification.VerifyChecker')
                @Invariant({ balance >= 0 })
                static class Account {
                    int balance
                    Account(int b) { balance = b }
                }
            }
         '''.stripIndent()],
    ]
}
