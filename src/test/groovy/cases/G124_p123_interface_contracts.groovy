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

/** 'P123 interface contracts' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G124_p123_interface_contracts {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'An interface method\'s @Requires/@Ensures is inherited by every implementer — the contract-inheritance walk traverses implemented interfaces, not just the superclass.'

    static final List<Map> CASES = [
        // ---------- Phase 123: interface-declared contracts ----------
        // groovy-contracts lets an interface method carry a @Requires/@Ensures that every implementer inherits.
        // The contract-inheritance walk (findContractText / findRequires) now traverses implemented interfaces,
        // not just the superclass, so the interface's precondition guards the body and its postcondition is checked.
        // Discriminating: the interface @Requires({ d != 0 }) is the ONLY thing guarding the body's div-by-zero.
        [group: 'P123 interface contracts', name: 'interface @Requires guards the implementer body (verifies)', ok: true,
         src: HDR + """
interface NonZero {
    @Requires({ d != 0 })
    int half(int d)
}
@TypeChecked(extensions = 'verification.VerifyChecker')
class Calc implements NonZero {
    int half(int d) { 100.intdiv(d) }
}
"""],
        // Control: drop the interface and the SAME body refutes — so the interface @Requires is what's doing the work.
        [group: 'P123 interface contracts', name: 'without the interface the body refutes (control)', ok: false, expect: 'Division by zero',
         src: HDR + """
@TypeChecked(extensions = 'verification.VerifyChecker')
class Calc {
    int half(int d) { 100.intdiv(d) }
}
"""],
        // An interface @Ensures is the implementer's postcondition: a body that satisfies it verifies …
        [group: 'P123 interface contracts', name: 'interface @Ensures checked on the implementer (verifies)', ok: true,
         src: HDR + """
interface Doubler {
    @Ensures({ result == 2 * n })
    int twice(int n)
}
@TypeChecked(extensions = 'verification.VerifyChecker')
class D implements Doubler {
    int twice(int n) { n + n }
}
"""],
        // … and one that breaks it refutes.
        [group: 'P123 interface contracts', name: 'interface @Ensures violated by the implementer refutes', ok: false, expect: 'postcondition',
         src: HDR + """
interface Doubler {
    @Ensures({ result == 2 * n })
    int twice(int n)
}
@TypeChecked(extensions = 'verification.VerifyChecker')
class D implements Doubler {
    int twice(int n) { n + 1 }
}
"""],
        // README: an interface (MinBalance) carrying a tighter precondition, on a class that also extends Account —
        // the implementer inherits Account's weaker precondition (superclass-first), so it stays substitutable and
        // verifies; the interface contract is captured and available where no nearer declaration shadows it.
        [group: 'P123 interface contracts', name: 'README: Restricted2Account extends Account implements MinBalance', ok: true,
         src: HDR + """
@TypeChecked(extensions = 'verification.VerifyChecker')
class Account {
    int balance
    @Requires({ 0 <= amount && amount <= balance })
    @Ensures({ result == balance - amount })
    int debit(int amount) { balance - amount }
}
interface MinBalance {
    @Requires({ 0 <= amount && amount <= balance - 100 })
    int debit(int amount)
}
@TypeChecked(extensions = 'verification.VerifyChecker')
class Restricted2Account extends Account implements MinBalance {
    @Ensures({ result == balance - amount })
    int debit(int amount) { balance - amount }
}
"""],
    ]
}
