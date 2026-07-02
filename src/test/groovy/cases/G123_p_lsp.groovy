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

/** 'P-lsp' — 7 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G123_p_lsp {

    static final List<Map> CASES = [
        // ---------- Phase 120: behavioral subtyping (Liskov substitution) ----------
        // When an override *redeclares* its own contract, groovy-verify proves it is substitutable for the
        // overridden method: the precondition must be WEAKENED (pre_parent ⟹ pre_child) and the postcondition
        // STRENGTHENED ((pre_parent ∧ post_child) ⟹ post_parent). These are pure SMT implication checks over
        // the shared parameter/result namespace — no body involved — and a violation comes with a witness.
        // A child that strengthens its precondition rejects calls the parent accepted — the classic LSP break:
        [group: 'P-lsp', name: 'strengthened precondition refutes (witness)', ok: false, expect: 'precondition is not behaviourally compatible',
         src: HDR + """
@TypeChecked(extensions = 'verification.VerifyChecker')
class Base { @Requires({ x >= 0 }) @Ensures({ result == x }) int f(int x) { x } }
@TypeChecked(extensions = 'verification.VerifyChecker')
class Sub extends Base { @Requires({ x >= 10 }) @Ensures({ result == x }) int f(int x) { x } }
"""],
        // Weakening the precondition (accepting more) is fine — substitutable.
        [group: 'P-lsp', name: 'weakened precondition is allowed', ok: true,
         src: HDR + """
@TypeChecked(extensions = 'verification.VerifyChecker')
class Base { @Requires({ x >= 0 }) @Ensures({ result == x }) int f(int x) { x } }
@TypeChecked(extensions = 'verification.VerifyChecker')
class Sub extends Base { @Requires({ x >= -5 }) @Ensures({ result == x }) int f(int x) { x } }
"""],
        // Parent has no @Requires (accepts everything); a child that adds one strengthens it — a violation.
        [group: 'P-lsp', name: 'adding a precondition over an unconstrained parent refutes', ok: false, expect: 'precondition is not behaviourally compatible',
         src: HDR + """
@TypeChecked(extensions = 'verification.VerifyChecker')
class Base { @Ensures({ result == x }) int f(int x) { x } }
@TypeChecked(extensions = 'verification.VerifyChecker')
class Sub extends Base { @Requires({ x >= 0 }) @Ensures({ result == x }) int f(int x) { x } }
"""],
        // A child that weakens its postcondition promises less than the parent — a violation.
        [group: 'P-lsp', name: 'weakened postcondition refutes', ok: false, expect: 'postcondition is not behaviourally compatible',
         src: HDR + """
@TypeChecked(extensions = 'verification.VerifyChecker')
class Base { @Requires({ x >= 0 }) @Ensures({ result >= 5 }) int f(int x) { x + 5 } }
@TypeChecked(extensions = 'verification.VerifyChecker')
class Sub extends Base { @Requires({ x >= 0 }) @Ensures({ result >= 0 }) int f(int x) { x + 5 } }
"""],
        // Strengthening the postcondition (promising more) is fine — substitutable.
        [group: 'P-lsp', name: 'strengthened postcondition is allowed', ok: true,
         src: HDR + """
@TypeChecked(extensions = 'verification.VerifyChecker')
class Base { @Requires({ x >= 0 }) @Ensures({ result >= 5 }) int f(int x) { x + 10 } }
@TypeChecked(extensions = 'verification.VerifyChecker')
class Sub extends Base { @Requires({ x >= 0 }) @Ensures({ result >= 10 }) int f(int x) { x + 10 } }
"""],
        // The README account example (instance-field contracts): GoldAccount weakens `debit`'s precondition
        // (overdraft) → substitutable; RestrictedAccount strengthens it (min balance) → refuted with a witness.
        [group: 'P-lsp', name: 'README: GoldAccount weakens debit precondition (substitutable)', ok: true,
         src: HDR + """
@TypeChecked(extensions = 'verification.VerifyChecker')
class Account {
    int balance
    @Requires({ 0 <= amount && amount <= balance })
    @Ensures({ result == balance - amount })
    int debit(int amount) { balance - amount }
}
@TypeChecked(extensions = 'verification.VerifyChecker')
class GoldAccount extends Account {
    @Requires({ 0 <= amount && amount <= balance + 1000 })
    @Ensures({ result == balance - amount })
    int debit(int amount) { balance - amount }
}
"""],
        [group: 'P-lsp', name: 'README: RestrictedAccount strengthens debit precondition (refutes)', ok: false, expect: 'precondition is not behaviourally compatible',
         src: HDR + """
@TypeChecked(extensions = 'verification.VerifyChecker')
class Account {
    int balance
    @Requires({ 0 <= amount && amount <= balance })
    @Ensures({ result == balance - amount })
    int debit(int amount) { balance - amount }
}
@TypeChecked(extensions = 'verification.VerifyChecker')
class RestrictedAccount extends Account {
    @Requires({ 0 <= amount && amount <= balance - 100 })
    @Ensures({ result == balance - amount })
    int debit(int amount) { balance - amount }
}
"""],
    ]
}
