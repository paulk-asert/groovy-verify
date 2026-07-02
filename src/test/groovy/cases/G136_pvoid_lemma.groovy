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

/** 'Pvoid lemma' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G136_pvoid_lemma {

    static final List<Map> CASES = [

        // ===== Void-method (lemma) postcondition enforcement =====
        // Soundness: a void method's @Ensures is now enforced (was a silent vacuous pass). A void lemma's
        // @Ensures is over params/fields; the refutation anchors on the @Ensures expression (a MethodNode
        // anchor is silently dropped by Groovy's StaticTypeCheckingVisitor on this path).
        [group: 'Pvoid lemma', name: 'false void @Ensures refutes (was vacuous)', ok: false, expect: 'Cannot prove',
         src: tc('class C { @Ensures({ 1 == 2 }) static void bad() {} }')],
        [group: 'Pvoid lemma', name: 'false void post-state @Ensures refutes', ok: false, expect: 'Cannot prove',
         src: tc('class C { int x;  @Ensures({ x == 99 }) void set5() { x = 5 } }')],
        [group: 'Pvoid lemma', name: 'false void @Ensures over param refutes', ok: false, expect: 'Cannot prove',
         src: tc('class C { @Requires({ n >= 0 }) @Ensures({ n < 0 }) static void bad(int n) {} }')],
        [group: 'Pvoid lemma', name: 'true void @Ensures over param verifies', ok: true,
         src: tc('class C { @Requires({ n >= 5 }) @Ensures({ n > 0 }) static void ok(int n) {} }')],
        // The pure void-lemma form of the doubling recurrence (Phase 93b) — now a GENUINE proof, not vacuous.
        [group: 'Pvoid lemma', name: 'doublesEachStep void lemma proves (genuine)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ 2 ** (n + 1) == 2 * (2 ** n) })
                        static void doublesEachStep(int n) {}
                    }''')],
        // A FALSE symbolic-exponent claim soft-fails to "could not decide" (the pow$ step axiom is
        // refute-hostile on symbolic args — the same trade as `2 ** n == 5`), not a clean pass. Honest:
        // it does NOT verify, so the void lemma's @Ensures is still held to account.
        [group: 'Pvoid lemma', name: 'false doubling variant soft-fails (refute-hostile, not a clean pass)', ok: false, expect: 'Could not decide',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ 2 ** (n + 1) == 3 * (2 ** n) })
                        static void wrongDoubling(int n) {}
                    }''')],
    ]
}
