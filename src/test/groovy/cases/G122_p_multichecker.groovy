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

/** 'P-multichecker' — 8 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G122_p_multichecker {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'RegexChecker (pattern syntax) + VerifyChecker (match semantics) compose on the same .matches, each on its own concern.'

    static final List<Map> CASES = [
        // ===== Multi-checker composition (Q2): VerifyChecker runs alongside a sibling groovy-typecheckers
        // extension in one @TypeChecked(extensions=[...]); each reports its own errors. Here BOTH engage the
        // SAME `.matches("[a-z]+")` in the body: RegexChecker validates the pattern's *syntax* (it inspects
        // String.matches since GROOVY-12081), VerifyChecker proves the *semantics* — `result` equals the
        // match, via Z3's regex membership (str.in_re). One regex, two checkers, syntax and semantics.
        [group: 'P-multichecker', name: 'RegexChecker (syntax) + VerifyChecker (semantics) on the same .matches', ok: true,
         src: tcExt(['groovy.typecheckers.RegexChecker', 'verification.VerifyChecker'], '''class C {
                        @Requires({ s != null })
                        @Ensures({ result == s.matches("[a-z]+") })   // groovy-verify: result IS the match (str.in_re)
                        static boolean isLower(String s) { s.matches("[a-z]+") }   // RegexChecker: the pattern is well-formed
                    }''')],
        [group: 'P-multichecker', name: 'RegexChecker fires on a malformed pattern; the proof is unaffected', ok: false, expect: 'Bad regex',
         src: tcExt(['groovy.typecheckers.RegexChecker', 'verification.VerifyChecker'], '''class C {
                        @Requires({ s != null })
                        @Ensures({ result == s.matches("[a-z]+") })
                        static boolean isLower(String s) { s.matches("[a-z+") }
                    }''')],
        [group: 'P-multichecker', name: 'VerifyChecker refutes a false claim about the match; pattern is well-formed', ok: false, expect: 'Cannot prove',
         src: tcExt(['groovy.typecheckers.RegexChecker', 'verification.VerifyChecker'], '''class C {
                        @Requires({ s != null })
                        @Ensures({ result })
                        static boolean isLower(String s) { s.matches("[a-z]+") }
                    }''')],
        // ----- Cooperative synergy: PurityChecker supplies the purity GUARANTEE VerifyChecker relies on.
        // VerifyChecker's pure-evaluation (Phase 8a) proves f() by inlining the contract-free same-class
        // helper triple() as a value — an evaluation that is only meaningful if triple is referentially
        // transparent, which VerifyChecker assumes (the "contract-free" heuristic) but never verifies.
        // PurityChecker proves triple's @Pure affirmatively, so the assumption underpinning VerifyChecker's
        // proof becomes machine-checked. Both pass here.
        [group: 'P-multichecker', name: 'PurityChecker + VerifyChecker: @Pure helper, contract proven via pure-eval', ok: true,
         src: tcExt(['groovy.typecheckers.PurityChecker', 'verification.VerifyChecker'], '''class C {
                        @Pure
                        static int triple(int n) { 3 * n }   // PurityChecker: provably side-effect-free
                        @Ensures({ result == 30 })
                        static int f() { triple(10) }   // groovy-verify: proven by evaluating triple(10)
                    }''')],
        // When the assumption is violated, the combination rejects it — PurityChecker pinpoints WHY
        // (`@Pure violation: field assignment to 'counter'`) where VerifyChecker, unable to evaluate the
        // impure body, only degrades to a vague "Cannot prove". The precise diagnostic is the synergy.
        [group: 'P-multichecker', name: 'impure @Pure helper rejected — PurityChecker names the violation', ok: false, expect: '@Pure violation',
         src: tcExt(['groovy.typecheckers.PurityChecker', 'verification.VerifyChecker'], '''class C {
                        static int counter = 0
                        @Pure
                        static int triple(int n) { counter = counter + 1; 3 * n }
                        @Ensures({ result == 30 })
                        static int f() { triple(10) }
                    }''')],
        // And VerifyChecker still checks the contract itself: a false @Ensures over the pure helper refutes.
        [group: 'P-multichecker', name: 'VerifyChecker refutes a false contract over the pure helper', ok: false, expect: 'Cannot prove',
         src: tcExt(['groovy.typecheckers.PurityChecker', 'verification.VerifyChecker'], '''class C {
                        @Pure
                        static int triple(int n) { 3 * n }
                        @Ensures({ result == 31 })
                        static int f() { triple(10) }
                    }''')],
        // ----- NullChecker: groovy-verify proves/disproves the per-element non-nullness its model can't see.
        // NullChecker (even in flow-sensitive `strict` mode) tracks the nullness of *variables* and annotations;
        // it has no per-*element* nullity model, so it silently ASSUMES an array element `xs[0]` is non-null.
        // groovy-verify makes `xs[0].method()` an obligation `xs[0] != null` against its per-element oracle
        // (Phase 37). So on the SAME deref, groovy-verify discharges the condition NullChecker merely assumes —
        // here from a @Requires — and strict NullChecker is independently satisfied. Both pass:
        [group: 'P-multichecker', name: 'NullChecker(strict) + VerifyChecker: per-element non-null proven from @Requires', ok: true,
         src: tcExt(["groovy.typecheckers.NullChecker(strict: true)", 'verification.VerifyChecker'], '''class C {
                        @Requires({ xs != null && xs.length > 0 && xs[0] != null })
                        static int firstLen(String[] xs) { xs[0].length() }   // proven safe; strict NullChecker is satisfied too
                    }''')],
        // Drop the `xs[0] != null` premise and groovy-verify *disproves* the assumption with a concrete witness
        // (`firstLen` on a length-1 array holding null) — while strict NullChecker stays silent, its flow model
        // having no handle on the element. The condition NullChecker assumes, groovy-verify refutes.
        [group: 'P-multichecker', name: 'VerifyChecker disproves a per-element null NullChecker assumes away', ok: false, expect: 'Possible NullPointerException',
         src: tcExt(["groovy.typecheckers.NullChecker(strict: true)", 'verification.VerifyChecker'], '''class C {
                        @Requires({ xs != null && xs.length > 0 })
                        static int firstLen(String[] xs) { xs[0].length() }
                    }''')],
    ]
}
