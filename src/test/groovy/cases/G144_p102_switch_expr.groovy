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

/** 'P102 switch expr' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G144_p102_switch_expr {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A switch in EXPRESSION position (`return switch (\u2026)`, a first-class SwitchExpression) folds to an ite-chain; a switch in STATEMENT position \u2014 including the implicit-return form, which GROOVY-12399 settled is decided by POSITION rather than arm shape \u2014 is walked as the n-way if/else it is, one path per arm, so an arm may do real work before yielding and a switch that is not the last statement is modelled too. An unmatched case (Groovy yields null), a false branch claim, or a wrong claim about either statement-position shape refutes; a colon-form arm that FALLS THROUGH into the next is refused loudly.'

    static final List<Map> CASES = [
        // Phase 102 — switch EXPRESSIONS (arrow form, simple literal labels) lower to an ite-chain
        // ite(subj==l1,v1, ite(subj==l2,v2, ... default-or-fresh)). Up to Groovy 6.0.0-beta-2 a switch expr
        // desugared to `{ -> switch }.call()` (still recognised); since beta-3 it is a first-class
        // SwitchExpression node, AND static type checking requires it to be exhaustive — a `default` unless
        // the subject is an enum whose constants are all covered. So every case here carries a default; the
        // verifier's contribution is knowing when that default is DEAD (the precondition covers the labels —
        // the proof goes through) and when it is not (i in 1..4 reaches 'z' — refuted with i = 4).
        [group: 'P102 switch expr', name: 'target: switch i->letter proves', ok: true,
         src: tc('''class C {
                        @Requires({ i in 1..3 })
                        @Ensures({ result in 'a'..'c' })
                        static String letter(int i) {
                            switch(i) { case 1 -> 'a'; case 2 -> 'b'; case 3 -> 'c'; default -> 'z' }
                        }
                    }''')],
        [group: 'P102 switch expr', name: 'soundness: i in 1..4 reaches the default refutes (i=4)', ok: false, expect: 'postcondition',
         src: tc('''class C {
                        @Requires({ i in 1..4 })
                        @Ensures({ result in 'a'..'c' })
                        static String letter(int i) {
                            switch(i) { case 1 -> 'a'; case 2 -> 'b'; case 3 -> 'c'; default -> 'z' }
                        }
                    }''')],
        [group: 'P102 switch expr', name: 'false postcondition refutes (case 3 gives c)', ok: false, expect: 'postcondition',
         src: tc('''class C {
                        @Requires({ i in 1..3 })
                        @Ensures({ result in 'a'..'b' })
                        static String letter(int i) {
                            switch(i) { case 1 -> 'a'; case 2 -> 'b'; case 3 -> 'c'; default -> 'z' }
                        }
                    }''')],
        [group: 'P102 switch expr', name: 'default covers all cases, proves with no precondition', ok: true,
         src: tc('''class C {
                        @Ensures({ result in 'a'..'z' })
                        static String f(int i) {
                            switch(i) { case 1 -> 'a'; default -> 'z' }
                        }
                    }''')],
        // A block-bodied arrow case with an explicit `yield` (beta-3's spelling) reads the same way.
        [group: 'P102 switch expr', name: 'a yield-bodied case proves', ok: true,
         src: tc('''class C {
                        @Requires({ i in 1..2 })
                        @Ensures({ result == i * 10 })
                        static int tens(int i) {
                            switch(i) { case 1 -> { yield 10 }; case 2 -> 20; default -> 0 }
                        }
                    }''')],
        // ── no default, no match: Groovy yields null, so a non-trivial postcondition refutes on that path.
        //    Groovy 6.0.0-RC-3's GROOVY-12399 removed the carve-out that GUARANTEED this ("a switch in
        //    implicit-return position stayed an expression that yielded null when unmatched"), so the
        //    behaviour now falls out of ordinary implicit-return handling rather than a rule written for it.
        //    The encoder's no-default model — an unconstrained result, a sound conservative refute — rests on
        //    it, which is why it is pinned here rather than left as an assumption.
        [group: 'P102 switch expr', name: 'no default and no match yields null, so the postcondition refutes',
         ok: false, expect: 'postcondition',
         src: tc('''class C {
                        @Ensures({ result == 'a' })
                        static String unmatched(int i) {
                            switch(i) { case 1 -> 'a' }
                        }
                    }''')],
        [group: 'P102 switch expr', name: 'string subject switch proves', ok: true,
         src: tc('''class C {
                        @Requires({ s in 'x'..'y' })
                        @Ensures({ result == 1 || result == 2 })
                        static int code(String s) {
                            switch(s) { case 'x' -> 1; case 'y' -> 2; default -> 0 }
                        }
                    }''')],

        // ── Since GROOVY-12399 settled that POSITION decides whether a switch yields a value, a switch in
        //    STATEMENT form is walked as the n-way if/else it is — one path per arm. Two shapes the
        //    single-expression ite-chain could never reach follow, each with its refute twin so the proof is
        //    shown to be real rather than a silent skip.
        [group: 'P102 switch expr', name: 'an arm that does real work before yielding proves', ok: true,
         src: tc('''class C {
                        @Requires({ i == 1 })
                        @Ensures({ result == 6 })
                        static int multi(int i) {
                            switch(i) { case 1 -> { int t = 2; yield t * 3 }; default -> 0 }
                        }
                    }''')],
        [group: 'P102 switch expr', name: 'a wrong claim about a working arm refutes', ok: false, expect: 'postcondition',
         src: tc('''class C {
                        @Requires({ i == 1 })
                        @Ensures({ result == 99 })
                        static int multi(int i) {
                            switch(i) { case 1 -> { int t = 2; yield t * 3 }; default -> 0 }
                        }
                    }''')],
        [group: 'P102 switch expr', name: 'a switch in statement position (not the last statement) proves', ok: true,
         src: tc('''class C {
                        @Requires({ i == 1 })
                        @Ensures({ result == 7 })
                        static int nonTail(int i) {
                            int r = 0
                            switch(i) { case 1 -> r = 7; default -> r = 9 }
                            return r
                        }
                    }''')],
        [group: 'P102 switch expr', name: 'a wrong claim about a statement-position switch refutes', ok: false, expect: 'postcondition',
         src: tc('''class C {
                        @Requires({ i == 1 })
                        @Ensures({ result == 99 })
                        static int nonTail(int i) {
                            int r = 0
                            switch(i) { case 1 -> r = 7; default -> r = 9 }
                            return r
                        }
                    }''')],
        // ── the boundary, said out loud: an arm that runs on into the next is not modelled.
        [group: 'P102 switch expr', name: 'a colon-form arm that falls through is refused loudly',
         expect: 'switch case falls through to the next',
         src: tc('''class C {
                        @Requires({ i == 1 })
                        @Ensures({ result == 7 })
                        static int fall(int i) {
                            int r = 0
                            switch(i) { case 1: r = 7; case 2: r = 9; break }
                            return r
                        }
                    }''')],
    ]
}
