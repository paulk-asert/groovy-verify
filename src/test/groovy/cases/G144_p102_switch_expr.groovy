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
    static final String DESCRIPTION = 'A switch expression (arrow form, int/String/range labels) folds to an ite-chain; an unmatched case or a false branch claim refutes.'

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
        [group: 'P102 switch expr', name: 'string subject switch proves', ok: true,
         src: tc('''class C {
                        @Requires({ s in 'x'..'y' })
                        @Ensures({ result == 1 || result == 2 })
                        static int code(String s) {
                            switch(s) { case 'x' -> 1; case 'y' -> 2; default -> 0 }
                        }
                    }''')],
    ]
}
