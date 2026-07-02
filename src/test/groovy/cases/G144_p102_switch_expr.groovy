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
        // Phase 102 — switch EXPRESSIONS (arrow form, simple literal labels) lower to an ite-chain. A switch
        // expr desugars to `{ -> switch }.call()`; the encoder recognises that and builds
        // ite(subj==l1,v1, ite(subj==l2,v2, ... default-or-fresh)). int and String subjects; no-default/no-match
        // is a fresh value (Groovy yields null) so an uncovered case refutes conservatively.
        [group: 'P102 switch expr', name: 'target: switch i->letter proves', ok: true,
         src: tc('''class C {
                        @Requires({ i in 1..3 })
                        @Ensures({ result in 'a'..'c' })
                        static String letter(int i) {
                            switch(i) { case 1 -> 'a'; case 2 -> 'b'; case 3 -> 'c' }
                        }
                    }''')],
        [group: 'P102 switch expr', name: 'soundness: i in 1..4 unmatched refutes (i=4)', ok: false, expect: 'postcondition',
         src: tc('''class C {
                        @Requires({ i in 1..4 })
                        @Ensures({ result in 'a'..'c' })
                        static String letter(int i) {
                            switch(i) { case 1 -> 'a'; case 2 -> 'b'; case 3 -> 'c' }
                        }
                    }''')],
        [group: 'P102 switch expr', name: 'false postcondition refutes (case 3 gives c)', ok: false, expect: 'postcondition',
         src: tc('''class C {
                        @Requires({ i in 1..3 })
                        @Ensures({ result in 'a'..'b' })
                        static String letter(int i) {
                            switch(i) { case 1 -> 'a'; case 2 -> 'b'; case 3 -> 'c' }
                        }
                    }''')],
        [group: 'P102 switch expr', name: 'default covers all cases, proves with no precondition', ok: true,
         src: tc('''class C {
                        @Ensures({ result in 'a'..'z' })
                        static String f(int i) {
                            switch(i) { case 1 -> 'a'; default -> 'z' }
                        }
                    }''')],
        [group: 'P102 switch expr', name: 'string subject switch proves', ok: true,
         src: tc('''class C {
                        @Requires({ s in 'x'..'y' })
                        @Ensures({ result == 1 || result == 2 })
                        static int code(String s) {
                            switch(s) { case 'x' -> 1; case 'y' -> 2 }
                        }
                    }''')],
    ]
}
