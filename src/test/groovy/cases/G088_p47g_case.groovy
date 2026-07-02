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

/** 'P47g case' — 8 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G088_p47g_case {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Literal toUpperCase/toLowerCase fold; a wrong-case literal refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 47g: case folding (toUpperCase / toLowerCase / equalsIgnoreCase) ----------
        // Literal pinning at mint: "Hello".toUpperCase() folds to "HELLO".
        [group: 'P47g case', name: 'literal toUpperCase folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "HELLO" })
                        static String f() { "Hello".toUpperCase() }
                    }''')],
        [group: 'P47g case', name: 'literal toLowerCase folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "hello" })
                        static String f() { "HELLO".toLowerCase() }
                    }''')],
        // Wrong-case literal refutes.
        [group: 'P47g case', name: 'wrong-case literal refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == "hello" })
                        static String f() { "Hello".toUpperCase() }
                    }''')],
        // Length-preservation for literal arguments still folds via the mint pin.
        [group: 'P47g case', name: 'toUpperCase preserves length (literal)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 5 })
                        static int f() { "hello".toUpperCase().length() }
                    }''')],
        // equalsIgnoreCase via toLower equivalence.
        [group: 'P47g case', name: 'equalsIgnoreCase literals folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "Hello".equalsIgnoreCase("HELLO") ? 1 : 0 }
                    }''')],
        [group: 'P47g case', name: 'equalsIgnoreCase distinguishes content',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "Hello".equalsIgnoreCase("World") ? 1 : 0 }
                    }''')],
        // Reflexive: s.equalsIgnoreCase(s) is true — toLower applied to the same argument is
        // pointwise-equal regardless of axioms (Z3 sees the two terms as syntactically identical).
        [group: 'P47g case', name: 'equalsIgnoreCase is reflexive', ok: true,
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.equalsIgnoreCase(s) ? 1 : 0 }
                    }''')],
        // Symbolic: a precondition that names the lowered form connects to the dispatch
        // by syntactic identity — toLower(s) on the precondition side is the same term as
        // toLower(s) inside the equalsIgnoreCase lowering.
        [group: 'P47g case', name: 'equalsIgnoreCase symmetric to toLower equality', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && t != null && s.toLowerCase() == t.toLowerCase() })
                        @Ensures({ result == 1 })
                        static int f(String s, String t) { s.equalsIgnoreCase(t) ? 1 : 0 }
                    }''')],
    ]
}
