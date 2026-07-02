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

/** 'P46c string axioms' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G080_p46c_string_axioms {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'String length axioms: non-negativity, startsWith implies a length bound, a too-short string never starts with a longer prefix.'

    static final List<Map> CASES = [
        // Length on a String parameter is non-negative (axiom 1) — even with no other constraint,
        // s.length() >= 0 holds. This is the load-bearing axiom for length-based reasoning.
        [group: 'P46c string axioms', name: 'string length non-negativity', ok: true,
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ result >= 0 })
                        static int f(String s) { s.length() }
                    }''')],
        // Length-prefix bound (axiom 2): s.startsWith("hello") implies s.length() >= 5.
        [group: 'P46c string axioms', name: 'startsWith implies length bound', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.startsWith("hello") })
                        @Ensures({ result >= 5 })
                        static int f(String s) { s.length() }
                    }''')],
        // Headline application of axiom 2: a string of length 4 *cannot* start with "hello" —
        // the verifier proves the negation outright, not just leaves it open.
        [group: 'P46c string axioms', name: 'too-short string never starts with longer prefix', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.length() == 4 })
                        @Ensures({ !result })
                        static boolean f(String s) { s.startsWith("hello") }
                    }''')],
        // Soundness: claiming the opposite (a 4-char string starts with "hello") is refutable —
        // the axiom rules it out, so trying to ensure it succeeds is unverifiable.
        [group: 'P46c string axioms', name: 'too-short string cannot be claimed to start with longer prefix',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s != null && s.length() == 4 })
                        @Ensures({ result })
                        static boolean f(String s) { s.startsWith("hello") }
                    }''')],
        // Length-suffix bound (axiom 3): mirror of axiom 2 for endsWith.
        [group: 'P46c string axioms', name: 'endsWith implies length bound', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.endsWith("world") })
                        @Ensures({ result >= 5 })
                        static int f(String s) { s.length() }
                    }''')],
    ]
}
