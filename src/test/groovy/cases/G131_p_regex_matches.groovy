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

/** 'P regex matches' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G131_p_regex_matches {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A .matches postcondition is proven from a matches precondition; a wrong character-class claim refutes.'

    static final List<Map> CASES = [

        // VerifyChecker reasons about regex matching semantically: `.matches(pattern)` lowers to Z3's
        // regex membership (str.in_re), so a matches postcondition is *proven* from a matches precondition,
        // and a wrong character class refutes (sound — [a-z] is not [A-Z]).
        [group: 'P regex matches', name: 'matches postcondition proven from matches precondition', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.matches("[a-z]+") })
                        @Ensures({ result.matches("[a-z]+") })
                        static String echo(String s) { s }
                    }''')],
        [group: 'P regex matches', name: 'wrong character-class matches postcondition refutes', ok: false, expect: 'Cannot prove',
         src: tc('''class C {
                        @Requires({ s != null && s.matches("[a-z]+") })
                        @Ensures({ result.matches("[A-Z]+") })
                        static String echo(String s) { s }
                    }''')],
    ]
}
