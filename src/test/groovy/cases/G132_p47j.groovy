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

/** 'P47j ==~' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G132_p47j {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Groovy\'s ==~ match operator reflects the match and is equivalent to .matches; a false claim refutes.'

    static final List<Map> CASES = [
        [group: 'P47j ==~', name: '==~ result reflects the match', ok: true,
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ result == (s ==~ /[a-z]+/) })
                        static boolean f(String s) { s ==~ /[a-z]+/ }
                    }''')],
        [group: 'P47j ==~', name: '==~ provably equivalent to .matches', ok: true,
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ (s ==~ /[a-z]+/) == s.matches("[a-z]+") })
                        static void f(String s) { }
                    }''')],
        [group: 'P47j ==~', name: '==~ false claim refutes', ok: false, expect: 'Cannot prove',
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ s ==~ /[a-z]+/ })
                        static void f(String s) { }
                    }''')],
    ]
}
