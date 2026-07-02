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

/** 'P47d regex extras' — 13 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G085_p47d_regex_extras {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Regex character classes \\d+ / \\w+ match/reject digit and alphanumeric strings.'

    static final List<Map> CASES = [

        // ---------- Phase 47d: regex feature expansion ----------
        // Predefined classes: \d, \w, \s.
        [group: 'P47d regex extras', name: '\\\\d+ matches digits', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "123".matches("\\\\d+") ? 1 : 0 }
                    }''')],
        [group: 'P47d regex extras', name: '\\\\d+ rejects letters',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "abc".matches("\\\\d+") ? 1 : 0 }
                    }''')],
        [group: 'P47d regex extras', name: '\\\\w+ matches alphanumeric+underscore', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "abc_123".matches("\\\\w+") ? 1 : 0 }
                    }''')],
        [group: 'P47d regex extras', name: '\\\\s+ matches whitespace', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "   ".matches("\\\\s+") ? 1 : 0 }
                    }''')],
        // Negated predefined: \D = non-digit.
        [group: 'P47d regex extras', name: '\\\\D+ rejects digits', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { "123".matches("\\\\D+") ? 1 : 0 }
                    }''')],
        // Negated character class.
        [group: 'P47d regex extras', name: '[^0-9]+ matches non-digits', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "abc".matches("[^0-9]+") ? 1 : 0 }
                    }''')],
        [group: 'P47d regex extras', name: '[^0-9]+ rejects digits',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "123".matches("[^0-9]+") ? 1 : 0 }
                    }''')],
        // Anchors as no-op (matches is whole-string anchored).
        [group: 'P47d regex extras', name: 'anchors are redundant no-ops', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "abc".matches("^abc\\$") ? 1 : 0 }
                    }''')],
        // Quantified range: a{3} matches exactly three.
        [group: 'P47d regex extras', name: 'a{3} matches exactly three', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "aaa".matches("a{3}") ? 1 : 0 }
                    }''')],
        [group: 'P47d regex extras', name: 'a{3} rejects two',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "aa".matches("a{3}") ? 1 : 0 }
                    }''')],
        // {n,m} range.
        [group: 'P47d regex extras', name: 'a{2,4} matches three', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "aaa".matches("a{2,4}") ? 1 : 0 }
                    }''')],
        [group: 'P47d regex extras', name: 'a{2,4} rejects five',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "aaaaa".matches("a{2,4}") ? 1 : 0 }
                    }''')],
        // {n,} unbounded.
        [group: 'P47d regex extras', name: 'a{2,} matches three', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "aaa".matches("a{2,}") ? 1 : 0 }
                    }''')],
    ]
}
