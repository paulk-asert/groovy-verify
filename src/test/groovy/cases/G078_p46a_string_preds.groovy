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

/** 'P46a string preds' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G078_p46a_string_preds {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'String predicates (startsWith/endsWith/contains) as uninterpreted Bool functions; a contract assumption flows, and contains routes to the string (not list) predicate.'

    static final List<Map> CASES = [

        // ---------- Phase 46a: string predicates as uninterpreted Bool functions ----------
        // startsWith on a String parameter — proves a precondition that names the predicate.
        // The receiver routing kicks in via scalarTypes (s: String parameter).
        [group: 'P46a string preds', name: 'startsWith on String param: contract assumption flows', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.startsWith("foo") })
                        @Ensures({ result == 1 })
                        static int hasFooPrefix(String s) { s.startsWith("foo") ? 1 : 0 }
                    }''')],
        // Distinct predicates aren't equated — startsWith vs endsWith are independent functions.
        [group: 'P46a string preds', name: 'startsWith and endsWith are independent',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s != null && s.startsWith("foo") })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.endsWith("bar") ? 1 : 0 }
                    }''')],
        // contains/isEmpty route through the same dispatch — disambiguated from list semantics
        // by the scalarTypes check (which sees s: String, not List).
        [group: 'P46a string preds', name: 'String contains routes to string predicate (not list existential)', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.contains("admin") })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.contains("admin") ? 1 : 0 }
                    }''')],
        [group: 'P46a string preds', name: 'String isEmpty as unary predicate', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.isEmpty() })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.isEmpty() ? 1 : 0 }
                    }''')],
        // Routing on List<String>[i] — xs[i].startsWith(p) for List<String> xs.
        [group: 'P46a string preds', name: 'startsWith on xs[i] for List<String>', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] != null && xs[0].startsWith("foo") })
                        @Ensures({ result == 1 })
                        static int f(List<String> xs) { xs[0].startsWith("foo") ? 1 : 0 }
                    }''')],
    ]
}
