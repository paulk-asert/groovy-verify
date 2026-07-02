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

/** 'P46b string length' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G079_p46b_string_length {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'String .length()/.size() pinned for literals and equated; a wrong literal length refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 46b: string length oracle with literal pinning ----------
        // Literal pinning: "hello".length() == 5 folds via the mint-time pin.
        [group: 'P46b string length', name: 'literal length pinned', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 5 })
                        static int f() { "hello".length() }
                    }''')],
        // GDK alias size() on a String routes to length too — Groovy treats them as synonyms.
        [group: 'P46b string length', name: 'String size() == length()', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 5 })
                        static int f() { "hello".size() }
                    }''')],
        // Wrong length refutes — the pinning is exact.
        [group: 'P46b string length', name: 'wrong literal length refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 4 })
                        static int f() { "hello".length() }
                    }''')],
        // s.isEmpty() lowered to length(s) == 0 — both expressions resolve to the same term.
        [group: 'P46b string length', name: 'isEmpty <=> length == 0', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.isEmpty() })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.length() }
                    }''')],
    ]
}
