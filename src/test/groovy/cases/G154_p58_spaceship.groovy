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

/** 'P58 spaceship' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G154_p58_spaceship {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The spaceship <=> as a three-way comparator (-1/0/1 = Integer.compareTo); a contract over it verifies.'

    static final List<Map> CASES = [

        // ---------- Phase 58: spaceship operator `<=>` (three-way Int comparison) ----------
        // `a <=> b` is a correct three-way comparator: its sign matches the direct comparison.
        [group: 'P58 spaceship', name: 'spaceship is a correct three-way comparator', ok: true,
         src: tc('''class C {
                        @Ensures({ (result < 0) == (a < b) && (result == 0) == (a == b) &&
                                   (result > 0) == (a > b) })
                        static int cmp(int a, int b) { a <=> b }
                    }''')],
        // For a < b the spaceship is exactly -1 (Integer.compareTo semantics).
        [group: 'P58 spaceship', name: 'spaceship of a<b is -1', ok: true,
         src: tc('''class C {
                        @Requires({ a < b })
                        @Ensures({ result == -1 })
                        static int cmp(int a, int b) { a <=> b }
                    }''')],
        // Soundness: unconstrained, the spaceship isn't always 1.
        [group: 'P58 spaceship', name: 'spaceship is not always 1 (refutes)',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int cmp(int a, int b) { a <=> b }
                    }''')],
    ]
}
