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

/** 'P46e charAt' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G081_p46e_charat {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Literal s.charAt(i) folds (first/last position); a wrong literal refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 46e: charAt with per-position literal pinning + bounds ----------
        // Literal pinning: "hello".charAt(0) folds to 104 ('h' codepoint) via the mint pin. The
        // explicit (int) cast bridges Groovy's char-vs-int type distinction at the return.
        [group: 'P46e charAt', name: 'literal charAt at position 0', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 104 })
                        static int f() { (int) "hello".charAt(0) }
                    }''')],
        [group: 'P46e charAt', name: 'literal charAt at last position', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 111 })
                        static int f() { (int) "hello".charAt(4) }
                    }''')],
        // Wrong codepoint refutes — per-position pinning is exact.
        [group: 'P46e charAt', name: 'wrong literal charAt refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 65 })
                        static int f() { (int) "hello".charAt(0) }
                    }''')],
        // Bounds check: an out-of-bounds charAt index refutes with the IndexBounds diagnostic.
        [group: 'P46e charAt', name: 'out-of-bounds charAt refutes',
         expect: 'Possible IndexOutOfBoundsException',
         src: tc('''class C {
                        @Requires({ s != null && s.length() > 0 })
                        static int f(String s) { (int) s.charAt(s.length()) }
                    }''')],
        // Bounds check: a guarded charAt verifies.
        [group: 'P46e charAt', name: 'guarded charAt verifies', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.length() > 0 })
                        static int f(String s) { (int) s.charAt(0) }
                    }''')],
        // Symbolic charAt as a sentinel — equality through the uninterpreted function.
        [group: 'P46e charAt', name: 'charAt sentinel echoes assumption', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.length() > 0 && s.charAt(0) == 65 })
                        @Ensures({ result == 65 })
                        static int f(String s) { (int) s.charAt(0) }
                    }''')],
    ]
}
