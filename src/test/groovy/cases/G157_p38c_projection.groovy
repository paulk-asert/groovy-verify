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

/** 'P38c projection' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G157_p38c_projection {

    static final List<Map> CASES = [

        // ---------- Phase 38c-3: keySet / values projections on map factories ----------
        // Map.of(...).keySet() returns a set factory of the keys; .contains folds via disjunction.
        [group: 'P38c projection', name: 'Map.of(...).keySet().contains folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { Map.of("a", 1, "b", 2).keySet().contains("a") ? 1 : 0 }
                    }''')],
        // Soundness: a key not in the map doesn't appear in the keySet projection.
        [group: 'P38c projection', name: 'Map.of(...).keySet().contains refutes for absent key',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { Map.of("a", 1, "b", 2).keySet().contains("z") ? 1 : 0 }
                    }''')],
        // Map.of(...).values() returns a list factory of the values; .contains folds.
        [group: 'P38c projection', name: 'Map.of(...).values().contains folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { Map.of("a", 10, "b", 20).values().contains(20) ? 1 : 0 }
                    }''')],
        // .size() on a keySet projection folds to the literal key count.
        [group: 'P38c projection', name: 'keySet().size() folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 2 })
                        static int f() { Map.of("a", 1, "b", 2).keySet().size() }
                    }''')],
    ]
}
