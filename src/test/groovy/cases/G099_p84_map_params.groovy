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

/** 'P84 map params' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G099_p84_map_params {

    static final List<Map> CASES = [

        // ---------- Phase 84: map PARAMETERS with .key access ----------
        // `m.key` (property) on a map param routes to the value array — `m.sum` ≡ `m['sum']`. The caller's
        // map, so each key is a fresh entity in the value sort (consistent: same key → same value).
        [group: 'P84 map params', name: 'map param: m.sum property == precondition', ok: true,
         src: tc('''class C {
                        @Requires({ m.sum == 3 })
                        @Ensures({ result == 3 })
                        static int f(Map<String, Integer> m) { m.sum }
                    }''')],
        [group: 'P84 map params', name: 'map param: subscript form still works', ok: true,
         src: tc('''class C {
                        @Requires({ m['sum'] == 3 })
                        @Ensures({ result == 3 })
                        static int f(Map<String, Integer> m) { m['sum'] }
                    }''')],
        // Key arithmetic lives in the body (contract closures erase the value generic to Object, so `m.x +
        // m.y` won't compile there — the same @TypeChecked limit as tuple slots / List<Double>).
        [group: 'P84 map params', name: 'map param: keys in body arithmetic', ok: true,
         src: tc('''class C {
                        @Requires({ m.x >= 5 && m.y >= 5 })
                        @Ensures({ result >= 10 })
                        static int f(Map<String, Integer> m) { m.x + m.y }
                    }''')],
        [group: 'P84 map params', name: 'map param: wrong value refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ m.sum == 3 })
                        @Ensures({ result == 4 })
                        static int f(Map<String, Integer> m) { m.sum }
                    }''')],

        // Regression (Phase 84 fix): a property access on a RAW `Map` (non-String / unknown key sort) must
        // skip loudly, NOT crash Z3 with a key-domain sort mismatch. (Named-argument maps land here: raw
        // `Map`, Object values — at odds with @TypeChecked, so not verifiable; the point is it can't crash.)
        [group: 'P84 map params', name: 'raw Map property skips, no crash', expect: 'outside fragment',
         src: tc('''class C {
                        @Requires({ m.foo == 0 })
                        @Ensures({ result == 0 })
                        static int f(Map m) { 0 }
                    }''')],
    ]
}
