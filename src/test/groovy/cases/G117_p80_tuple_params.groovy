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

/** 'P80 tuple params' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G117_p80_tuple_params {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A tuple parameter\'s slots are read in the contract/body (homogeneous and heterogeneous).'

    static final List<Map> CASES = [

        // ---------- Phase 80: tuple PARAMETERS with .vN access ----------
        // A tuple parameter's slots are the caller's components — each `t.vN`/`t[k]` mints a fresh typed
        // entity `t$vN` in the slot's sort (like a Phase-45 object field). `.size()` folds to the arity.
        // Slot access flows to the body's return (arithmetic on slots lives in the body, where generics
        // survive — in the *contract* closure @TypeChecked erases the slot generic to Object, so contracts
        // use comparisons on slots, not arithmetic).
        [group: 'P80 tuple params', name: 'tuple param: result == t.v1', ok: true,
         src: tc('''class C {
                        @Ensures({ result == t.v1 })
                        static int firstOf(Tuple2<Integer, Integer> t) { t.v1 }
                    }''')],
        [group: 'P80 tuple params', name: 'tuple param: first/second + size', ok: true,
         src: tc('''class C {
                        @Requires({ t.first >= 0 && t.second >= 0 })
                        @Ensures({ result >= 0 && t.size() == 2 })
                        static int sum(Tuple2<Integer, Integer> t) { t.first + t.second }
                    }''')],
        // Heterogeneous tuple parameter: v1 Int, v2 String — each a distinct entity in its own sort.
        [group: 'P80 tuple params', name: 'tuple param: heterogeneous Int + String', ok: true,
         src: tc('''class C {
                        @Requires({ t.v2 == "hi" })
                        @Ensures({ result == t.v1 })
                        static int f(Tuple2<Integer, String> t) { t.v1 }
                    }''')],
        // Constant-index access on a tuple parameter.
        [group: 'P80 tuple params', name: 'tuple param: constant index t[0]', ok: true,
         src: tc('''class C {
                        @Ensures({ result == t[0] })
                        static int first(Tuple2<Integer, Integer> t) { t.v1 }
                    }''')],
        // Refute: v1 >= 0 does not give v1 > 0.
        [group: 'P80 tuple params', name: 'tuple param: v1>=0 does not prove v1>0', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ t.v1 >= 0 })
                        @Ensures({ result > 0 })
                        static int f(Tuple2<Integer, Integer> t) { t.v1 }
                    }''')],
    ]
}
