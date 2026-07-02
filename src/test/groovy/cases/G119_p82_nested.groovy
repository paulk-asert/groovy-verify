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

/** 'P82 nested' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G119_p82_nested {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Nested tuples: .v1.v2 slot access in a body (and via a local).'

    static final List<Map> CASES = [

        // ---------- Phase 82: nested tuples ----------
        // Constructed/returned nested tuple — slot resolution recurses through the factory containers. Nested
        // access lives in the BODY: a *contract* closure erases the nested generic to Object (`result.v1.v2`
        // → Object.v2) under @TypeChecked, the same erasure as slot arithmetic / List<Double> elements.
        [group: 'P82 nested', name: 'constructed nested: .v1.v2 == 2 (body)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 2 })
                        static int m() { Tuple.tuple(Tuple.tuple(1, 2), 3).v1.v2 }
                    }''')],
        [group: 'P82 nested', name: 'constructed nested via local', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 2 })
                        static int m() {
                            def t = Tuple.tuple(Tuple.tuple(1, 2), 3)
                            t.v1.v2
                        }
                    }''')],
        [group: 'P82 nested', name: 'constructed nested: .v1.v1 == 1 (body)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int m() { Tuple.tuple(Tuple.tuple(1, 2), 3).v1.v1 }
                    }''')],
        // Nested tuple PARAMETER — t.v1.v2 flattens to a fresh entity t$v1$v2.
        [group: 'P82 nested', name: 'nested param: body access verifies', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f(Tuple2<Tuple2<Integer, Integer>, Integer> t) {
                            int x = t.v1.v2
                            x - x
                        }
                    }''')],
        [group: 'P82 nested', name: 'nested param: unconstrained slot refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 5 })
                        static int f(Tuple2<Tuple2<Integer, Integer>, Integer> t) { t.v1.v2 }
                    }''')],
    ]
}
