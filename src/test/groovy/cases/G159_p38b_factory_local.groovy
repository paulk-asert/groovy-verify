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

/** 'P38b factory local' — 7 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G159_p38b_factory_local {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The factory folds lift across a local binding (xs = List.of(...); xs.size()).'

    static final List<Map> CASES = [

        // ---------- Phase 38b: factory through assignment ----------
        // The Phase 38 known limit closed: a local bound to a factory carries the fold across the
        // variable boundary. xs = List.of(args); xs.size() now folds the same as the inline form.
        [group: 'P38b factory local', name: 'xs = List.of(...); xs.size() folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() {
                            List<Integer> xs = List.of(1, 2, 3)
                            xs.size()
                        }
                    }''')],
        // Soundness anchor: the wrong literal refutes.
        [group: 'P38b factory local', name: 'xs = List.of(...); xs.size() wrong literal refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 4 })
                        static int f() {
                            List<Integer> xs = List.of(1, 2, 3)
                            xs.size()
                        }
                    }''')],
        // Groovy list literal through assignment: bracket-indexed access folds via the recorded factory.
        [group: 'P38b factory local', name: 'xs = [a, b, c]; xs[1] folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 20 })
                        static int f() {
                            List<Integer> xs = [10, 20, 30]
                            xs[1]
                        }
                    }''')],
        // .contains through assignment: disjunction over recorded elements.
        [group: 'P38b factory local', name: 'xs = List.of(...); xs.contains folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() {
                            List<Integer> xs = List.of(1, 2, 3)
                            xs.contains(2) ? 1 : 0
                        }
                    }''')],
        // `x in xs` operator through assignment.
        [group: 'P38b factory local', name: 'x in xs operator across assignment', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() {
                            List<Integer> xs = [1, 2, 3]
                            (2 in xs) ? 1 : 0
                        }
                    }''')],
        // Map factory through assignment: containsKey + get fold both lift across the variable.
        [group: 'P38b factory local', name: 'm = Map.of(...); m.containsKey + m.get fold', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 2 })
                        static int f() {
                            Map<String, Integer> m = Map.of("a", 1, "b", 2)
                            m.containsKey("b") ? m.get("b") : 0
                        }
                    }''')],
        // Set factory through assignment: .size folds.
        [group: 'P38b factory local', name: 's = Set.of(...); s.size folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() {
                            Set<Integer> s = Set.of(1, 2, 3)
                            s.size()
                        }
                    }''')],
    ]
}
