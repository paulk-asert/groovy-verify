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

/** 'P38 factory' — 11 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G075_p38_factory {

    static final List<Map> CASES = [
        // ---------- Phase 38: immutable-container factory recognition ----------
        // List.of(...).size() folds to a literal count — usable as a ground int in @Ensures.
        [group: 'P38 factory', name: 'List.of(args).size() folds to literal', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() { List.of(1, 2, 3).size() }
                    }''')],
        // Soundness: List.of(1, 2, 3).size() is provably 3, not 4 — refute the wrong literal.
        [group: 'P38 factory', name: 'List.of size: wrong literal refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 4 })
                        static int f() { List.of(1, 2, 3).size() }
                    }''')],
        // Groovy list literal: same fold via the ListExpression branch.
        [group: 'P38 factory', name: 'Groovy [a, b, c].size() folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 2 })
                        static int f() { [10, 20].size() }
                    }''')],
        // .contains() over a list factory: disjunction over the entries.
        [group: 'P38 factory', name: 'List.of(...).contains folds to disjunction', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { List.of(1, 2, 3).contains(2) ? 1 : 0 }
                    }''')],
        // Soundness on contains: refute the wrong claim.
        [group: 'P38 factory', name: 'List.of(...).contains refutes wrong element',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { List.of(1, 2, 3).contains(99) ? 1 : 0 }
                    }''')],
        // `x in [...]` operator form, same lowering as .contains.
        [group: 'P38 factory', name: 'x in [a, b, c] operator folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { (2 in [1, 2, 3]) ? 1 : 0 }
                    }''')],
        // List.of(...).get(literal_i) folds to the literal element.
        [group: 'P38 factory', name: 'List.of(...).get(0) folds to first element', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 10 })
                        static int f() { List.of(10, 20, 30).get(0) }
                    }''')],
        // [...][i] bracket-access on a Groovy list literal also folds.
        [group: 'P38 factory', name: '[a, b, c][i] bracket fold for constant i', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 20 })
                        static int f() { [10, 20, 30][1] }
                    }''')],
        // Set.of factory: .size and .contains the same way (uniqueness of args not enforced —
        // dedup-aware sizing is a known limit).
        [group: 'P38 factory', name: 'Set.of(args).size folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() { Set.of(1, 2, 3).size() }
                    }''')],
        // Map.of factory: keys/values via containsKey / containsValue.
        [group: 'P38 factory', name: 'Map.of(...).containsKey folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { Map.of("a", 1, "b", 2).containsKey("a") ? 1 : 0 }
                    }''')],
        [group: 'P38 factory', name: 'Map.of(...).get(k) ite-chain folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 2 })
                        static int f() { Map.of("a", 1, "b", 2).get("b") }
                    }''')],
    ]
}
