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

/** 'P38c symbolic i' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G158_p38c_symbolic_i {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A factory container indexed by a symbolic i in range folds; without the bound it refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 38c-4: non-constant-i ite-chain for factory list indexing ----------
        // Symbolic i in range: the ite-chain returns one of the literal elements; the disjunctive
        // @Ensures covers all three branches.
        [group: 'P38c symbolic i', name: 'List.of(...)[i] for symbolic i in range', ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= i && i < 3 })
                        @Ensures({ result == 10 || result == 20 || result == 30 })
                        static int f(int i) { [10, 20, 30][i] }
                    }''')],
        // Soundness anchor: without the @Requires constraint on i, the ite-chain's default branch
        // (an unconstrained int) makes the @Ensures refute.
        [group: 'P38c symbolic i', name: 'List.of(...)[i] without bound refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 10 || result == 20 || result == 30 })
                        static int f(int i) { [10, 20, 30][i] }
                    }''')],
        // Composes with factory-through-assignment: local factory, symbolic index, bounded by
        // the (pinned) size oracle from Phase 38b.
        [group: 'P38c symbolic i', name: 'xs = List.of(...); xs[i] for symbolic i in range', ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= i && i < 3 })
                        @Ensures({ result == 10 || result == 20 || result == 30 })
                        static int f(int i) {
                            List<Integer> xs = List.of(10, 20, 30)
                            xs[i]
                        }
                    }''')],
    ]
}
