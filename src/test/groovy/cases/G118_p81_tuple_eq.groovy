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

/** 'P81 tuple eq' — 7 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G118_p81_tuple_eq {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Component-wise tuple equality: equal constructed tuples prove equal, unequal refute.'

    static final List<Map> CASES = [

        // ---------- Phase 81: component-wise tuple / list == ----------
        // `a == b` over two fixed-arity products folds to the conjunction of pairwise component equalities
        // (and `!=` its negation); a length mismatch is false (Groovy's list/tuple equality).
        [group: 'P81 tuple eq', name: 'equal constructed tuples', ok: true,
         src: tc('''class C {
                        @Ensures({ Tuple.tuple(1, 2) == Tuple.tuple(1, 2) })
                        static void m() { }
                    }''')],
        [group: 'P81 tuple eq', name: 'unequal tuples refute', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ Tuple.tuple(1, 2) == Tuple.tuple(1, 3) })
                        static void m() { }
                    }''')],
        [group: 'P81 tuple eq', name: 'unequal tuples !=', ok: true,
         src: tc('''class C {
                        @Ensures({ Tuple.tuple(1, 2) != Tuple.tuple(1, 3) })
                        static void m() { }
                    }''')],
        // Two tuple parameters: equal components ⇒ equal tuples.
        [group: 'P81 tuple eq', name: 'two params: equal components ⇒ a == b', ok: true,
         src: tc('''class C {
                        @Requires({ a.v1 == b.v1 && a.v2 == b.v2 })
                        @Ensures({ a == b })
                        static void check(Tuple2<Integer, Integer> a, Tuple2<Integer, Integer> b) { }
                    }''')],
        // Tuple parameter vs a constructed tuple.
        [group: 'P81 tuple eq', name: 'param == constructed tuple', ok: true,
         src: tc('''class C {
                        @Requires({ t.v1 == 5 && t.v2 == 7 })
                        @Ensures({ t == Tuple.tuple(5, 7) })
                        static void check(Tuple2<Integer, Integer> t) { }
                    }''')],
        // Different arity ⇒ not equal.
        [group: 'P81 tuple eq', name: 'different arity refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ Tuple.tuple(1, 2) == Tuple.tuple(1, 2, 3) })
                        static void m() { }
                    }''')],
        // Bonus: the same fold gives list-literal equality.
        [group: 'P81 tuple eq', name: 'list literal equality', ok: true,
         src: tc('''class C {
                        @Ensures({ [1, 2, 3] == [1, 2, 3] })
                        static void m() { }
                    }''')],
    ]
}
