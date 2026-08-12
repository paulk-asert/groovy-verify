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

/** 'P79 tuples' — 9 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G105_p79_tuples {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Tuple/TupleN fixed-arity typed products with .vN slot access (and first/second/size), heterogeneous slots.'

    static final List<Map> CASES = [

        // ---------- Phase 79: Tuple / TupleN — fixed-arity typed products ----------
        // A `Tuple.tuple(a, b)` / `new TupleN(a, b)` is modelled as a fixed-arity factory (on the Phase-78
        // foundation), so a returned tuple binds `result` and its slots fold: `.v1`/`.vN`, `.first`/`.second`,
        // `.getVN()`, constant-index `[k]`, and `.size()`. Heterogeneous slots translate in their own sort.
        [group: 'P79 tuples', name: 'return Tuple.tuple(10,20): .v1/.v2', ok: true,
         src: tc('''class C {
                        @Ensures({ result.v1 == 10 && result.v2 == 20 })
                        static Tuple2<Integer, Integer> pair() { Tuple.tuple(10, 20) }
                    }''')],
        [group: 'P79 tuples', name: 'tuple accessors: [k], first/second, size', ok: true,
         src: tc('''class C {
                        @Ensures({ result[0] == 10 && result.first == 10 && result.second == 20 &&
                                   result.getV2() == 20 && result.size() == 2 })
                        static Tuple2<Integer, Integer> pair() { Tuple.tuple(10, 20) }
                    }''')],
        // new TupleN constructor form, heterogeneous slots (Integer + String) each in their own sort.
        [group: 'P79 tuples', name: 'new Tuple2(1, "hi"): heterogeneous slots', ok: true,
         src: tc('''class C {
                        @Ensures({ result.v1 == 1 && result.v2 == "hi" })
                        static Tuple2<Integer, String> pair() { new Tuple2<Integer, String>(1, "hi") }
                    }''')],
        // The faithful HumanEval 008 (sum_product) as a TYPED tuple return.
        [group: 'P79 tuples', name: 'sum_product returns Tuple2(sum, product)', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result.v1 == xs.sum() && result.v2 == xs.inject(1) { a, x -> a * x } })
                        static Tuple2<Integer, Integer> sumProduct(List<Integer> xs) {
                            int s = xs[0]
                            int p = xs[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= xs.size() &&
                                         s == xs[0..<i].sum() &&
                                         p == xs[0..<i].inject(1) { a, x -> a * x } })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) { s += xs[i]; p *= xs[i]; i += 1 }
                            return Tuple.tuple(s, p)
                        }
                    }''')],
        // A false slot claim refutes (.v1 is 10, not 20).
        [group: 'P79 tuples', name: 'tuple wrong slot claim refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result.v1 == 20 })
                        static Tuple2<Integer, Integer> pair() { Tuple.tuple(10, 20) }
                    }''')],
        // Multiple assignment `def (a, b) = …` desugars to a temp + constant-index slot reads.
        [group: 'P79 tuples', name: 'multiple assignment from a tuple', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 30 })
                        static int m() {
                            def (a, b) = Tuple.tuple(10, 20)
                            a + b
                        }
                    }''')],
        [group: 'P79 tuples', name: 'multiple assignment from a list literal', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int m() {
                            def (a, b) = [1, 2]
                            a + b
                        }
                    }''')],
        [group: 'P79 tuples', name: 'multiple assignment wrong sum refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 99 })
                        static int m() {
                            def (a, b) = [1, 2]
                            a + b
                        }
                    }''')],
        // Typed components: since Groovy 6.0.0-beta-2 (GROOVY-12228) STC honours each target's declared type
        // (previously typed from the RHS component). The desugar is name-based and type-blind
        // (BodyEncoder.tupleMultiAssign), so the proof is identical either way — this pins that the typed
        // spelling stays green across the STC change.
        [group: 'P79 tuples', name: 'multiple assignment with typed int components', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 30 })
                        static int m() {
                            def (int a, int b) = Tuple.tuple(10, 20)
                            a + b
                        }
                    }''')],
    ]
}
