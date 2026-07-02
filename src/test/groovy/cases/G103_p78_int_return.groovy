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

/** 'P78 int[] return' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G103_p78_int_return {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'An int[] return accepts a coerced [a,b] / new int[]{a,b} with constant-index result[k] and .length; a wrong length refutes.'

    static final List<Map> CASES = [

        // The SAME returns through a declared `int[]` type (not List). Groovy implicitly coerces the body's
        // list literal `[s, p]` to int[], and the result-binding keys off the return EXPRESSION (a
        // ListExpression), so `result` binds as a list factory exactly as the List<Integer> form does —
        // result[k] / result.length fold, independent of the declared array type. No code beyond Phase 78
        // was needed; these lock the int[]-return shape in (it previously worked only untested).
        [group: 'P78 int[] return', name: '[a,b] coerced to int[]: result[k] + length', ok: true,
         src: tc('''class C {
                        @Ensures({ result.length == 2 && result[0] == a && result[1] == b })
                        static int[] pair(int a, int b) { [a, b] }
                    }''')],
        // Crisp refute: the size pin (factory entry count) makes a wrong `.length` UNSAT. Kept axiom-free
        // (no aggregation) so the refute is a clean counterexample, not the refute-hostile timeout the
        // inject/sum axioms produce (the gcd/fib aggregation-helper property: prove-friendly, refute-hostile).
        [group: 'P78 int[] return', name: 'int[] return: wrong length refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result.length == 3 })
                        static int[] pair(int a, int b) { [a, b] }
                    }''')],
        // Flagship: HumanEval 008 sum_product with an int[] return — the List<Integer> sibling above, now
        // array-typed. Both aggregates proven element-wise off the loop invariant (sum + inject product).
        [group: 'P78 int[] return', name: 'sum_product returns int[] [sum, product]', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result[0] == xs.sum() && result[1] == xs.inject(1) { a, x -> a * x } })
                        static int[] sumProduct(List<Integer> xs) {
                            int s = xs[0], p = xs[0], i = 1
                            @Invariant({ 1 <= i && i <= xs.size() &&
                                         s == xs[0..<i].sum() && p == xs[0..<i].inject(1) { a, x -> a * x } })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) { s += xs[i]; p *= xs[i]; i += 1 }
                            [s, p]   // also: new int[]{s, p}
                        }
                    }''')],
        // The CONSTRUCTED array-literal form `new int[]{...}` (an ArrayExpression with an initializer) — the
        // array dual of a list literal. Recognised as a fixed-arity list-kind factory over its initializer
        // expressions, so result[k] / result.length fold exactly as the coerced `[a,b]` form does.
        [group: 'P78 int[] return', name: 'new int[]{a,b} return: result[k] + length', ok: true,
         src: tc('''class C {
                        @Ensures({ result.length == 2 && result[0] == a && result[1] == b })
                        static int[] pair(int a, int b) { new int[]{a, b} }
                    }''')],
        // Crisp refute (int elements, no aggregation axiom): result[0] is a, not b.
        [group: 'P78 int[] return', name: 'new int[]{a,b} return: wrong element refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result[0] == b })
                        static int[] pair(int a, int b) { new int[]{a, b} }
                    }''')],
        // A body local bound to `new int[]{...}` records as a factory too (tryRecordFactoryAssign on the
        // local), so the returned local's elements/length fold without any array store.
        [group: 'P78 int[] return', name: 'new int[]{...} local, returned', ok: true,
         src: tc('''class C {
                        @Ensures({ result.length == 3 && result[0] == x && result[2] == x })
                        static int[] triple(int x) { int[] r = new int[]{x, x, x}; r }
                    }''')],
    ]
}
