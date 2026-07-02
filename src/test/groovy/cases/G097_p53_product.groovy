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

/** 'P53 product' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G097_p53_product {

    static final List<Map> CASES = [

        // ---------- Phase 53: product aggregation via the inject(1){a,x->a*x} fold ----------
        // A literal-bounded range product unfolds via the step axiom to the element product.
        [group: 'P53 product', name: 'range product unfolds to elements', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() >= 2 })
                        @Ensures({ xs[0..<2].inject(1) { a, x -> a * x } == xs[0] * xs[1] })
                        static void f(List<Integer> xs) { }
                    }''')],
        // The canonical loop-invariant proof: a running product equals the prefix product at each
        // step, so the returned value equals the whole-list product (the inject fold).
        [group: 'P53 product', name: 'running product equals list product', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result == xs.inject(1) { a, x -> a * x } })
                        static int product(List<Integer> xs) {
                            int p = xs[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= xs.size() &&
                                         p == xs[0..<i].inject(1) { a, x -> a * x } })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                p = p * xs[i]
                                i = i + 1
                            }
                            return p
                        }
                    }''')],
        // inject(0){a,x->a+x} is recognised as a sum fold too (same machinery, `+` instead of `*`).
        [group: 'P53 product', name: 'inject sum fold unfolds', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() >= 2 })
                        @Ensures({ xs[0..<2].inject(0) { a, x -> a + x } == xs[0] + xs[1] })
                        static void f(List<Integer> xs) { }
                    }''')],
        // HumanEval 8 (sum_product) shape: compute the sum AND the product in one loop, each proven
        // against its aggregate. (This variant returns `s + p` to expose both in one int; the faithful
        // `return [sum, product]` version is in the P78 group, now that list returns are modelled.)
        [group: 'P53 product', name: 'sum_product: both aggregations in one loop', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result == xs.sum() + xs.inject(1) { a, x -> a * x } })
                        static int sumPlusProduct(List<Integer> xs) {
                            int s = xs[0]
                            int p = xs[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= xs.size() &&
                                         s == xs[0..<i].sum() &&
                                         p == xs[0..<i].inject(1) { a, x -> a * x } })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                s = s + xs[i]
                                p = p * xs[i]
                                i = i + 1
                            }
                            return s + p
                        }
                    }''')],
    ]
}
