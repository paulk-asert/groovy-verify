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

/** 'P83 named-map' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G098_p83_named_map {

    static final List<Map> CASES = [

        // ---------- Phase 83: maps as named tuples (m.key / m['key'] on a returned map literal) ----------
        // A returned map literal binds `result` as a map factory (Phase 78); the property form `result.key`
        // folds to the value at that key (subscript `result['key']` already worked).
        [group: 'P83 named-map', name: 'map return: result.key property access', ok: true,
         src: tc('''class C {
                        @Ensures({ result.sum == 3 && result.product == 2 })
                        static Map<String, Integer> m() { [sum: 3, product: 2] }
                    }''')],
        [group: 'P83 named-map', name: 'map return: subscript form', ok: true,
         src: tc('''class C {
                        @Ensures({ result['sum'] == 3 && result['product'] == 2 })
                        static Map<String, Integer> m() { [sum: 3, product: 2] }
                    }''')],
        [group: 'P83 named-map', name: 'map return: wrong value refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result.sum == 99 })
                        static Map<String, Integer> m() { [sum: 3, product: 2] }
                    }''')],
        // The faithful HumanEval 008 (sum_product) as a NAMED-tuple map — the user's example.
        [group: 'P83 named-map', name: 'sum_product as a named-tuple map', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result.sum == xs.sum() && result.product == xs.inject(1) { a, x -> a * x } })
                        static Map<String, Integer> sumProduct(List<Integer> xs) {
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
                            return [sum: s, product: p]
                        }
                    }''')],
    ]
}
