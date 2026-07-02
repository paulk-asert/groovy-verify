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

/** 'P85 compound assign' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G100_p85_compound_assign {

    static final List<Map> CASES = [

        // ---------- Phase 85: compound assignment operators (+= -= *= /= %=) ----------
        // A statement-level desugar `s += e` → `s = s + e`, applied in both the straight-line and loop
        // body processors — so the same variable / field / array-element assignment paths handle it.
        // (No overlap with contracts: contract closures are pure predicates and never contain assignments.)
        [group: 'P85 compound assign', name: 'sumProduct loop body with += *=', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result == xs.sum() + xs.inject(1) { a, x -> a * x } })
                        static int sumProduct(List<Integer> xs) {
                            int s = xs[0]
                            int p = xs[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= xs.size() &&
                                         s == xs[0..<i].sum() && p == xs[0..<i].inject(1) { a, x -> a * x } })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) { s += xs[i]; p *= xs[i]; i += 1 }
                            return s + p
                        }
                    }''')],
        [group: 'P85 compound assign', name: 'straight-line += then *=', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 6 })
                        static int f() { int s = 1; s += 2; s *= 2; s }
                    }''')],
        [group: 'P85 compound assign', name: 'straight-line -= symbolic', ok: true,
         src: tc('''class C {
                        @Requires({ x >= 3 })
                        @Ensures({ result == x - 3 })
                        static int f(int x) { int s = x; s -= 3; s }
                    }''')],
        [group: 'P85 compound assign', name: 'wrong compound result refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 5 })
                        static int f() { int s = 1; s += 2; s }
                    }''')],
        // Array-element compound assignment desugars to an array store.
        [group: 'P85 compound assign', name: 'array element a[i] += 1', ok: true,
         src: tc('''class C {
                        int[] a
                        @Requires({ a != null && 0 <= i && i < a.length })
                        @Ensures({ a[i] == old.a[i] + 1 })
                        void bump(int i) { a[i] += 1 }
                    }''')],
    ]
}
