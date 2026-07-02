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

/** 'P110 tuple-exit' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G233_p110_tuple_exit {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A Tuple returned from a mid-loop early-exit (return Tuple.tuple(i,j)); a wrong slot order refutes.'

    static final List<Map> CASES = [
        // ---------- P110 tuple return on an early-exit path ----------
        // checkEarlyExit bound only a scalar `result`, so an early `return Tuple.tuple(i, j)` couldn't resolve
        // its slot accessors (`result.v1`/`.v2`) in the @Ensures. Phase 110 makes the early-exit binding
        // factory-aware (the same `tryRecordFactoryAssign` path checkUse uses on the natural return), so a
        // tuple/list/map return on a prefix / in-body / inner-loop exit folds its slots. Combined with the
        // Phase-109 nested inner-return, this lands the natural nested form of FoVeOOS *Duplets* `duplet`
        // (find a duplicate pair) at *partial correctness* — the witness-search shape the example is about.
        [group: 'P110 tuple-exit', name: 'nested duplet (tuple) partial correctness', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result.v1 == -1 || (0 <= result.v1 && result.v1 < result.v2 && result.v2 < a.length && a[result.v1] == a[result.v2]) })
                        static Tuple2<Integer, Integer> duplet(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                int j = i + 1
                                @Invariant({ 0 <= i && i < a.length && i + 1 <= j && j <= a.length })
                                @Decreases({ a.length - j })
                                while (j < a.length) {
                                    if (a[i] == a[j]) return Tuple.tuple(i, j)
                                    j = j + 1
                                }
                                i = i + 1
                            }
                            return Tuple.tuple(-1, -1)
                        }
                    }''')],
        // Refute control — claim v1 > v2 on the found path (false: i < j); must refute, proving the slots are
        // genuinely bound on the inner-exit path, not left free.
        [group: 'P110 tuple-exit', name: 'wrong slot order refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result.v1 == -1 || result.v1 > result.v2 })
                        static Tuple2<Integer, Integer> duplet(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                int j = i + 1
                                @Invariant({ 0 <= i && i < a.length && i + 1 <= j && j <= a.length })
                                @Decreases({ a.length - j })
                                while (j < a.length) {
                                    if (a[i] == a[j]) return Tuple.tuple(i, j)
                                    j = j + 1
                                }
                                i = i + 1
                            }
                            return Tuple.tuple(-1, -1)
                        }
                    }''')],
        // Generality: a single-loop early exit returning a tuple folds its slots too (not nested-specific).
        [group: 'P110 tuple-exit', name: 'single-loop tuple early-exit', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result.v1 == -1 || (0 <= result.v1 && result.v1 < a.length && a[result.v1] == target && result.v2 == target) })
                        static Tuple2<Integer, Integer> find(int[] a, int target) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= a.length })
                            @Decreases({ a.length - k })
                            while (k < a.length) {
                                if (a[k] == target) return Tuple.tuple(k, target)
                                k = k + 1
                            }
                            return Tuple.tuple(-1, -1)
                        }
                    }''')],
    ]
}
