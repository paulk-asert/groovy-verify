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

/** 'P49b in-body exits' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G092_p49b_in_body_exits {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'An if(cond) return e at the top of a loop body is verified on its own path; preservation holds on the no-exit path.'

    static final List<Map> CASES = [

        // ---------- Phase 49b (Slice B): early-return INSIDE a loop body ----------
        // The in-body return path: its @Ensures verifies under invariant ∧ guard ∧
        // ¬prior-in-body-guards ∧ this-guard, with result bound to the exit value.
        // The loop's preservation / progress fire on the "no exit fired" path
        // (¬each-in-body-guard assumed during the body walk).
        [group: 'P49b in-body exits', name: 'single in-body early-return verifies', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) {
                                if (i == 5) return 42
                                i = i + 1
                            }
                            return i
                        }
                    }''')],
        // Soundness: an in-body return whose value violates the postcondition refutes.
        [group: 'P49b in-body exits', name: 'in-body return postcondition violation refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) {
                                if (i == 5) return -1
                                i = i + 1
                            }
                            return i
                        }
                    }''')],
        // Preservation under in-body exit: the body's normal-continuation path keeps the
        // invariant. The {@code i++} still happens on the no-exit path.
        [group: 'P49b in-body exits', name: 'preservation holds on no-exit body path', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result >= -1 })
                        static int firstNegativeIndex(List<Integer> xs) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= xs.size() })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                if (xs[i] < 0) return i
                                i = i + 1
                            }
                            return -1
                        }
                    }''')],
        // Multiple in-body exits: each verified independently; ¬prior-guards assumed for later ones.
        [group: 'P49b in-body exits', name: 'multiple stacked in-body returns', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) {
                                if (i == 3) return 100
                                if (i == 7) return 200
                                i = i + 1
                            }
                            return i
                        }
                    }''')],
    ]
}
