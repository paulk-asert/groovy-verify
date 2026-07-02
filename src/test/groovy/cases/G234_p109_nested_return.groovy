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

/** 'P109 nested-return' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G234_p109_nested_return {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A nested (doubly-looped) search that returns a witness on a match verifies, and the in-body return\'s @Ensures is checked.'

    static final List<Map> CASES = [
        // ---------- P109 nested loop with an inner early return ----------
        // Phase 91 summarised a nested inner loop by havocking its writes + assuming `inner_inv ∧ ¬inner_guard`,
        // but bailed if the inner body contained a `return` (the write-set couldn't account for it). Phase 109:
        // a `return` writes nothing to outer state, so the summary's fall-through path is unaffected — and the
        // inner exit's @Ensures is discharged separately, with the inner loop's body-entry context
        // (`inner_inv ∧ inner_guard`), the same Phase-49b treatment applied to the inner site. So a 2D
        // witness-search returning an index from the inner loop verifies (partial correctness).
        [group: 'P109 nested-return', name: 'nested inner-return verifies', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == -1 || (0 <= result && result < a.length) })
                        static int firstDup(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                int j = i + 1
                                @Invariant({ 0 <= i && i < a.length && i + 1 <= j && j <= a.length })
                                @Decreases({ a.length - j })
                                while (j < a.length) {
                                    if (a[i] == a[j]) return j
                                    j = j + 1
                                }
                                i = i + 1
                            }
                            return -1
                        }
                    }''')],
        // Soundness control: the inner-return path yields j >= 1 > 0, so `result <= 0` must refute — proof
        // that the inner exit's @Ensures is genuinely checked, not skipped.
        [group: 'P109 nested-return', name: 'inner-return postcondition is checked', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result <= 0 })
                        static int firstDup(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                int j = i + 1
                                @Invariant({ 0 <= i && i < a.length && i + 1 <= j && j <= a.length })
                                @Decreases({ a.length - j })
                                while (j < a.length) {
                                    if (a[i] == a[j]) return j
                                    j = j + 1
                                }
                                i = i + 1
                            }
                            return -1
                        }
                    }''')],
    ]
}
