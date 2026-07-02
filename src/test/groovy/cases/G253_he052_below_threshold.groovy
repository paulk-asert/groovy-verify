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

/** 'HE052 below_threshold' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G253_he052_below_threshold {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'HumanEval 052 — boolean predicate over a list: true iff every element is below t; the early return-false witnesses the negated quantifier, and an off-by-one (<= t) refutes.'

    static final List<Map> CASES = [

        // ---------- 052 below_threshold (HumanEval) — a boolean predicate over a list: are ALL elements below t ----------
        // The early `return false` witnesses the negation of the `every` at the offending index (the 072 palindrome shape,
        // with the simpler element predicate `l[it] < t`).
        [group: 'HE052 below_threshold', name: 'true iff every element is below the threshold', ok: true,
         src: tc('''class C {
                        @Requires({ l != null })
                        @Ensures({ result == (0..<l.size()).every { l[it] < t } })
                        static boolean belowThreshold(List<Integer> l, int t) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= l.size() && (0..<i).every { l[it] < t } })
                            @Decreases({ l.size() - i })
                            while (i < l.size()) {
                                if (l[i] >= t) return false
                                i = i + 1
                            }
                            return true
                        }
                    }''')],
        // Soundness: an off-by-one using `<= t` instead of `< t` admits an element equal to t — refutes (kept straight-
        // line so the refutation lands cleanly).
        [group: 'HE052 below_threshold', name: 'off-by-one (<= t) refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ l != null })
                        @Ensures({ result == (0..<l.size()).every { l[it] < t } })
                        static boolean belowThreshold(List<Integer> l, int t) {
                            return (0..<l.size()).every { l[it] <= t }
                        }
                    }''')],
    ]
}
