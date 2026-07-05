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

/** 'P57 monotonic' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G149_p57_monotonic {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'HumanEval 057 monotonic — a list is all-non-decreasing OR all-non-increasing (a disjunctive ∀∀ spec via dual existential flags).'

    static final List<Map> CASES = [

        // ---------- HumanEval 057 (monotonic): list is all-non-decreasing OR all-non-increasing ----------
        // A DISJUNCTIVE spec — `(∀ pair: l[j] <= l[j+1]) || (∀ pair: l[j] >= l[j+1])`. The scan tracks two flags;
        // each is a bounded EXISTENTIAL over the prefix (`increasing == ∃j<i. l[j] < l[j+1]`), carried in the
        // invariant. The in-body early return (both flags set ⇒ not monotonic) is the Phase-49b machinery.
        [group: 'P57 monotonic', name: 'monotonic verifies (disjunctive ∀∀ spec)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == (l.indices.every { it == 0 || l[it - 1] <= l[it] } ||
                                              l.indices.every { it == 0 || l[it - 1] >= l[it] }) })
                        static boolean monotonic(int[] l) {
                            if (l.length <= 1) return true
                            boolean increasing = false
                            boolean decreasing = false
                            int i = 0
                            @Invariant({ 0 <= i && i <= l.length - 1 &&
                                         !(increasing && decreasing) &&
                                         increasing == (0..<i).any { l[it] < l[it + 1] } &&
                                         decreasing == (0..<i).any { l[it] > l[it + 1] } })
                            @Decreases({ l.length - 1 - i })
                            while (i < l.length - 1) {
                                if (l[i] < l[i + 1]) increasing = true
                                else if (l[i] > l[i + 1]) decreasing = true
                                if (increasing && decreasing) return false
                                i = i + 1
                            }
                            return true
                        }
                    }''')],
        // Non-vacuousness control — claim only the non-decreasing half (drop the `|| non-increasing`). The body
        // returns true for an all-DECREASING list too, so the weaker spec is false there → refutes.
        [group: 'P57 monotonic', name: 'dropping the OR-decreasing disjunct refutes (proof is non-vacuous)',
         ok: false, expect: 'postcondition',
         src: tc('''class C {
                        @Ensures({ result == l.indices.every { it == 0 || l[it - 1] <= l[it] } })
                        static boolean monotonic(int[] l) {
                            if (l.length <= 1) return true
                            boolean increasing = false
                            boolean decreasing = false
                            int i = 0
                            @Invariant({ 0 <= i && i <= l.length - 1 &&
                                         !(increasing && decreasing) &&
                                         increasing == (0..<i).any { l[it] < l[it + 1] } &&
                                         decreasing == (0..<i).any { l[it] > l[it + 1] } })
                            @Decreases({ l.length - 1 - i })
                            while (i < l.length - 1) {
                                if (l[i] < l[i + 1]) increasing = true
                                else if (l[i] > l[i + 1]) decreasing = true
                                if (increasing && decreasing) return false
                                i = i + 1
                            }
                            return true
                        }
                    }''')],
    ]
}
