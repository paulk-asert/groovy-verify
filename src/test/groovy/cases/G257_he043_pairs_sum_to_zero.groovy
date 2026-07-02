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

/** 'HE043 pairs_sum_to_zero' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G257_he043_pairs_sum_to_zero {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'HumanEval 043 — is there a pair summing to zero: the nested-existential biconditional verifies via a seen.contains rewrite (the Verus break is unsupported) and a \'no pair so far\' invariant; an always-true checker refutes on the empty list.'

    static final List<Map> CASES = [

        // ---------- 043 pairs_sum_to_zero (HumanEval) — EXPERIMENT: is there a pair summing to zero? ----------
        // The Verus original uses a nested loop with a `break` over a GROWING `seen` accumulator; rewritten here with
        // `seen.contains(-l[i])` (break unsupported). The full spec is a nested existential, and proving the
        // `return false` direction needs a nested "no pair so far" invariant. This is the edge of the fragment.
        [group: 'HE043 pairs_sum_to_zero', name: 'a pair sums to zero (nested existential)', ok: true,
         src: tc('''class C {
                        @Requires({ l != null })
                        @Ensures({ result == (0..<l.size()).any { i -> (0..<i).any { j -> l[i] + l[j] == 0 } } })
                        static boolean pairsSumToZero(List<Integer> l) {
                            List<Integer> seen = []
                            int i = 0
                            @Invariant({ seen != null && 0 <= i && i <= l.size() && seen.size() == i &&
                                         (0..<i).every { seen[it] == l[it] } &&
                                         (0..<i).every { a -> (0..<a).every { b -> l[a] + l[b] != 0 } } })
                            @Decreases({ l.size() - i })
                            while (i < l.size()) {
                                if (seen.contains(-l[i])) return true
                                seen.add(l[i])
                                i = i + 1
                            }
                            return false
                        }
                    }''')],
        // Non-vacuity: a checker that always answers "yes" is wrong on the empty list (no pair exists there) — refutes.
        [group: 'HE043 pairs_sum_to_zero', name: 'always-true checker refutes (empty list has no pair)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ l != null })
                        @Ensures({ result == (0..<l.size()).any { i -> (0..<i).any { j -> l[i] + l[j] == 0 } } })
                        static boolean pairsSumToZero(List<Integer> l) {
                            return true
                        }
                    }''')],
    ]
}
