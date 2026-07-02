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

/** 'HE152 compare' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G251_he152_compare {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'HumanEval 152 — element-wise over two lists: each output is the absolute difference |game[i]-guess[i]| (abs as the body\'s conditional); the signed difference (no abs) refutes.'

    static final List<Map> CASES = [

        // 152 compare: each output is the absolute difference of the two inputs (abs spelled as the conditional the
        // body uses — Math.abs is modelled for FP only, and this keeps spec and code identical).
        [group: 'HE152 compare', name: 'every element is the absolute difference', ok: true,
         src: tc('''class C {
                        @Requires({ game != null && guess != null && game.size() == guess.size() })
                        @Ensures({ result.size() == game.size() &&
                                   (0..<game.size()).every { result[it] == (game[it] > guess[it] ? game[it] - guess[it] : guess[it] - game[it]) } })
                        static List<Integer> compare(List<Integer> game, List<Integer> guess) {
                            List<Integer> differences = []
                            int i = 0
                            @Invariant({ differences != null && 0 <= i && i <= game.size() && game.size() == guess.size() &&
                                         differences.size() == i &&
                                         (0..<i).every { differences[it] == (game[it] > guess[it] ? game[it] - guess[it] : guess[it] - game[it]) } })
                            @Decreases({ game.size() - i })
                            while (i < game.size()) {
                                int diff = game[i] > guess[i] ? game[i] - guess[i] : guess[i] - game[i]
                                differences.add(diff)
                                i = i + 1
                            }
                            return differences
                        }
                    }''')],
        // Soundness: the *signed* difference (forgetting the abs) refutes — it is negative when guess exceeds game.
        [group: 'HE152 compare', name: 'signed difference (no abs) refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ game != null && guess != null && game.size() == guess.size() })
                        @Ensures({ result.size() == game.size() &&
                                   (0..<game.size()).every { result[it] == game[it] - guess[it] } })
                        static List<Integer> compare(List<Integer> game, List<Integer> guess) {
                            List<Integer> differences = []
                            int i = 0
                            @Invariant({ differences != null && 0 <= i && i <= game.size() && game.size() == guess.size() &&
                                         differences.size() == i &&
                                         (0..<i).every { differences[it] == (game[it] > guess[it] ? game[it] - guess[it] : guess[it] - game[it]) } })
                            @Decreases({ game.size() - i })
                            while (i < game.size()) {
                                int diff = game[i] > guess[i] ? game[i] - guess[i] : guess[i] - game[i]
                                differences.add(diff)
                                i = i + 1
                            }
                            return differences
                        }
                    }''')],
    ]
}
