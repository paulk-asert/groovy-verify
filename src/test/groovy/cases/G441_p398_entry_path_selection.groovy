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

/**
 * 'P398 entry-path selection' — a witness is sought along at most 32 exact paths from entry. They were the shortest,
 * which for nested loops are all within the outer loop's first iteration, so a failure needing a later outer
 * iteration had its call withheld. When the shortest find none, a second pass now tries 32 more chosen by iterations:
 * runs whose completed loops all ran alike, with every loop part-way below that (as loops sharing a bound do), fewest
 * iterations of any one loop first. A call found before is found as before.
 */
class G441_p398_entry_path_selection {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 398: when the shortest entry paths give no witness, a second pass chosen by iterations (uniform completed loops, fewest iterations first) finds runs past the outer loop's first iteration."

    static final List<Map> CASES = [

        // Before: no call — the shortest paths stopped at the outer loop's first iteration; f(2) returns -1 at i == j == 1.
        [group: "P398 entry-path selection", name: "a return at a later outer iteration gets its run",
         expect: ["Cannot prove postcondition of f", "fails on: f(2)"],
         src: tc('''class A {
                            @Requires({ n >= 0 })
                            @Ensures({ result >= 0 })
                            static int f(int n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    int j = 0
                                    @Invariant({ 0 <= j && j <= n })
                                    @Decreases({ n - j })
                                    while (j < n) {
                                        if (i == 1 && j == 1) return -1
                                        j = j + 1
                                    }
                                    i = i + 1
                                }
                                return 0
                            }
                        }''')],

        // Before: no call. The i == 2 pass sets s = -1, so the inner entry at i == 3 breaks `i < 2 || s >= 0`.
        [group: "P398 entry-path selection", name: "… a nested entry broken on a later outer iteration",
         expect: ["Cannot prove loop invariant holds on entry in f", "fails on: f(4)"],
         src: tc('''class A {
                            @Requires({ n >= 0 })
                            static int f(int n) {
                                int s = 0
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    int j = 0
                                    @Invariant({ 0 <= j && j <= n && (i < 2 || s >= 0) })
                                    @Decreases({ n - j })
                                    while (j < n) {
                                        if (i == 2 && j == 1) s = -1
                                        j = j + 1
                                    }
                                    i = i + 1
                                }
                                return s
                            }
                        }''')],

        // Before: no call (Phase 397's boundary); f(2) reaches i == j == k == 1.
        [group: "P398 entry-path selection", name: "… and a return three loops down",
         expect: ["Cannot prove postcondition of f", "fails on: f(2)"],
         src: tc('''class A {
                            @Requires({ n >= 0 })
                            @Ensures({ result >= 0 })
                            static int f(int n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= n })
                                @Decreases({ n - i })
                                while (i < n) {
                                    int j = 0
                                    @Invariant({ 0 <= j && j <= n })
                                    @Decreases({ n - j })
                                    while (j < n) {
                                        int k = 0
                                        @Invariant({ 0 <= k && k <= n })
                                        @Decreases({ n - k })
                                        while (k < n) {
                                            if (i == 1 && j == 1 && k == 1) return -1
                                            k = k + 1
                                        }
                                        j = j + 1
                                    }
                                    i = i + 1
                                }
                                return 0
                            }
                        }''')],
    ]
}
