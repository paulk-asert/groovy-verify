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
 * 'P319 majority' — gap 4 of the LemmaScript ports. Boyer–Moore majority (majority.ts) counts occurrences in a prefix,
 * which Phase 208's range count already supported; what stopped it was that its second loop forgot what the first
 * had established (Phase 207 had every later loop restate it). A later loop now keeps an earlier loop's exit facts
 * it leaves alone, and the trailing if/else return majority.ts ends with is read as its ternary.
 */
class G364_p319_majority {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 319 Boyer–Moore majority (gap 4 of the LemmaScript ports): majority.ts verifies verbatim, occOf(arr, x, n) spelt arr[0..<n].count(x) and its unbounded quantifiers ranged over the array\'s own values. Two engine changes: a later loop keeps an earlier loop\'s exit facts (each invariant conjunct and the negated guard) that neither it nor the code between writes, as in Dafny, where Phase 207 had every later loop restate them; and a trailing if/else (else-if chains too) both of whose branches return is read as the matching ternary. Boundary: a wrong claim under the quantified count axioms comes back undecided, not with a counterexample.'

    static final List<Map> CASES = [

        // LemmaScript's majority.ts, structure for structure: occOf(arr, x, n) is arr[0..<n].count(x). Its two
        // unbounded quantifiers range over the array's own values (a value that never occurs has count 0), and
        // cnt <= i covers those.
        [group: 'P319 majority', name: 'majority.ts, verbatim: Boyer-Moore majority vote', ok: true,
         src: tc('''class C {
                        /** Returns the value occurring in more than half of arr, or -1 when there is none. */
                        @Requires({ arr != null && arr.every { int k -> k >= 0 } })
                        @Ensures({ result == -1 || (result >= 0 && 2 * arr[0..<arr.length].count(result) > arr.length) })
                        @Ensures({ arr.any { int x -> 2 * arr[0..<arr.length].count(x) > arr.length } ==> result != -1 })
                        static int majority(int[] arr) {
                            int cand = 0
                            int cnt = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= arr.length && cnt >= 0 && cnt <= i && cand >= 0 })
                            @Invariant({ 2 * arr[0..<i].count(cand) <= i + cnt })
                            @Invariant({ arr.every { int y -> y == cand || 2 * arr[0..<i].count(y) <= i - cnt } })
                            @Decreases({ arr.length - i })
                            while (i < arr.length) {
                                if (cnt == 0) {
                                    cand = arr[i]
                                    cnt = 1
                                } else if (arr[i] == cand) {
                                    cnt = cnt + 1
                                } else {
                                    cnt = cnt - 1
                                }
                                i = i + 1
                            }
                            int occ = 0
                            int j = 0
                            @Invariant({ 0 <= j && j <= arr.length && occ == arr[0..<j].count(cand) })
                            @Decreases({ arr.length - j })
                            while (j < arr.length) {
                                if (arr[j] == cand) {
                                    occ = occ + 1
                                }
                                j = j + 1
                            }
                            if (2 * occ > arr.length) {
                                return cand
                            } else {
                                return -1
                            }
                        }
                    }''')],
        // Pass 1 on its own: the candidate and the others invariants preserve each other. Neither alone is inductive.
        [group: 'P319 majority', name: 'pass 1 alone: the counting invariants are inductive', ok: true,
         src: tc('''class C {
                        @Requires({ arr != null })
                        static int pick(int[] arr) {
                            int cand = 0
                            int cnt = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= arr.length && cnt >= 0 && cnt <= i })
                            @Invariant({ 2 * arr[0..<i].count(cand) <= i + cnt })
                            @Invariant({ arr.every { int y -> y == cand || 2 * arr[0..<i].count(y) <= i - cnt } })
                            @Decreases({ arr.length - i })
                            while (i < arr.length) {
                                if (cnt == 0) {
                                    cand = arr[i]
                                    cnt = 1
                                } else if (arr[i] == cand) {
                                    cnt = cnt + 1
                                } else {
                                    cnt = cnt - 1
                                }
                                i = i + 1
                            }
                            return cand
                        }
                    }''')],
        // Pass 2 on its own: the prefix count steps with the loop (Phase 208's range-count axioms).
        [group: 'P319 majority', name: 'pass 2 alone: occOf as a prefix count', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == a[0..<a.length].count(v) })
                        static int occ(int[] a, int v) {
                            int c = 0
                            int j = 0
                            @Invariant({ 0 <= j && j <= a.length && c == a[0..<j].count(v) })
                            @Decreases({ a.length - j })
                            while (j < a.length) {
                                if (a[j] == v) { c = c + 1 }
                                j = j + 1
                            }
                            return c
                        }
                    }''')],
        // The second loop never writes s or i, so the first loop's s == 2 * i and i == n hold after both, unrestated.
        [group: 'P319 majority', name: 'a later loop keeps an earlier loop\'s exit facts', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == 2 * n })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s == 2 * i })
                            @Decreases({ n - i })
                            while (i < n) { s = s + 2; i = i + 1 }
                            int j = 0
                            @Invariant({ 0 <= j && j <= n })
                            @Decreases({ n - j })
                            while (j < n) { j = j + 1 }
                            return s
                        }
                    }''')],
        // The soundness half. s changes between the loops: the first loop's facts about it are gone.
        [group: 'P319 majority', name: 'not kept when the code between the loops writes them', expect: 'Cannot prove postcondition of f',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == 2 * n })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s == 2 * i })
                            @Decreases({ n - i })
                            while (i < n) { s = s + 2; i = i + 1 }
                            s = s + 1
                            int j = 0
                            @Invariant({ 0 <= j && j <= n })
                            @Decreases({ n - j })
                            while (j < n) { j = j + 1 }
                            return s
                        }
                    }''')],
        // …or inside the second loop, even by adding zero: a write is a write.
        [group: 'P319 majority', name: 'not kept when the later loop writes them', expect: 'Cannot prove postcondition of f',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == 2 * n })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s == 2 * i })
                            @Decreases({ n - i })
                            while (i < n) { s = s + 2; i = i + 1 }
                            int j = 0
                            @Invariant({ 0 <= j && j <= n })
                            @Decreases({ n - j })
                            while (j < n) { s = s + 0; j = j + 1 }
                            return s
                        }
                    }''')],
        // The trailing if/else majority.ts ends with, generalised: every branch returns, so the tail is a ternary.
        [group: 'P319 majority', name: 'an else-if return chain after a loop is its ternary', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 && result <= 2 })
                        static int f(int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) { i = i + 1 }
                            if (i == 0) {
                                return 0
                            } else if (i == 1) {
                                return 1
                            } else {
                                return 2
                            }
                        }
                    }''')],
        // No else, so it falls through to the next statement: not a tail, and still the loud skip.
        [group: 'P319 majority', name: 'an if without an else after a loop still skips', expect: 'unsupported statement IfStatement after loop',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) { i = i + 1 }
                            if (i > 5) { return i }
                            return 0
                        }
                    }''')],
        // Honest boundary: Z3 can't build a counterexample through the quantified count axioms, so a wrong claim
        // (here: a majority always exists) comes back undecided, loudly, not with a model.
        [group: 'P319 majority', name: 'boundary: a wrong majority claim is undecided, not refuted', expect: 'Could not decide postcondition of majority',
         src: tc('''class C {
                        @Requires({ arr.every { int k -> k >= 0 } })
                        @Ensures({ result != -1 })
                        static int majority(int[] arr) {
                            int cand = 0
                            int cnt = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= arr.length && cnt >= 0 && cnt <= i && cand >= 0 })
                            @Invariant({ 2 * arr[0..<i].count(cand) <= i + cnt })
                            @Invariant({ arr.every { int y -> y == cand || 2 * arr[0..<i].count(y) <= i - cnt } })
                            @Decreases({ arr.length - i })
                            while (i < arr.length) {
                                if (cnt == 0) {
                                    cand = arr[i]
                                    cnt = 1
                                } else if (arr[i] == cand) {
                                    cnt = cnt + 1
                                } else {
                                    cnt = cnt - 1
                                }
                                i = i + 1
                            }
                            int occ = 0
                            int j = 0
                            @Invariant({ 0 <= j && j <= arr.length && occ == arr[0..<j].count(cand) })
                            @Decreases({ arr.length - j })
                            while (j < arr.length) {
                                if (arr[j] == cand) {
                                    occ = occ + 1
                                }
                                j = j + 1
                            }
                            if (2 * occ > arr.length) {
                                return cand
                            } else {
                                return -1
                            }
                        }
                    }''')],
    ]
}
