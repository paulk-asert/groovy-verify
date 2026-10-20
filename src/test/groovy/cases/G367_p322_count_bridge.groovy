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
 * 'P322 count bridge' — an array's whole count {@code a.count(v)} and its prefix count over the full length
 * {@code a[0..<a.length].count(v)} are one quantity. They were separate functions (Phase 12's count, Phase 208's range
 * oracle) with nothing linking them; the bridge {@code ∀v. count(a, v) == bcount(a, v, 0, a.length)} is emitted once
 * per array handle, only when both spellings meet in a VC.
 */
class G367_p322_count_bridge {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 322 count bridge: an int array\'s whole count a.count(v) equals its prefix count over the full length a[0..<a.length].count(v), in both directions, for a bound value (a.every { y -> … a.count(y) … }) and after a store, so a counting loop that maintains the prefix form concludes the whole form, and the Boyer–Moore majority vote states its postconditions as arr.count(x). Emitted only when both spellings meet in one VC, so whole-count-only proofs keep their quantifier profile. Lists already shared one function. A wrong count claim is undecided rather than refuted.'

    static final List<Map> CASES = [

        // ---------- the two spellings are one quantity ----------
        [group: 'P322 count bridge', name: 'a full-length prefix count is the whole count', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ a[0..<a.length].count(v) == a.count(v) })
                        static void f(int[] a, int v) { }
                    }''')],
        [group: 'P322 count bridge', name: 'a fact about the whole count reaches the prefix count', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && a.count(v) == c })
                        @Ensures({ a[0..<a.length].count(v) == c })
                        static void f(int[] a, int v, int c) { }
                    }''')],
        // The bridge quantifies over the value, so it serves a value that is itself bound.
        [group: 'P322 count bridge', name: 'the bridge holds for every value', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ a.every { int y -> a.count(y) == a[0..<a.length].count(y) } })
                        static void f(int[] a) { }
                    }''')],
        // Each array handle gets its own bridge, so it holds after a store too.
        [group: 'P322 count bridge', name: 'the bridge holds after a store', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ a.count(v) == a[0..<a.length].count(v) })
                        static void f(int[] a, int v) { a[0] = v }
                    }''')],

        // ---------- what it's for ----------
        // A counting loop maintains the prefix form; the postcondition states the whole form.
        [group: 'P322 count bridge', name: 'a counting loop concludes the whole count', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == a.count(v) })
                        static int occ(int[] a, int v) {
                            int c = 0
                            int j = 0
                            @Invariant({ 0 <= j && j <= a.length && c == a[0..<j].count(v) })
                            @Decreases({ a.length - j })
                            while (j < a.length) {
                                if (a[j] == v) c = c + 1
                                j = j + 1
                            }
                            return c
                        }
                    }''')],
        // LemmaScript's majority vote with its postconditions as arr.count(x) (majority.ts's occOf(arr, x, arr.length)).
        [group: 'P322 count bridge', name: 'majority vote with whole-array counts', ok: true,
         src: tc('''class C {
                        /** Returns the value occurring in more than half of arr, or -1 when there is none. */
                        @Requires({ arr.every { int k -> k >= 0 } })
                        @Ensures({ result == -1 || (result >= 0 && 2 * arr.count(result) > arr.length) })
                        @Ensures({ arr.any { int x -> 2 * arr.count(x) > arr.length } ==> result != -1 })
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

        // ---------- not over-claimed ----------
        // An off-by-one whole-count claim after the loop isn't proved (undecided under the count axioms, not refuted).
        [group: 'P322 count bridge', name: 'a wrong whole count is not proved', expect: 'Could not decide postcondition of occ',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == a.count(v) + 1 })
                        static int occ(int[] a, int v) {
                            int c = 0
                            int j = 0
                            @Invariant({ 0 <= j && j <= a.length && c == a[0..<j].count(v) })
                            @Decreases({ a.length - j })
                            while (j < a.length) {
                                if (a[j] == v) c = c + 1
                                j = j + 1
                            }
                            return c
                        }
                    }''')],
    ]
}
