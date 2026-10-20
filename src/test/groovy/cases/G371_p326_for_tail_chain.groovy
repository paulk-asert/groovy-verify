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
 * 'P326 for loop tail chain' — Phase 49c lifts the exits of an if/else chain ending a loop body, but a {@code for}
 * loop's update is appended after the user's body at capture, so the chain was no longer the tail and the loop
 * skipped loudly. LoopSpec now records the update, and the lifting looks just ahead of it (VerifyChecker.desugarTailReturns).
 */
class G371_p326_for_tail_chain {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 326 for loop tail chain: an if/else chain ending a for or for-in loop body whose leaves return or break (with a lead) is lifted into top-level exits as in a while loop, with the appended update kept last, so it runs on every continuing leaf; before, the update made the chain not the tail and the loop skipped loudly. Composes with Phase 325\'s continue flag.'

    static final List<Map> CASES = [

        [group: 'P326 for loop tail chain', name: 'a return and a break ending a for body', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == -1 || (0 <= result && result < a.length && a[result] == t) })
                        static int find(int[] a, int t) {
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            for (int i = 0; i < a.length; i++) {
                                if (a[i] == t) return i
                                else if (a[i] == t + 1) break
                            }
                            return -1
                        }
                    }''')],
        [group: 'P326 for loop tail chain', name: 'breaks with leads ending a for body', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == -1 || (0 <= result && result < a.length && a[result] == t) })
                        static int find(int[] a, int t) {
                            int found = -1
                            @Invariant({ 0 <= i && i <= a.length && found == -1 })
                            @Decreases({ a.length - i })
                            for (int i = 0; i < a.length; i++) {
                                if (a[i] == t) { found = i; break }
                                else if (a[i] < 0) { found = -1; break }
                            }
                            return found
                        }
                    }''')],
        [group: 'P326 for loop tail chain', name: 'a tail chain in a for-in body', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result >= -1 })
                        static int f(List<Integer> xs, int t) {
                            @Invariant({ true })
                            for (int x in xs) {
                                if (x == t) return x < 0 ? -1 : x
                                else if (x < 0) break
                            }
                            return -1
                        }
                    }''')],
        [group: 'P326 for loop tail chain', name: 'continues ahead of a for tail chain', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == -1 || (0 <= result && result < a.length && a[result] == t) })
                        static int find(int[] a, int t) {
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            for (int i = 0; i < a.length; i++) {
                                if (a[i] < 0) continue
                                if (a[i] > 100) continue
                                if (a[i] == t) return i
                                else if (a[i] == t + 1) break
                            }
                            return -1
                        }
                    }''')],
        [group: 'P326 for loop tail chain', name: 'a wrong return from the chain is refuted', expect: 'Cannot prove postcondition of find',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == -1 || (0 <= result && result < a.length && a[result] == t) })
                        static int find(int[] a, int t) {
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            for (int i = 0; i < a.length; i++) {
                                if (a[i] == t) return i
                                else if (a[i] == t + 1) return i
                            }
                            return -1
                        }
                    }''')],
        // The update still runs on the continuing leaf: stepping by 2 breaks i <= a.length on f([0], 5).
        [group: 'P326 for loop tail chain', name: 'the update still runs after the chain', expect: 'Cannot prove loop invariant is preserved',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= -1 })
                        static int find(int[] a, int t) {
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            for (int i = 0; i < a.length; i += 2) {
                                if (a[i] == t) return i
                                else if (a[i] < 0) break
                            }
                            return -1
                        }
                    }''')],
        // ---------- nested ----------
        // A nested loop's body gets the same lifting, so the chain's breaks reach the inner summary as top-level exits.
        [group: 'P326 for loop tail chain', name: 'a nested for loop tail chain', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                int k = 0
                                @Invariant({ 0 <= j && j <= n && k >= 0 })
                                @Decreases({ n - j })
                                for (int j = 0; j < n; j++) {
                                    if (j == i) break
                                    else if (j > 3) { k = 1; break }
                                }
                                s = s + k
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        // Fixed alongside: a nested for loop's init didn't run before its invariant's entry check (j was unconstrained).
        [group: 'P326 for loop tail chain', name: 'a nested for loop establishes its invariant from its init', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                int k = 0
                                @Invariant({ 0 <= j && j <= n && k >= 0 })
                                @Decreases({ n - j })
                                for (int j = 0; j < n; j++) {
                                    k = k + 1
                                }
                                s = s + k
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P326 for loop tail chain', name: 'a nested for loop init that breaks the invariant is refuted', expect: 'Cannot prove loop invariant holds on entry',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                int k = 0
                                @Invariant({ 0 <= j && j <= n && k >= 0 })
                                @Decreases({ n - j })
                                for (int j = n + 1; j < n; j++) {
                                    k = k + 1
                                }
                                s = s + k
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
    ]
}
