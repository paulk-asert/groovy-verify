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
 * 'P325 continue ahead of an exit' — Phase 324's continue desugaring moved what follows an {@code if (c) continue}
 * into its else branch, which buried a later {@code break} or {@code return} where the exit lifting can't see it.
 * A top-level {@code if (c) continue} / {@code if (c) { lead; continue }} followed by an exit now records the
 * continue in a flag instead ({@code boolean cont = c; if (cont) { lead }}), and guards what follows by it: an exit
 * {@code if (d) X} becomes {@code if (!cont && d) X}, so it stays a top-level exit (ContractExpansionTransform.continueFree).
 */
class G370_p325_continue_flag {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 325 continue ahead of an exit: a top-level if (c) continue or if (c) { lead; continue } followed by a break or return records the continue in a body-local flag and guards what follows by it, so if (d) break / if (d) { lead; break } / if (d) return e stay top-level exits (with condition !cont && d, short-circuited so d is only evaluated when the iteration did not continue), in an outer loop and in a nested one; a continue nested in an if ahead of an exit still skips loudly.'

    static final List<Map> CASES = [

        [group: 'P325 continue ahead of an exit', name: 'a continue ahead of a break', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 })
                        static int f(int[] a, int t) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] < 0) { i = i + 1; continue }
                                if (a[i] == t) break
                                i = i + 1
                            }
                            return i
                        }
                    }''')],
        // A search that skips the negatives: the break's condition, a[i] == t, reaches the postcondition.
        [group: 'P325 continue ahead of an exit', name: 'the break carries its condition past the continue', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == -1 || (0 <= result && result < a.length && a[result] == t) })
                        static int find(int[] a, int t) {
                            int i = 0
                            int r = -1
                            @Invariant({ 0 <= i && i <= a.length && r == -1 })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] < 0) { i = i + 1; continue }
                                if (a[i] == t) { r = i; break }
                                i = i + 1
                            }
                            return r
                        }
                    }''')],
        [group: 'P325 continue ahead of an exit', name: 'a return after a continue', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == -1 || (0 <= result && result < a.length && a[result] == t) })
                        static int find(int[] a, int t) {
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            for (int i = 0; i < a.length; i++) {
                                if (a[i] < 0) continue
                                if (a[i] == t) return i
                            }
                            return -1
                        }
                    }''')],
        [group: 'P325 continue ahead of an exit', name: 'two continues ahead of a return and a break', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == -1 || (0 <= result && result < a.length && a[result] == t) })
                        static int find(int[] a, int t) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                i = i + 1
                                if (a[i - 1] < 0) continue
                                if (a[i - 1] > 100) continue
                                if (a[i - 1] == t) return i - 1
                                else if (a[i - 1] == t + 1) break
                            }
                            return -1
                        }
                    }''')],
        // a[i + 1] is in bounds only because the continue wasn't taken: the guarded exit short-circuits.
        [group: 'P325 continue ahead of an exit', name: 'the exit condition is evaluated only when not continuing', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 })
                        static int f(int[] a, int t) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (i + 1 >= a.length) { i = i + 1; continue }
                                if (a[i + 1] == t) break
                                i = i + 1
                            }
                            return i
                        }
                    }''')],
        [group: 'P325 continue ahead of an exit', name: 'a wrong break value is refuted', expect: 'Cannot prove postcondition of find',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == -1 || (0 <= result && result < a.length && a[result] == t) })
                        static int find(int[] a, int t) {
                            int i = 0
                            int r = -1
                            @Invariant({ 0 <= i && i <= a.length && r == -1 })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] < 0) { i = i + 1; continue }
                                if (a[i] != t) { r = i; break }
                                i = i + 1
                            }
                            return r
                        }
                    }''')],
        // The continuing iteration must still preserve the invariant: s goes negative on f([1], 2).
        [group: 'P325 continue ahead of an exit', name: 'the continuing iteration preserves the invariant', expect: 'Cannot prove loop invariant is preserved',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 })
                        static int f(int[] a, int t) {
                            int s = 0
                            @Invariant({ 0 <= i && i <= a.length && s >= 0 })
                            @Decreases({ a.length - i })
                            for (int i = 0; i < a.length; i++) {
                                if (a[i] > 0) { s = s - 1; continue }
                                if (a[i] == t) break
                                s = s + 1
                            }
                            return s
                        }
                    }''')],

        // ---------- in a nested loop ----------
        [group: 'P325 continue ahead of an exit', name: 'a continue ahead of a nested loop break', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                @Invariant({ 0 <= j && j <= n })
                                @Decreases({ n - j })
                                while (j < n) {
                                    j = j + 1
                                    if (j % 2 == 0) continue
                                    if (j > i) break
                                }
                                s = s + j
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P325 continue ahead of an exit', name: 'a wrong value from a nested break past a continue is refuted', expect: 'Cannot prove loop invariant is preserved',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                int d = 0
                                @Invariant({ 0 <= j && j <= n })
                                @Decreases({ n - j })
                                while (j < n) {
                                    j = j + 1
                                    if (j % 2 == 0) continue
                                    if (j > i) { d = -1; break }
                                }
                                s = s + d
                                i = i + 1
                            }
                            return s
                        }
                    }''')],

        // ---------- still out ----------
        [group: 'P325 continue ahead of an exit', name: 'a continue nested in an if ahead of a break skips loudly', expect: 'Skipped loop verification',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 })
                        static int f(int[] a, int t) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                i = i + 1
                                if (t > 0) {
                                    if (a[i - 1] < 0) continue
                                    t = t - 1
                                }
                                if (a[i - 1] == t) break
                            }
                            return i
                        }
                    }''')],
    ]
}
