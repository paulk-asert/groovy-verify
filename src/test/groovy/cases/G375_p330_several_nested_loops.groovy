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
 * 'P330 several nested loops' — a loop body could hold only one annotated nested loop ("more than one nested loop in
 * the loop body — not yet supported"). Each is now verified in turn (VerifyChecker.verifyNestedLoop): its
 * establishment runs the outer body up to it, where the nested loops before it are summarised, and its own
 * preservation, progress and returns are checked as for a single one.
 */
class G375_p330_several_nested_loops {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 330 several nested loops: a loop body may hold any number of annotated nested loops in sequence, each with its own establishment (from the outer body up to it, the nested loops before it summarised, so their exit facts reach it), preservation, progress and returns; and a nested loop return is checked against @Ensures in any of sequential outer loops. Loops nested three deep still skip loudly.'

    static final List<Map> CASES = [

        [group: 'P330 several nested loops', name: 'two nested loops in one body', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                int p = 0
                                int j = 0
                                @Invariant({ 0 <= j && j <= n && p >= 0 })
                                @Decreases({ n - j })
                                while (j < n) { p = p + 1; j = j + 1 }
                                int q = 0
                                int k = 0
                                @Invariant({ 0 <= k && k <= i && q >= 0 })
                                @Decreases({ i - k })
                                while (k < i) { q = q + 2; k = k + 1 }
                                s = s + p + q
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        // k <= j needs j == n, the first nested loop's exit fact, carried by its summary into the second's establishment.
        [group: 'P330 several nested loops', name: 'the second nested loop starts from the first one exit', ok: true,
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
                                while (j < n) { j = j + 1 }
                                int k = 0
                                @Invariant({ 0 <= k && k <= j })
                                @Decreases({ j - k })
                                while (k < j) { k = k + 1 }
                                s = s + k
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P330 several nested loops', name: 'a wrong establishment of the second nested loop is refuted', expect: 'Cannot prove loop invariant holds on entry',
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
                                while (j < n) { j = j + 1 }
                                int k = j + 1
                                @Invariant({ 0 <= k && k <= j })
                                @Decreases({ j - k })
                                while (k < j) { k = k + 1 }
                                s = s + k
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P330 several nested loops', name: 'a wrong preservation of the second nested loop is refuted', expect: 'Cannot prove loop invariant is preserved',
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
                                while (j < n) { j = j + 1 }
                                int q = 0
                                int k = 0
                                @Invariant({ 0 <= k && k <= n && q >= 0 })
                                @Decreases({ n - k })
                                while (k < n) { q = q - 1; k = k + 1 }
                                s = s + q
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P330 several nested loops', name: 'a return in the second nested loop', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == -1 || (0 <= result && result < a.length && a[result] == 0) })
                        static int f(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                int j = 0
                                @Invariant({ 0 <= j && j <= a.length })
                                @Decreases({ a.length - j })
                                while (j < a.length) { j = j + 1 }
                                int k = 0
                                @Invariant({ 0 <= k && k <= a.length })
                                @Decreases({ a.length - k })
                                while (k < a.length) {
                                    if (a[k] == 0) return k
                                    k = k + 1
                                }
                                i = i + 1
                            }
                            return -1
                        }
                    }''')],
        [group: 'P330 several nested loops', name: 'a wrong return in the second nested loop is refuted', expect: 'Cannot prove postcondition of f',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == -1 || (0 <= result && result < a.length && a[result] == 0) })
                        static int f(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                int j = 0
                                @Invariant({ 0 <= j && j <= a.length })
                                @Decreases({ a.length - j })
                                while (j < a.length) { j = j + 1 }
                                int k = 0
                                @Invariant({ 0 <= k && k <= a.length })
                                @Decreases({ a.length - k })
                                while (k < a.length) {
                                    if (a[k] == 1) return k
                                    k = k + 1
                                }
                                i = i + 1
                            }
                            return -1
                        }
                    }''')],
        // The nested return is checked whichever of sequential loops it sits in. (A correct version still skips loudly:
        // the last loop can't summarise an earlier one that holds a nested loop.)
        [group: 'P330 several nested loops', name: 'a nested return in an earlier of sequential loops is checked', expect: 'Cannot prove postcondition of f',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 })
                        static int f(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                int k = 0
                                @Invariant({ 0 <= k && k <= a.length })
                                @Decreases({ a.length - k })
                                while (k < a.length) {
                                    if (a[k] < 0) return -1
                                    k = k + 1
                                }
                                i = i + 1
                            }
                            int j = 0
                            @Invariant({ 0 <= j && j <= a.length })
                            @Decreases({ a.length - j })
                            while (j < a.length) { j = j + 1 }
                            return j
                        }
                    }''')],
    ]
}
