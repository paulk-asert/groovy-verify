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
 * 'P324 continue and nested break' — the last loop gap of the LemmaScript ports. {@code continue} is desugared out of
 * the captured loop body (ContractExpansionTransform.desugarContinue); a nested loop's top-level breaks each add an
 * exit state to its summary (LoopEncoder.summarizeWithBreaks).
 */
class G369_p324_continue_break {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 324 continue and nested break (the last loop gap of the LemmaScript ports): an unlabelled continue is desugared at capture — what follows an if that may continue moves into its branches, a continue drops the rest of its branch — before a for loop\'s update is appended, so while, for, for-in and do-while all take it, and the continuing iteration preserves the invariant as in Dafny; a rewrite that would bury a top-level break skips loudly (one before a nested loop is Phase 344). A top-level if (c) break / if (c) { lead; break } in a nested loop adds one exit state per break to the inner summary (inv && guard at the iteration start, the body to the break, its condition and lead), merged with the natural exit under a selector whose alternatives assert only under their own guard (SmtSession.pushAssertGuard).'

    static final List<Map> CASES = [

        // ---------- continue ----------
        // P; if (c) continue; Q reads as P; if (c) {} else { Q }: the continuing iteration must still preserve the invariant.
        [group: 'P324 continue and nested break', name: 'continue in a while loop', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 })
                        static int f(int[] a) {
                            int i = 0
                            int s = 0
                            @Invariant({ 0 <= i && i <= a.length && s >= 0 })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                i = i + 1
                                if (a[i - 1] < 0) continue
                                s = s + a[i - 1]
                            }
                            return s
                        }
                    }''')],
        [group: 'P324 continue and nested break', name: 'continue in a for loop still runs the update', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 })
                        static int f(int[] a) {
                            int s = 0
                            @Invariant({ 0 <= i && i <= a.length && s >= 0 })
                            @Decreases({ a.length - i })
                            for (int i = 0; i < a.length; i++) {
                                if (a[i] < 0) continue
                                s = s + a[i]
                            }
                            return s
                        }
                    }''')],
        [group: 'P324 continue and nested break', name: 'continue in a for-in loop', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result >= 0 })
                        static int f(List<Integer> xs) {
                            int s = 0
                            @Invariant({ s >= 0 })
                            for (int x in xs) {
                                if (x < 0) continue
                                s = s + x
                            }
                            return s
                        }
                    }''')],
        [group: 'P324 continue and nested break', name: 'continue in a do-while loop', ok: true,
         src: tc('''class C {
                        @Requires({ n > 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int i = 0
                            int s = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            do {
                                i = i + 1
                                if (i % 2 == 0) continue
                                s = s + i
                            } while (i < n)
                            return s
                        }
                    }''')],
        [group: 'P324 continue and nested break', name: 'continue with a lead', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == a.length })
                        static int f(int[] a) {
                            int neg = 0
                            int pos = 0
                            @Invariant({ 0 <= i && i <= a.length && neg + pos == i })
                            @Decreases({ a.length - i })
                            for (int i = 0; i < a.length; i++) {
                                if (a[i] < 0) { neg = neg + 1; continue }
                                pos = pos + 1
                            }
                            return neg + pos
                        }
                    }''')],
        [group: 'P324 continue and nested break', name: 'continue from a nested if', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 })
                        static int f(int[] a) {
                            int s = 0
                            @Invariant({ 0 <= i && i <= a.length && s >= 0 })
                            @Decreases({ a.length - i })
                            for (int i = 0; i < a.length; i++) {
                                if (a[i] != 0) {
                                    if (a[i] < 0) continue
                                    s = s + 1
                                }
                                s = s + a[i] * a[i]
                            }
                            return s
                        }
                    }''')],
        // Skipping the positives instead keeps the negatives: s >= 0 fails, on f([-1]).
        [group: 'P324 continue and nested break', name: 'a wrong continue is refuted', expect: 'Cannot prove loop invariant is preserved',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 })
                        static int f(int[] a) {
                            int s = 0
                            @Invariant({ 0 <= i && i <= a.length && s >= 0 })
                            @Decreases({ a.length - i })
                            for (int i = 0; i < a.length; i++) {
                                if (a[i] > 0) continue
                                s = s + a[i]
                            }
                            return s
                        }
                    }''')],
        [group: 'P324 continue and nested break', name: 'a continue before a nested loop verifies (Phase 344)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                i = i + 1
                                if (i % 2 == 0) continue
                                int j = 0
                                @Invariant({ 0 <= j && j <= i })
                                @Decreases({ i - j })
                                while (j < i) { j = j + 1 }
                                s = s + j
                            }
                            return s
                        }
                    }''')],

        // ---------- break out of a nested loop ----------
        [group: 'P324 continue and nested break', name: 'break out of a nested loop', ok: true,
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
                                    if (j == i) break
                                    j = j + 1
                                }
                                s = s + j
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        // The exact sum needs j == i, which holds only at the break: the inner summary carries each break's state.
        [group: 'P324 continue and nested break', name: 'the break exit carries its condition', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n * (n - 1) / 2 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && 2 * s == i * (i - 1) })
                            @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                @Invariant({ 0 <= j && j <= i })
                                @Decreases({ n - j })
                                while (j < n) {
                                    if (j == i) break
                                    j = j + 1
                                }
                                s = s + j
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P324 continue and nested break', name: 'a break lead need not keep the inner invariant', ok: true,
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
                                    if (j == i) { j = n + 5; break }
                                    j = j + 1
                                }
                                s = s + j
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P324 continue and nested break', name: 'a wrong value from the break is refuted', expect: 'Cannot prove loop invariant is preserved',
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
                                    if (j == i) { d = -1; break }
                                    j = j + 1
                                }
                                s = s + d
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        // A break leaves only the inner loop, but a return still has to meet the method's @Ensures (here, it doesn't).
        [group: 'P324 continue and nested break', name: 'an inner return beside a break keeps its own check', expect: 'Cannot prove postcondition of f',
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
                                    if (j == 7) return -1
                                    if (j == i) break
                                    j = j + 1
                                }
                                s = s + j
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
    ]
}
