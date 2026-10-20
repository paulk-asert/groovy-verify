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
 * 'P329 early exits with sequential loops' — a method with several annotated loops in sequence skipped loudly as soon
 * as any had an early exit. The last site checks every prefix exit (its prefix is the method's up to it), each
 * earlier site its own in-body returns, and an earlier loop's breaks reach the later loops through the prefix
 * replay. Fixed alongside: prefix exit guards were assumed false at method entry rather than where they are
 * evaluated (VerifyChecker.walkPrefix), which proved false postconditions and invariants.
 */
class G374_p329_sequential_exits {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 329 early exits with sequential loops: a return in any of several sequential annotated loops, an exit between them, and a break out of an earlier loop are verified instead of skipping the method; an earlier loop that breaks keeps the invariant conjuncts over state nothing before its breaks writes, but not its negated guard. Fixed alongside (unsound before): a prefix exit guard was assumed false at method entry, not where it is evaluated, so after x = x + 1 a guard x == 2 read as x0 == 2, and false postconditions and loop invariants proved.'

    static final List<Map> CASES = [

        // ---------- fixed: a prefix exit guard is assumed false where it is evaluated ----------
        // f(2): x becomes 3, so the first exit isn't taken and it returns 7. The guards were assumed false at method
        // entry (x0 != 2), which ruled that run out.
        [group: 'P329 early exits with sequential loops', name: 'a prefix exit guard is read after the statements ahead of it', expect: 'Cannot prove postcondition of f',
         src: tc('''class C {
                        @Ensures({ result != 7 })
                        static int f(int x) {
                            x = x + 1
                            if (x == 2) return 0
                            if (x == 3) return 7
                            int i = 0
                            @Invariant({ i >= 0 })
                            @Decreases({ 10 - i })
                            while (i < 10) { i = i + 1 }
                            return 1
                        }
                    }''')],
        // f(2) reaches the loop with x == 3.
        [group: 'P329 early exits with sequential loops', name: 'establishment reads a prefix exit guard where it is evaluated', expect: 'Cannot prove loop invariant holds on entry',
         src: tc('''class C {
                        @Ensures({ result >= 0 })
                        static int f(int x) {
                            x = x + 1
                            if (x == 2) return 0
                            int i = 0
                            @Invariant({ i >= 0 && x != 3 })
                            @Decreases({ 10 - i })
                            while (i < 10) { i = i + 1 }
                            return 1
                        }
                    }''')],

        // ---------- early exits with sequential loops ----------
        [group: 'P329 early exits with sequential loops', name: 'a return in the first loop, a sum in the second', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= -1 })
                        static int f(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] < 0) return -1
                                i = i + 1
                            }
                            int s = 0
                            int j = 0
                            @Invariant({ 0 <= j && j <= a.length && s >= 0 })
                            @Decreases({ a.length - j })
                            while (j < a.length) {
                                if (a[j] > 0) s = s + a[j]
                                j = j + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P329 early exits with sequential loops', name: 'a wrong return in the first loop is refuted', expect: 'Cannot prove postcondition of f',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 })
                        static int f(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] < 0) return -1
                                i = i + 1
                            }
                            int s = 0
                            int j = 0
                            @Invariant({ 0 <= j && j <= a.length && s >= 0 })
                            @Decreases({ a.length - j })
                            while (j < a.length) {
                                if (a[j] > 0) s = s + a[j]
                                j = j + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P329 early exits with sequential loops', name: 'an exit between the loops reads the first loop state', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 })
                        static int f(int[] a) {
                            int neg = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length && neg >= 0 })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] < 0) neg = neg + 1
                                i = i + 1
                            }
                            if (neg > 0) return neg
                            int s = 0
                            int j = 0
                            @Invariant({ 0 <= j && j <= a.length && s >= 0 })
                            @Decreases({ a.length - j })
                            while (j < a.length) {
                                s = s + 1
                                j = j + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P329 early exits with sequential loops', name: 'a wrong exit between the loops is refuted', expect: 'Cannot prove postcondition of f',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 })
                        static int f(int[] a) {
                            int neg = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length && neg >= 0 })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] < 0) neg = neg + 1
                                i = i + 1
                            }
                            if (neg > 0) return -neg
                            int s = 0
                            int j = 0
                            @Invariant({ 0 <= j && j <= a.length && s >= 0 })
                            @Decreases({ a.length - j })
                            while (j < a.length) {
                                s = s + 1
                                j = j + 1
                            }
                            return s
                        }
                    }''')],
        // A conjunct of the first loop's invariant over nothing written before its break (0 <= i) holds at the break.
        [group: 'P329 early exits with sequential loops', name: 'the second loop starts where the first broke off', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 && result <= a.length })
                        static int f(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] == 0) break
                                i = i + 1
                            }
                            int c = 0
                            int j = i
                            @Invariant({ i <= j && j <= a.length && 0 <= c && c <= j - i })
                            @Decreases({ a.length - j })
                            while (j < a.length) {
                                c = c + 1
                                j = j + 1
                            }
                            return c
                        }
                    }''')],
        [group: 'P329 early exits with sequential loops', name: 'a return in the second loop', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == -1 || (0 <= result && result < a.length && a[result] == t) })
                        static int f(int[] a, int t) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                s = s + a[i]
                                i = i + 1
                            }
                            int j = 0
                            @Invariant({ 0 <= j && j <= a.length })
                            @Decreases({ a.length - j })
                            while (j < a.length) {
                                if (a[j] == t) return j
                                j = j + 1
                            }
                            return -1
                        }
                    }''')],
        // f(new int[2]) never reaches i == 3, so it returns 9: the guard was only ever evaluated on earlier values of i.
        [group: 'P329 early exits with sequential loops', name: 'an in-body guard is not assumed false after its loop', expect: 'Cannot prove postcondition of f',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result != 9 })
                        static int f(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (i == 3) return 0
                                i = i + 1
                            }
                            int j = 0
                            @Invariant({ 0 <= j && j <= a.length })
                            @Decreases({ a.length - j })
                            while (j < a.length) { j = j + 1 }
                            return i == 2 ? 9 : 1
                        }
                    }''')],
        // f([0]) returns -1: the lead writes i, so 0 <= i isn't carried past the loop.
        [group: 'P329 early exits with sequential loops', name: 'a break lead that writes a conjunct drops it', expect: 'Cannot prove postcondition of f',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 && result <= a.length })
                        static int f(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] == 0) { i = -1; break }
                                i = i + 1
                            }
                            int c = 0
                            int j = 0
                            @Invariant({ 0 <= j && j <= a.length && c == j })
                            @Decreases({ a.length - j })
                            while (j < a.length) {
                                c = c + 1
                                j = j + 1
                            }
                            return i
                        }
                    }''')],
        // f([0]) returns 0: at the break i < a.length, so the invariant survives but the negated guard doesn't.
        [group: 'P329 early exits with sequential loops', name: 'the negated guard is not kept across a break', expect: 'Cannot prove postcondition of f',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == a.length })
                        static int f(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] == 0) break
                                i = i + 1
                            }
                            int j = 0
                            @Invariant({ 0 <= j && j <= a.length })
                            @Decreases({ a.length - j })
                            while (j < a.length) { j = j + 1 }
                            return i
                        }
                    }''')],
    ]
}
