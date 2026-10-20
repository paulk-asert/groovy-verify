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
 * 'P337 sequential-loop repros' — a refutation's failing call is rendered from the solver's model, and some checks
 * see less than the whole precondition: a bounds check drops its quantified and aggregate conjuncts (Phase 91b), and a
 * later loop knows an earlier one only by its summary. So a repro could break the method's own @Requires. The rendered
 * arguments are now pinned and the full precondition re-checked (VerifyChecker.reproUnderRequires). If they break it,
 * the elements come from a model that meets it; failing that, the call is withheld with a note. A loop summary's
 * havocked value is shown as "s (after a loop)", not s$havoc$0.
 */
class G381_p337_sequential_loop_repros {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 337 sequential-loop repros: a failing call must meet the method\'s own @Requires. A check that assumed only part of it (a bounds check without its quantified conjuncts, a later loop after an earlier one\'s summary) gets its rendered arguments re-checked against the whole precondition; elements that break it are replaced from a model that meets it ([44, 6] as int[] for a.every { v > 5 }), and a call no model can repair is withheld with a note. A value after a loop reads s (after a loop), not s$havoc$0.'

    static final List<Map> CASES = [

        // The allocate bump loop without its slack bound. The bounds check ran without ws.sum() > 0, so its model had
        // ws.length = 0: allocate(1, new int[0]) is a call @Requires forbids, and allocate never fails here.
        [group: 'P337 sequential-loop repros', name: 'a repro that breaks @Requires is withheld, with a note',
         expect: ['Possible IndexOutOfBoundsException', 'no failing call: these arguments break the @Requires'],
         refute: 'fails on: allocate(1, new int[0])',
         src: tc('''class C {
                        @Requires({ ws != null && total >= 0 && ws.every { int w -> w >= 0 } && ws.sum() > 0 })
                        @Ensures({ result.length == ws.length && result.sum() == total })
                        static int[] allocate(int total, int[] ws) {
                            int W = ws.sum()
                            int[] result = new int[ws.length]
                            int s = 0
                            int p = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= ws.length && result.length == ws.length })
                            @Invariant({ s == result[0..<i].sum(0) && p == ws[0..<i].sum(0) })
                            @Invariant({ s * W <= total * p })
                            @Decreases({ ws.length - i })
                            while (i < ws.length) {
                                result[i] = (total * ws[i]).intdiv(W)
                                s = s + result[i]
                                p = p + ws[i]
                                i = i + 1
                            }
                            int left = total - s
                            int k = 0
                            @Invariant({ 0 <= k && 0 <= left && result.length == ws.length })
                            @Invariant({ result.sum() + left == total })
                            @Decreases({ left })
                            while (left > 0) {
                                result[k] = result[k] + 1
                                k = k + 1
                                left = left - 1
                            }
                            return result
                        }
                    }''')],
        // new int[2] has zeros, which a.every { v > 5 } rules out; a model of the precondition with a.length == 2 and
        // n == 3 supplies the elements.
        [group: 'P337 sequential-loop repros', name: 'a repro whose elements break @Requires is rebuilt from a model that meets it',
         expect: ['Possible IndexOutOfBoundsException', 'fails on: f([44, 6] as int[], 3)'], refute: 'new int[2]',
         src: tc('''class C {
                        @Requires({ a != null && a.length == 2 && a.every { int v -> v > 5 } && n >= 0 })
                        static void f(int[] a, int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) { i = i + 1 }
                            int j = 0
                            @Invariant({ 0 <= j && j <= i })
                            @Decreases({ i - j })
                            while (j < i) { a[j] = a[j] + 1; j = j + 1 }
                        }
                    }''')],
        [group: 'P337 sequential-loop repros', name: 'a repro that meets a quantified @Requires is kept',
         expect: 'fails on: f([1] as int[], -1)',
         src: tc('''class C {
                        @Requires({ a != null && a.every { int v -> v >= 0 } && a.length >= 1 })
                        static int f(int[] a, int k) { a[k] }
                    }''')],
        // It read s$havoc$0 = 1, the loop summary's internal name.
        [group: 'P337 sequential-loop repros', name: 'a value after an earlier loop is shown under its source name',
         expect: ['s (after a loop) = 1', 'fails on: f(1)'], refute: '$havoc$',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s == i })
                            @Decreases({ n - i })
                            while (i < n) { s = s + 1; i = i + 1 }
                            int j = 0
                            @Invariant({ 0 <= j && s == 0 })
                            @Decreases({ n - j })
                            while (j < n) { j = j + 1 }
                            return s
                        }
                    }''')],
        [group: 'P337 sequential-loop repros', name: 'a later loop\'s preservation repro',
         expect: ['Cannot prove loop invariant is preserved', 'fails on: f(1)'],
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s == i })
                            @Decreases({ n - i })
                            while (i < n) { s = s + 1; i = i + 1 }
                            int t = 0
                            int j = 0
                            @Invariant({ 0 <= j && j <= s && t == 0 })
                            @Decreases({ s - j })
                            while (j < s) { t = t + 1; j = j + 1 }
                            return t
                        }
                    }''')],
        [group: 'P337 sequential-loop repros', name: 'a later loop\'s bounds repro',
         expect: ['Possible IndexOutOfBoundsException', 'fails on: f(new int[0], 1)'],
         src: tc('''class C {
                        @Requires({ a != null && n >= 0 })
                        static void f(int[] a, int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) { i = i + 1 }
                            int j = 0
                            @Invariant({ 0 <= j && j <= i })
                            @Decreases({ i - j })
                            while (j < i) { a[j] = 0; j = j + 1 }
                        }
                    }''')],
        [group: 'P337 sequential-loop repros', name: 'a postcondition after two loops',
         expect: ['Cannot prove postcondition', 'fails on: f(0)'],
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == 2 * n + 1 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s == i })
                            @Decreases({ n - i })
                            while (i < n) { s = s + 1; i = i + 1 }
                            int j = 0
                            @Invariant({ 0 <= j && j <= n && s == n + j })
                            @Decreases({ n - j })
                            while (j < n) { s = s + 1; j = j + 1 }
                            return s
                        }
                    }''')],
    ]
}
