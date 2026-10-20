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
 * 'P336 nested-loop repros' — a nested loop's preservation, progress, returns and body obligations are checked at an
 * arbitrary inner iteration, which knew nothing of the outer loop, so a refutation could pick n = 0 and render a call
 * that never enters the outer loop. The outer invariant and guard conjuncts over names nothing writes between the
 * outer-body entry and the inner iteration, and the outer loop's frame facts, now hold there too
 * (VerifyChecker.outerFactsForInner). En route: under a do-while outer loop the inner establishment assumed the outer
 * invariant and guard on the first pass, when neither has been checked; it is now also checked from the loop entry.
 */
class G380_p336_nested_loop_repros {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 336 nested-loop repros: a nested loop is checked at an arbitrary inner iteration with the outer loop\'s invariant and guard conjuncts that nothing on the way writes, and its frame facts, so a refutation\'s failing call enters the outer loop (f(1, 1), not f(0, 1)). An outer fact the outer body overwrites before the inner loop is not assumed. Under a do-while, the inner loop is also established on the first pass, which runs before the guard.'

    static final List<Map> CASES = [

        // It read f(0, 1) before: with n = 0 the outer loop never runs.
        [group: 'P336 nested-loop repros', name: 'an inner preservation repro enters the outer loop', expect: ['Cannot prove loop invariant is preserved', 'fails on: f(1, 1)'],
         src: tc('''class C {
                        static void f(int n, int m) {
                            int k = 0
                            @Invariant({ 0 <= k })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                int t = 0
                                @Invariant({ 0 <= i && t == 0 })
                                @Decreases({ m - i })
                                while (i < m) { t = t + 1; i = i + 1 }
                                k = k + 1
                            }
                        }
                    }''')],
        // The outer invariant 0 <= k <= n and guard k < n hold in the inner body: nothing on the way writes k or n.
        [group: 'P336 nested-loop repros', name: 'an inner bounds repro enters the outer loop', expect: ['Possible IndexOutOfBoundsException', 'fails on: f(new int[0], 1)'],
         src: tc('''class C {
                        @Requires({ a != null && n >= 0 })
                        static void f(int[] a, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= a.length + 1 })
                                @Decreases({ a.length + 1 - i })
                                while (i <= a.length) { a[i] = k; i = i + 1 }
                                k = k + 1
                            }
                        }
                    }''')],
        [group: 'P336 nested-loop repros', name: 'the outer guard proves an inner invariant clause', ok: true,
         src: tc('''class C {
                        static void f(int n) {
                            int k = 0
                            @Invariant({ 0 <= k })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && k < n })
                                @Decreases({ 3 - i })
                                while (i < 3) { i = i + 1 }
                                k = k + 1
                            }
                        }
                    }''')],
        // k = n runs before the inner loop, so k < n is no longer true there.
        [group: 'P336 nested-loop repros', name: 'an outer fact the outer body overwrites is not assumed', expect: ['Cannot prove loop invariant holds on entry', 'fails on: f(1)'],
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        static void f(int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                k = n
                                int i = 0
                                @Invariant({ 0 <= i && k < n })
                                @Decreases({ 3 - i })
                                while (i < 3) { i = i + 1 }
                            }
                        }
                    }''')],
        // Unsound before: the do-while body runs once before its guard, and with n = 0, k < n is false.
        [group: 'P336 nested-loop repros', name: 'under a do-while the inner loop is also established on the first pass', expect: ['Cannot prove loop invariant holds on entry', 'fails on: f(0)'],
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        static void f(int n) {
                            int k = 0
                            @Invariant({ 0 <= k })
                            @Decreases({ n - k })
                            do {
                                int i = 0
                                @Invariant({ 0 <= i && k < n })
                                @Decreases({ 3 - i })
                                while (i < 3) { i = i + 1 }
                                k = k + 1
                            } while (k < n)
                        }
                    }''')],
        [group: 'P336 nested-loop repros', name: 'a correct inner invariant under a do-while verifies', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 1 })
                        static void f(int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            do {
                                int i = 0
                                @Invariant({ 0 <= i && i <= 3 && k < n })
                                @Decreases({ 3 - i })
                                while (i < 3) { i = i + 1 }
                                k = k + 1
                            } while (k < n)
                        }
                    }''')],
        [group: 'P336 nested-loop repros', name: 'an instance method with a field beside the loops', ok: true,
         src: tc('''class C {
                        int cnt = 0
                        void bump() { cnt = cnt + 1 }
                        void f(int n) {
                            int k = 0
                            @Invariant({ 0 <= k })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i })
                                @Decreases({ 3 - i })
                                while (i < 3) { i = i + 1 }
                                k = k + 1
                            }
                        }
                    }''')],
    ]
}
