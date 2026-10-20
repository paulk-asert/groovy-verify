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
 * 'P338 a loop after a nested outer loop' — a later annotated loop replays the earlier ones as summaries: havoc what the
 * loop writes, assume its invariant and negated guard (LoopEncoder.summarizeInner). The write set came from innerFrame,
 * which bailed on any loop in the body, so an earlier outer loop holding a nested loop skipped the method ("nested loop
 * writes a field/collection or unbounded construct"). An annotated nested loop now contributes the writes of its init,
 * guard and body; it is verified at its own site. An unannotated one still bails.
 */
class G382_p338_loop_after_nested_loop {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 338 a loop after a nested outer loop: an annotated loop may follow an outer loop that holds a nested loop (a row-wise pass, then a plain one), and two such outer loops may follow each other. The earlier loop is summarised with its nested loop\'s writes havocked too, so its exit facts reach the later loop, and a fact the nested loop overwrites does not. An unannotated nested loop still skips loudly.'

    static final List<Map> CASES = [

        // The earlier loop is summarised (its writes, the inner loop's included, havocked; inv and not guard assumed), so s == n * m reaches the later loop.
        [group: 'P338 a loop after a nested outer loop', name: 'a loop after an outer loop that holds a nested loop', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 })
                        @Ensures({ result == n * m + n })
                        static int f(int n, int m) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && s == k * m })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m && s == k * m + i })
                                @Decreases({ m - i })
                                while (i < m) { s = s + 1; i = i + 1 }
                                k = k + 1
                            }
                            int j = 0
                            @Invariant({ 0 <= j && j <= n && s == n * m + j })
                            @Decreases({ n - j })
                            while (j < n) { s = s + 1; j = j + 1 }
                            return s
                        }
                    }''')],
        [group: 'P338 a loop after a nested outer loop', name: 'a wrong postcondition after both refutes', expect: ['Cannot prove postcondition', 'fails on: f(0, 0)'],
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 })
                        @Ensures({ result == n * m + n + 1 })
                        static int f(int n, int m) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && s == k * m })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m && s == k * m + i })
                                @Decreases({ m - i })
                                while (i < m) { s = s + 1; i = i + 1 }
                                k = k + 1
                            }
                            int j = 0
                            @Invariant({ 0 <= j && j <= n && s == n * m + j })
                            @Decreases({ n - j })
                            while (j < n) { s = s + 1; j = j + 1 }
                            return s
                        }
                    }''')],
        [group: 'P338 a loop after a nested outer loop', name: 'a wrong inner invariant in the earlier loop is still caught', expect: 'Cannot prove loop invariant is preserved',
         src: tc('''class C {
                        @Requires({ n >= 1 && m >= 1 })
                        static int f(int n, int m) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && s == 0 })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= 0 })
                                @Decreases({ m - i })
                                while (i < m) { s = s + 1; i = i + 1 }
                                k = k + 1
                            }
                            int j = 0
                            @Invariant({ 0 <= j && j <= n && s == 0 })
                            @Decreases({ n - j })
                            while (j < n) { j = j + 1 }
                            return s
                        }
                    }''')],
        // t = 5 holds before the loops, but the inner loop counts t up.
        [group: 'P338 a loop after a nested outer loop', name: 'a fact the inner loop overwrites does not reach the later loop', expect: ['Cannot prove postcondition', 'fails on: f(1, 1)'],
         src: tc('''class C {
                        @Requires({ n >= 1 && m >= 1 })
                        @Ensures({ result == 5 })
                        static int f(int n, int m) {
                            int t = 5
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m })
                                @Decreases({ m - i })
                                while (i < m) { t = t + 1; i = i + 1 }
                                k = k + 1
                            }
                            int j = 0
                            @Invariant({ 0 <= j && j <= n })
                            @Decreases({ n - j })
                            while (j < n) { j = j + 1 }
                            return t
                        }
                    }''')],
        [group: 'P338 a loop after a nested outer loop', name: 'a fact nothing writes does', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 })
                        @Ensures({ result == 5 })
                        static int f(int n, int m) {
                            int t = 5
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m })
                                @Decreases({ m - i })
                                while (i < m) { s = s + 1; i = i + 1 }
                                k = k + 1
                            }
                            int j = 0
                            @Invariant({ 0 <= j && j <= n })
                            @Decreases({ n - j })
                            while (j < n) { j = j + 1 }
                            return t
                        }
                    }''')],
        [group: 'P338 a loop after a nested outer loop', name: 'array contents the earlier outer loop sets reach the later loop', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && n >= 0 && n <= a.length })
                        @Ensures({ result == 0 })
                        static int f(int[] a, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && (0..<k).every { int p -> a[p] == 0 } })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= 3 })
                                @Decreases({ 3 - i })
                                while (i < 3) { i = i + 1 }
                                a[k] = 0
                                k = k + 1
                            }
                            int s = 0
                            int j = 0
                            @Invariant({ 0 <= j && j <= n && s == 0 })
                            @Decreases({ n - j })
                            while (j < n) { s = s + a[j]; j = j + 1 }
                            return s
                        }
                    }''')],
        [group: 'P338 a loop after a nested outer loop', name: 'an early return in the later loop', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n, int m) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && s >= 0 })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m && s >= 0 })
                                @Decreases({ m - i })
                                while (i < m) { s = s + 1; i = i + 1 }
                                k = k + 1
                            }
                            int j = 0
                            @Invariant({ 0 <= j && j <= n && s >= 0 })
                            @Decreases({ n - j })
                            while (j < n) { if (s > 100) return s - 100; j = j + 1 }
                            return s
                        }
                    }''')],
        [group: 'P338 a loop after a nested outer loop', name: 'three loops: the nested one, then two plain ones', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 })
                        @Ensures({ result == n * m + 2 * n })
                        static int f(int n, int m) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && s == k * m })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m && s == k * m + i })
                                @Decreases({ m - i })
                                while (i < m) { s = s + 1; i = i + 1 }
                                k = k + 1
                            }
                            int j = 0
                            @Invariant({ 0 <= j && j <= n && s == n * m + j })
                            @Decreases({ n - j })
                            while (j < n) { s = s + 1; j = j + 1 }
                            int h = 0
                            @Invariant({ 0 <= h && h <= n && s == n * m + n + h })
                            @Decreases({ n - h })
                            while (h < n) { s = s + 1; h = h + 1 }
                            return s
                        }
                    }''')],
        [group: 'P338 a loop after a nested outer loop', name: 'two outer loops with nested loops, in sequence', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 })
                        @Ensures({ result == 2 * n * m })
                        static int f(int n, int m) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && s == k * m })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m && s == k * m + i })
                                @Decreases({ m - i })
                                while (i < m) { s = s + 1; i = i + 1 }
                                k = k + 1
                            }
                            int k2 = 0
                            @Invariant({ 0 <= k2 && k2 <= n && s == n * m + k2 * m })
                            @Decreases({ n - k2 })
                            while (k2 < n) {
                                int i2 = 0
                                @Invariant({ 0 <= i2 && i2 <= m && s == n * m + k2 * m + i2 })
                                @Decreases({ m - i2 })
                                while (i2 < m) { s = s + 1; i2 = i2 + 1 }
                                k2 = k2 + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P338 a loop after a nested outer loop', name: 'an unannotated inner loop still skips loudly', expect: 'Skipped loop verification',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            int s = 0
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                while (i < 3) { s = s + 1; i = i + 1 }
                                k = k + 1
                            }
                            int j = 0
                            @Invariant({ 0 <= j && j <= n })
                            @Decreases({ n - j })
                            while (j < n) { j = j + 1 }
                            return s
                        }
                    }''')],
    ]
}
