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
 * 'P345 for-in over a range' — a for-in was modelled only over a named collection, so for (i in 0..<n), the commonest
 * Groovy counting loop, skipped the method ("unsupported statement ForStatement"). ContractExpansionTransform now
 * desugars a range for-in to a counting while with i itself the counter (auto invariant lo <= i <= hi, variant
 * hi - i), and establishment checks the range runs forwards (LoopSpec.rangeForward), since Groovy iterates a range
 * whose upper bound is below its lower one backwards.
 */
class G389_p345_range_for_in {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 345 for-in over a range: for (i in lo..<hi) and lo..hi (and (lo..<hi).each) desugar to a counting loop with i the counter, carrying an auto bounds invariant and variant, so an @Invariant over i is a loop-head invariant; establishment checks the range runs forwards (lo <= hi, and hi < Integer.MAX_VALUE for an inclusive range), since Groovy iterates 0..<n downwards when n < 0 and 1..0 is [1, 0]. A body that assigns the loop variable or writes what the bounds read skips loudly.'

    static final List<Map> CASES = [

        // for (int i in 0..<n) is int i = 0; while (i < n) { body; i = i + 1 }: i is the counter, so the invariant speaks of it at the loop head.
        [group: 'P345 for-in over a range', name: 'a count over 0..<n', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int f(int n) {
                            int s = 0
                            @Invariant({ 0 <= i && i <= n && s == i })
                            for (int i in 0..<n) { s = s + 1 }
                            return s
                        }
                    }''')],
        [group: 'P345 for-in over a range', name: 'literal bounds', ok: true,
         src: tc('''class C {
                        @Requires({ true })
                        @Ensures({ result == 10 })
                        static int f() {
                            int s = 0
                            @Invariant({ 0 <= i && i <= 10 && s == i })
                            for (int i in 0..<10) { s = s + 1 }
                            return s
                        }
                    }''')],
        [group: 'P345 for-in over a range', name: 'an untyped variable over 0..<a.length', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 })
                        static int f(int[] a) {
                            int s = 0
                            @Invariant({ s >= 0 })
                            for (i in 0..<a.length) { s = s + (a[i] > 0 ? a[i] : 0) }
                            return s
                        }
                    }''')],
        [group: 'P345 for-in over a range', name: 'a prefix sum over an array', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == a.sum() })
                        static int f(int[] a) {
                            int s = 0
                            @Invariant({ 0 <= i && i <= a.length && s == a[0..<i].sum(0) })
                            for (int i in 0..<a.length) { s = s + a[i] }
                            return s
                        }
                    }''')],
        [group: 'P345 for-in over a range', name: 'an inclusive 1..n', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 1 && n < 1000 })
                        @Ensures({ result == n })
                        static int f(int n) {
                            int s = 0
                            @Invariant({ 1 <= i && i <= n + 1 && s == i - 1 })
                            for (int i in 1..n) { s = s + 1 }
                            return s
                        }
                    }''')],
        [group: 'P345 for-in over a range', name: 'continue and break in a range loop', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result <= 5 })
                        static int f(int n) {
                            int s = 0
                            @Invariant({ 0 <= i && i <= n && s <= 5 && s <= i })
                            for (int i in 0..<n) {
                                if (i % 2 == 0) continue
                                if (s == 5) break
                                s = s + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P345 for-in over a range', name: 'nested range loops', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 })
                        @Ensures({ result == n * m })
                        static int f(int n, int m) {
                            int c = 0
                            @Invariant({ 0 <= i && i <= n && c == i * m })
                            for (int i in 0..<n) {
                                @Invariant({ 0 <= j && j <= m && c == i * m + j })
                                for (int j in 0..<m) { c = c + 1 }
                            }
                            return c
                        }
                    }''')],
        [group: 'P345 for-in over a range', name: 'sequential range loops', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == 2 * n })
                        static int f(int n) {
                            int s = 0
                            @Invariant({ 0 <= i && i <= n && s == i })
                            for (int i in 0..<n) { s = s + 1 }
                            @Invariant({ 0 <= j && j <= n && s == n + j })
                            for (int j in 0..<n) { s = s + 1 }
                            return s
                        }
                    }''')],
        [group: 'P345 for-in over a range', name: '(0..<n).each is the same loop', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == 0 })
                        static int f(int n) {
                            (0..<n).each { int i -> assert i < n }
                            return 0
                        }
                    }''')],
        [group: 'P345 for-in over a range', name: 'a false assert in (0..<n).each refutes', expect: ['Assertion may not hold', 'fails on: f(1)'],
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == 0 })
                        static int f(int n) {
                            (0..<n).each { int i -> assert i < n - 1 }
                            return 0
                        }
                    }''')],
        [group: 'P345 for-in over a range', name: 'a wrong invariant refutes', expect: ['Cannot prove loop invariant holds on entry', 'fails on: f(0)'],
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int f(int n) {
                            int s = 0
                            @Invariant({ 0 <= i && i <= n && s == i + 1 })
                            for (int i in 0..<n) { s = s + 1 }
                            return s
                        }
                    }''')],
        // Groovy iterates 0..<n downwards when n < 0 (0..<-2 is [0, -1]), which the counting loop does not model: lo <= hi is checked at entry.
        [group: 'P345 for-in over a range', name: 'a range that may run backwards refutes', expect: ['Cannot prove the for-in range runs forwards', 'needs: (0 <= n)'],
         src: tc('''class C {
                        @Requires({ true })
                        @Ensures({ result == n })
                        static int f(int n) {
                            int s = 0
                            @Invariant({ s == i })
                            for (int i in 0..<n) { s = s + 1 }
                            return s
                        }
                    }''')],
        // 1..0 is [1, 0], not empty: the classic 1..n edge.
        [group: 'P345 for-in over a range', name: '1..n with n == 0 runs backwards', expect: ['Cannot prove the for-in range runs forwards', 'fails on: f(0)'],
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int f(int n) {
                            int s = 0
                            @Invariant({ 1 <= i && i <= n + 1 && s == i - 1 })
                            for (int i in 1..n) { s = s + 1 }
                            return s
                        }
                    }''')],
        [group: 'P345 for-in over a range', name: '0..n - 1 with n == 0 runs backwards, and an off-by-one store refutes', expect: ['Possible IndexOutOfBoundsException', 'fails on: f(1)', 'Cannot prove the for-in range runs forwards', 'fails on: f(0)'],
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.length == n })
                        static int[] f(int n) {
                            int[] r = new int[n]
                            for (i in 0..n - 1) { r[i + 1] = i }
                            return r
                        }
                    }''')],
        [group: 'P345 for-in over a range', name: 'a nested range that may run backwards refutes', expect: ['Cannot prove the for-in range runs forwards', 'fails on: f(1)'],
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int c = 0
                            @Invariant({ 0 <= i && i <= n && c >= 0 })
                            for (int i in 0..<n) {
                                @Invariant({ c >= 0 })
                                for (int j in 0..<i - 1) { c = c + 1 }
                            }
                            return c
                        }
                    }''')],
        // The counter would reach hi + 1 at exit, which an int cannot hold.
        [group: 'P345 for-in over a range', name: 'an inclusive range up to Integer.MAX_VALUE refutes', expect: ['Cannot prove the for-in range runs forwards', 'fails on: f(2147483647)'],
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            @Invariant({ s >= 0 })
                            for (int i in 0..n) { s = 1 }
                            return s
                        }
                    }''')],
        [group: 'P345 for-in over a range', name: 'a body that assigns the loop variable skips loudly', expect: 'the body assigns the range for-in variable',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            @Invariant({ s >= 0 })
                            for (int i in 0..<n) { s = s + 1; i = i + 1 }
                            return s
                        }
                    }''')],
        [group: 'P345 for-in over a range', name: 'a body that writes a bound skips loudly', expect: 'which are evaluated once',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            int m = n
                            @Invariant({ s >= 0 })
                            for (int i in 0..<m) { s = s + 1; m = m - 1 }
                            return s
                        }
                    }''')],
        [group: 'P345 for-in over a range', name: 'an accumulating body with no invariant skips loudly', expect: 'needs an @Invariant to frame it',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.length == n })
                        static int[] f(int n) {
                            int[] r = new int[n]
                            for (i in 0..<n) { r[i] = i }
                            return r
                        }
                    }''')],
    ]
}
