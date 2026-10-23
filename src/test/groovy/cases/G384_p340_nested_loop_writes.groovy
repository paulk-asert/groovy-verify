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
 * 'P340 nested loop writing a field or collection' — an outer loop's summary of its nested loop (havoc what it
 * writes) bailed on this.f = v, m.put(k, v) and xs.set(i, v) ("nested loop writes a field/collection or unbounded
 * construct"), and the loop engine could not execute them as body statements either. They are now the stores they
 * are: f = v, m[k] = v, xs[i] = v (LoopEncoder.asStore), with List.set's bounds obligation. En route: the write set of
 * an outer loop holding a nested loop read the nested loop's raw block, where groovy-contracts weaves its invariant
 * checks, so it bailed and the outer loop had no frame facts (out != null lost); and a void method with @Ensures
 * after a loop skipped ("no return value after loop").
 */
class G384_p340_nested_loop_writes {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 340 nested loop writing a field or collection: a nested loop may assign this.field, put into a map, set or add list elements, or store into a field array; the outer loop havocs those writes in its summary, so the outer invariant and later code see them, and a fact the nested loop overwrites is not kept. List.set(i, v) carries its bounds obligation, in loops and straight-line code. A void method\'s @Ensures over fields is checked after a loop. List << in a loop body still skips loudly.'

    static final List<Map> CASES = [

        // this.count = this.count + 1 is count = count + 1: the summary havocs the field, the inner invariant keeps count >= 0.
        [group: 'P340 nested loop writing a field or collection', name: 'a nested loop writing this.field', ok: true,
         src: tc('''class C {
                        int count = 0
                        @Requires({ n >= 0 && m >= 0 && count >= 0 })
                        @Ensures({ count >= 0 })
                        void f(int n, int m) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && count >= 0 })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m && count >= 0 })
                                @Decreases({ m - i })
                                while (i < m) { this.count = this.count + 1; i = i + 1 }
                                k = k + 1
                            }
                        }
                    }''')],
        [group: 'P340 nested loop writing a field or collection', name: 'the exact count through this.field', ok: true,
         src: tc('''class C {
                        int count = 0
                        @Requires({ n >= 0 && m >= 0 && count == 0 })
                        @Ensures({ count == n * m })
                        void f(int n, int m) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && count == k * m })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m && count == k * m + i })
                                @Decreases({ m - i })
                                while (i < m) { this.count = this.count + 1; i = i + 1 }
                                k = k + 1
                            }
                        }
                    }''')],
        [group: 'P340 nested loop writing a field or collection', name: 'a nested loop writing a bare field', ok: true,
         src: tc('''class C {
                        int count = 0
                        @Requires({ n >= 0 && m >= 0 && count >= 0 })
                        @Ensures({ count >= 0 })
                        void f(int n, int m) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && count >= 0 })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m && count >= 0 })
                                @Decreases({ m - i })
                                while (i < m) { count = count + 1; i = i + 1 }
                                k = k + 1
                            }
                        }
                    }''')],
        [group: 'P340 nested loop writing a field or collection', name: 'a wrong claim about the field refutes', expect: ['Cannot prove postcondition', 'fails on: f(1, 1)'],
         src: tc('''class C {
                        int count = 0
                        @Requires({ n >= 1 && m >= 1 && count >= 0 })
                        @Ensures({ count == 0 })
                        void f(int n, int m) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && count >= 0 })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m && count >= 0 })
                                @Decreases({ m - i })
                                while (i < m) { this.count = this.count + 1; i = i + 1 }
                                k = k + 1
                            }
                        }
                    }''')],
        [group: 'P340 nested loop writing a field or collection', name: 'a field fact a nested loop changes does not reach the later loop', expect: ['Cannot prove postcondition', 'fails on: f(1, 1)'],
         src: tc('''class C {
                        int count = 0
                        @Requires({ n >= 1 && m >= 1 })
                        @Ensures({ count == 3 })
                        void f(int n, int m) {
                            count = 3
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m })
                                @Decreases({ m - i })
                                while (i < m) { this.count = this.count + 1; i = i + 1 }
                                k = k + 1
                            }
                            int j = 0
                            @Invariant({ 0 <= j && j <= n })
                            @Decreases({ n - j })
                            while (j < n) { j = j + 1 }
                        }
                    }''')],
        // out.size() == n * m; out != null is a frame fact of the outer loop, which its nested loop used to hide.
        [group: 'P340 nested loop writing a field or collection', name: 'a nested loop building a list', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 })
                        @Ensures({ result.size() == n * m })
                        static List<Integer> f(int n, int m) {
                            List<Integer> out = []
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && out.size() == k * m })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m && out.size() == k * m + i })
                                @Decreases({ m - i })
                                while (i < m) { out.add(i); i = i + 1 }
                                k = k + 1
                            }
                            return out
                        }
                    }''')],
        [group: 'P340 nested loop writing a field or collection', name: 'a nested loop adding to a list field', ok: true,
         src: tc('''class C {
                        List<Integer> log = []
                        @Requires({ n >= 0 && m >= 0 && log != null })
                        void f(int n, int m) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m })
                                @Decreases({ m - i })
                                while (i < m) { log.add(i); i = i + 1 }
                                k = k + 1
                            }
                        }
                    }''')],
        [group: 'P340 nested loop writing a field or collection', name: 'a nested loop putting into a map', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 && mp != null })
                        static void f(int n, int m, Map<Integer, Integer> mp) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m })
                                @Decreases({ m - i })
                                while (i < m) { mp.put(i, k); i = i + 1 }
                                k = k + 1
                            }
                        }
                    }''')],
        [group: 'P340 nested loop writing a field or collection', name: 'a map key the nested loop overwrites refutes the old value', expect: ['Cannot prove postcondition', 'fails on: f(1, 1, [:])'],
         src: tc('''class C {
                        @Requires({ n >= 1 && m >= 1 && mp != null })
                        @Ensures({ mp.get(0) == 7 })
                        static void f(int n, int m, Map<Integer, Integer> mp) {
                            mp.put(0, 7)
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m })
                                @Decreases({ m - i })
                                while (i < m) { mp.put(0, i + 100); i = i + 1 }
                                k = k + 1
                            }
                        }
                    }''')],
        [group: 'P340 nested loop writing a field or collection', name: 'a nested loop setting list elements in bounds', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && n >= 0 && xs.size() >= n })
                        static void f(List<Integer> xs, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= k })
                                @Decreases({ k - i })
                                while (i < k) { xs.set(i, 0); i = i + 1 }
                                k = k + 1
                            }
                        }
                    }''')],
        // Phase 385: the call is now an exact run's (`f([null, null], 1)` fails too: xs[0] is 5 after the loop); any list will do
        [group: 'P340 nested loop writing a field or collection', name: 'a list element the nested loop overwrites refutes the old value', expect: ['Cannot prove postcondition', 'fails on: f(['],
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() >= 2 && n >= 1 })
                        @Ensures({ xs[0] == 0 })
                        static void f(List<Integer> xs, int n) {
                            xs.set(0, 0)
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= 1 })
                                @Decreases({ 1 - i })
                                while (i < 1) { xs.set(0, 5); i = i + 1 }
                                k = k + 1
                            }
                        }
                    }''')],
        [group: 'P340 nested loop writing a field or collection', name: 'an out-of-bounds set in a nested loop refutes', expect: ['Possible IndexOutOfBoundsException', 'fails on: f([], 2)'],
         src: tc('''class C {
                        @Requires({ xs != null && n >= 0 })
                        static void f(List<Integer> xs, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= k })
                                @Decreases({ k - i })
                                while (i < k) { xs.set(i, 0); i = i + 1 }
                                k = k + 1
                            }
                        }
                    }''')],
        // It had no bounds obligation at all (xs[i] = v did).
        [group: 'P340 nested loop writing a field or collection', name: 'List.set out of bounds refutes in straight-line code too', expect: ['Possible IndexOutOfBoundsException', 'fails on: g([], -1)'],
         src: tc('''class C {
                        @Requires({ xs != null })
                        static void g(List<Integer> xs, int i) { xs.set(i, 0) }
                    }''')],
        [group: 'P340 nested loop writing a field or collection', name: 'a nested loop writing a field array', ok: true,
         src: tc('''class C {
                        int[] grid = new int[10]
                        @Requires({ n >= 0 && m >= 0 && grid != null && grid.length >= n * m })
                        void f(int n, int m) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m })
                                @Decreases({ m - i })
                                while (i < m) { grid[k * m + i] = 1; i = i + 1 }
                                k = k + 1
                            }
                        }
                    }''')],
        // Skipped before with "no return value after loop": a void method has no result to bind.
        [group: 'P340 nested loop writing a field or collection', name: 'a void method\'s @Ensures after a loop', ok: true,
         src: tc('''class C {
                        int count = 0
                        @Requires({ n >= 0 && count >= 0 })
                        @Ensures({ count >= 0 })
                        void f(int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && count >= 0 })
                            @Decreases({ n - k })
                            while (k < n) { count = count + 1; k = k + 1 }
                        }
                    }''')],
        [group: 'P340 nested loop writing a field or collection', name: 'a wrong void @Ensures after a loop refutes', expect: ['Cannot prove postcondition', 'fails on: f(1)'],
         src: tc('''class C {
                        int count = 0
                        @Requires({ n >= 1 && count >= 0 })
                        @Ensures({ count == -1 })
                        void f(int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && count >= 0 })
                            @Decreases({ n - k })
                            while (k < n) { count = count + 1; k = k + 1 }
                        }
                    }''')],
    ]
}
