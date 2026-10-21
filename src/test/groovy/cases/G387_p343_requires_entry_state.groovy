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
 * 'P343 @Requires is about the entry state' — the post-loop check, in-body exits and loop-region obligations
 * asserted the whole @Requires over the current state's symbols, so a parameter, field or collection the prefix or
 * the loop writes kept its entry fact: long-standing silent false proofs. Every non-entry context now assumes only
 * the conjuncts the writes before it leave standing (VerifyChecker.loopStableRequires, Phase 64's filter, now
 * shape-aware and used everywhere): a value-type parameter never reassigned keeps every fact, any parameter never
 * reassigned its nullness and an array its length, and contents, sizes and fields need a bounded write set they are
 * absent from. A nested loop is judged by its outer loop's writes. A repro takes a written parameter's input from a
 * model of @Requires, since the failure model holds its value at the failure.
 */
class G387_p343_requires_entry_state {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 343 @Requires is about the entry state: a parameter, field or collection the method writes before or in a loop no longer keeps its entry @Requires fact after the loop, at an in-body return, in body obligations or in nested loops (it did: @Requires({ x == 0 }) with x = x + 1 in the loop proved result == 0). A never-reassigned value parameter keeps every fact, an array stored into its length and nullness. Failing calls take a written parameter\'s input from @Requires (f(0, 1), not its post-loop value).'

    static final List<Map> CASES = [

        // Unsound before: @Requires({ x == 0 }) was assumed of the post-loop x, so result == 0 proved although f(0, 1) returns 1. The repro takes x from @Requires: the model x = 1 is its value after the loop.
        [group: 'P343 @Requires is about the entry state', name: 'a parameter the loop increments is not its entry value after the loop', expect: ['Cannot prove postcondition', 'fails on: f(0, 1)'],
         src: tc('''class C {
                        @Requires({ x == 0 && n >= 1 })
                        @Ensures({ result == 0 })
                        static int f(int x, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && x >= 0 })
                            @Decreases({ n - k })
                            while (k < n) { x = x + 1; k = k + 1 }
                            return x
                        }
                    }''')],
        // Unsound before: x = 5 against x == 0 made the post-loop context vacuous, so result == 99 proved.
        [group: 'P343 @Requires is about the entry state', name: 'a parameter set before the loop no longer contradicts its entry fact', expect: ['Cannot prove postcondition', 'fails on: f(0, 1)'],
         src: tc('''class C {
                        @Requires({ x == 0 && n >= 1 })
                        @Ensures({ result == 99 })
                        static int f(int x, int n) {
                            x = 5
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) { k = k + 1 }
                            return x
                        }
                    }''')],
        [group: 'P343 @Requires is about the entry state', name: 'an in-body return sees the written parameter, not its entry value', expect: ['Cannot prove postcondition', 'fails on: f(0, 2)'],
         src: tc('''class C {
                        @Requires({ x == 0 && n >= 2 })
                        @Ensures({ result == 0 })
                        static int f(int x, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && x == k })
                            @Decreases({ n - k })
                            while (k < n) { if (k == 1) return x; x = x + 1; k = k + 1 }
                            return 0
                        }
                    }''')],
        [group: 'P343 @Requires is about the entry state', name: 'a body bounds check sees the written index, not its entry value', expect: ['Possible IndexOutOfBoundsException', 'fails on: f(new int[1], 0, 2)'],
         src: tc('''class C {
                        @Requires({ a != null && a.length == 1 && x == 0 && n >= 2 })
                        static void f(int[] a, int x, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && x >= 0 })
                            @Decreases({ n - k })
                            while (k < n) { a[x] = 1; x = x + 1; k = k + 1 }
                        }
                    }''')],
        [group: 'P343 @Requires is about the entry state', name: 'a set the loop adds to is no longer empty after it', expect: ['Cannot prove postcondition', 'fails on: f([] as Set, 1)'],
         src: tc('''class C {
                        @Requires({ st != null && st.isEmpty() && n >= 1 })
                        @Ensures({ st.isEmpty() })
                        static void f(Set<Integer> st, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) { st.add(k); k = k + 1 }
                        }
                    }''')],
        // The repro takes the list from @Requires (empty): the model held its size after the loop.
        [group: 'P343 @Requires is about the entry state', name: 'a list the loop adds to is no longer empty after it', expect: ['Cannot prove postcondition', 'fails on: f([], 1)'],
         src: tc('''class C {
                        @Requires({ xs != null && xs.isEmpty() && n >= 1 })
                        @Ensures({ xs.isEmpty() })
                        static void f(List<Integer> xs, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) { xs.add(k); k = k + 1 }
                        }
                    }''')],
        [group: 'P343 @Requires is about the entry state', name: 'a set a nested loop adds to is no longer empty after it', expect: ['Cannot prove postcondition', 'fails on: f([] as Set, 1, 1)'],
         src: tc('''class C {
                        @Requires({ st != null && st.isEmpty() && n >= 1 && m >= 1 })
                        @Ensures({ st.isEmpty() })
                        static void f(Set<Integer> st, int n, int m) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m })
                                @Decreases({ m - i })
                                while (i < m) { st.add(i); i = i + 1 }
                                k = k + 1
                            }
                        }
                    }''')],
        [group: 'P343 @Requires is about the entry state', name: 'an array parameter the loop reassigns loses its entry length', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ a != null && a.length == 1 && n >= 1 })
                        @Ensures({ result == 1 })
                        static int f(int[] a, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && a != null })
                            @Decreases({ n - k })
                            while (k < n) { a = new int[5]; k = k + 1 }
                            return a.length
                        }
                    }''')],
        [group: 'P343 @Requires is about the entry state', name: 'preservation does not assume a parameter the prefix wrote', expect: ['Cannot prove loop invariant is preserved', 'fails on: f(0, 1)'],
         src: tc('''class C {
                        @Requires({ x == 0 && n >= 1 })
                        static void f(int x, int n) {
                            x = 5
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && x == 5 })
                            @Decreases({ n - k })
                            while (k < n) { x = 7; k = k + 1 }
                        }
                    }''')],
        // A content write cannot change an array's length or nullness, so those @Requires facts hold at every iteration.
        [group: 'P343 @Requires is about the entry state', name: 'an array stored into keeps its entry length and nullness', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && a.length == n && n >= 0 })
                        @Ensures({ a.length == n && (0..<n).every { int p -> a[p] == 0 } })
                        static void f(int[] a, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && (0..<k).every { int p -> a[p] == 0 } })
                            @Decreases({ n - k })
                            while (k < n) { a[k] = 0; k = k + 1 }
                        }
                    }''')],
    ]
}
