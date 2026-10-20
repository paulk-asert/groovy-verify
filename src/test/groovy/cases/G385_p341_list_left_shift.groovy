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
 * 'P341 list << in a loop body' — a statement xs << v skipped in any loop ("unsupported statement in loop region") and
 * in straight-line code ("statement with no modelled effect"). A left-nested chain xs << a << b on a variable is the
 * adds it makes (Encoder.leftShiftAdds): the loop engine applies them when xs is list-typed, the straight-line walk
 * when xs is declared a List or Set (the replay dispatches: a list appends, a set inserts), and a nested loop's
 * summary havocs the list. A StringBuilder's or an int's << is untouched and stays loud.
 */
class G385_p341_list_left_shift {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 341 list << in a loop body: xs << v (and a chain xs << a << b) on a list is xs.add(v), in a loop body, a nested loop (whose outer summary havocs the list) and straight-line code; on a declared Set it inserts. Sizes and appended elements are threaded as for add. A StringBuilder\'s or an int\'s << is not an add and still skips loudly.'

    static final List<Map> CASES = [

        // out << k is out.add(k): the size and the appended element are threaded.
        [group: 'P341 list << in a loop body', name: 'a loop appending with <<', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.size() == n })
                        static List<Integer> f(int n) {
                            List<Integer> out = []
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && out.size() == k })
                            @Decreases({ n - k })
                            while (k < n) { out << k; k = k + 1 }
                            return out
                        }
                    }''')],
        [group: 'P341 list << in a loop body', name: 'the elements appended with <<', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.size() == n && (0..<n).every { int p -> result[p] == 2 * p } })
                        static List<Integer> f(int n) {
                            List<Integer> out = []
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && out.size() == k && (0..<k).every { int p -> out[p] == 2 * p } })
                            @Decreases({ n - k })
                            while (k < n) { out << 2 * k; k = k + 1 }
                            return out
                        }
                    }''')],
        [group: 'P341 list << in a loop body', name: 'a wrong size after << refutes', expect: ['Cannot prove postcondition', 'fails on: f(1)'],
         src: tc('''class C {
                        @Requires({ n >= 1 })
                        @Ensures({ result.size() == n + 1 })
                        static List<Integer> f(int n) {
                            List<Integer> out = []
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && out.size() == k })
                            @Decreases({ n - k })
                            while (k < n) { out << k; k = k + 1 }
                            return out
                        }
                    }''')],
        [group: 'P341 list << in a loop body', name: 'a chained << appends each operand', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.size() == 2 * n })
                        static List<Integer> f(int n) {
                            List<Integer> out = []
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && out.size() == 2 * k })
                            @Decreases({ n - k })
                            while (k < n) { out << k << k; k = k + 1 }
                            return out
                        }
                    }''')],
        [group: 'P341 list << in a loop body', name: 'a nested loop appending with <<', ok: true,
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
                                while (i < m) { out << i; i = i + 1 }
                                k = k + 1
                            }
                            return out
                        }
                    }''')],
        // The size is not kept from before the loops: the nested loop changes it.
        [group: 'P341 list << in a loop body', name: 'the outer summary havocs a list the nested loop appends to', expect: ['Cannot prove postcondition', 'fails on: f(1, 1)'],
         src: tc('''class C {
                        @Requires({ n >= 1 && m >= 1 })
                        @Ensures({ result.size() == 0 })
                        static List<Integer> f(int n, int m) {
                            List<Integer> out = []
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) {
                                int i = 0
                                @Invariant({ 0 <= i && i <= m })
                                @Decreases({ m - i })
                                while (i < m) { out << i; i = i + 1 }
                                k = k + 1
                            }
                            return out
                        }
                    }''')],
        [group: 'P341 list << in a loop body', name: '<< in straight-line code', ok: true,
         src: tc('''class C {
                        @Ensures({ result.size() == 2 })
                        static List<Integer> f() {
                            List<Integer> out = []
                            out << 1
                            out << 2
                            return out
                        }
                    }''')],
        [group: 'P341 list << in a loop body', name: '<< on a list parameter', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 0 })
                        @Ensures({ xs.size() == 1 })
                        static void f(List<Integer> xs) {
                            xs << 5
                        }
                    }''')],
        [group: 'P341 list << in a loop body', name: '<< on a set parameter inserts', ok: true,
         src: tc('''class C {
                        @Requires({ st != null })
                        @Ensures({ st.contains(1) })
                        static void f(Set<Integer> st) {
                            st << 1
                        }
                    }''')],
        [group: 'P341 list << in a loop body', name: 'a wrong claim after a set << refutes', expect: ['Cannot prove postcondition', 'fails on: f([] as Set)'],
         src: tc('''class C {
                        @Requires({ st != null })
                        @Ensures({ st.contains(2) })
                        static void f(Set<Integer> st) {
                            st << 1
                        }
                    }''')],
        // Only a declared List or Set receiver is an add: a StringBuilder appends text.
        [group: 'P341 list << in a loop body', name: '<< on a StringBuilder still skips loudly', expect: 'statement with no modelled effect',
         src: tc('''class C {
                        @Requires({ sb != null })
                        @Ensures({ result == 1 })
                        static int f(StringBuilder sb) {
                            sb << 'abc'
                            return 1
                        }
                    }''')],
        [group: 'P341 list << in a loop body', name: 'a shift statement on an int still skips loudly', expect: 'statement with no modelled effect',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() {
                            int k = 1
                            k << 2
                            return k
                        }
                    }''')],
    ]
}
