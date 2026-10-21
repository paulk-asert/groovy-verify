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
 * 'P342 set << in a loop body' — in a loop body a set's add, remove and clear went down the list-mutation path
 * (LoopEncoder.applyListMutationInLoop), which writes the list oracles: the set model (membership, cardinality) saw
 * no change, so st.isEmpty() and !st.contains(0) were preserved through st.add(k), a silent unsoundness. A set's add
 * and remove now apply its own store and cardinality law, as the straight-line replay does; clear and other set
 * mutators are refused (loud). xs << v on a set is that add, and a nested loop's summary havocs the set itself.
 */
class G386_p342_set_left_shift {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 342 set << in a loop body: a set\'s add, remove and << in a loop body update its membership and cardinality (a duplicate add leaves the size alone), and a nested loop\'s summary havocs the set. Unsound before: the loop engine sent a set\'s add down the list path, so the set looked unchanged and st.isEmpty() survived an add. A set\'s clear in a loop skips loudly.'

    static final List<Map> CASES = [

        // It failed to preserve: the add wrote only the list oracles, so contains never saw it.
        [group: 'P342 set << in a loop body', name: 'a set add in a loop keeps what it inserted', ok: true,
         src: tc('''class C {
                        @Requires({ st != null && n >= 0 })
                        @Ensures({ (0..<n).every { int p -> st.contains(p) } })
                        static void f(Set<Integer> st, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && (0..<k).every { int p -> st.contains(p) } })
                            @Decreases({ n - k })
                            while (k < n) { st.add(k); k = k + 1 }
                        }
                    }''')],
        [group: 'P342 set << in a loop body', name: 'a set << in a loop', ok: true,
         src: tc('''class C {
                        @Requires({ st != null && n >= 0 })
                        @Ensures({ (0..<n).every { int p -> st.contains(p) } })
                        static void f(Set<Integer> st, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && (0..<k).every { int p -> st.contains(p) } })
                            @Decreases({ n - k })
                            while (k < n) { st << k; k = k + 1 }
                        }
                    }''')],
        [group: 'P342 set << in a loop body', name: 'a set size grows by at most one per add', ok: true,
         src: tc('''class C {
                        @Requires({ st != null && st.isEmpty() && n >= 0 })
                        @Ensures({ st.size() <= n })
                        static void f(Set<Integer> st, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && st.size() <= k })
                            @Decreases({ n - k })
                            while (k < n) { st.add(k % 3); k = k + 1 }
                        }
                    }''')],
        // Unsound before: the add was invisible to the set model, so st.isEmpty() was preserved and proved.
        [group: 'P342 set << in a loop body', name: 'a set no longer stays empty after an add', expect: ['Cannot prove loop invariant is preserved', 'fails on: f([] as Set, 1)'],
         src: tc('''class C {
                        @Requires({ st != null && st.isEmpty() && n >= 1 })
                        @Ensures({ st.isEmpty() })
                        static void f(Set<Integer> st, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && st.isEmpty() })
                            @Decreases({ n - k })
                            while (k < n) { st.add(k); k = k + 1 }
                        }
                    }''')],
        // Unsound before, the same way: !st.contains(0) survived st.add(0).
        [group: 'P342 set << in a loop body', name: 'a set no longer misses an element it inserted', expect: 'Cannot prove loop invariant is preserved',
         src: tc('''class C {
                        @Requires({ st != null && !st.contains(0) && n >= 1 })
                        @Ensures({ !st.contains(0) })
                        static void f(Set<Integer> st, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && !st.contains(0) })
                            @Decreases({ n - k })
                            while (k < n) { st.add(k); k = k + 1 }
                        }
                    }''')],
        [group: 'P342 set << in a loop body', name: 'adding a duplicate does not grow the set', expect: 'Cannot prove loop invariant is preserved',
         src: tc('''class C {
                        @Requires({ st != null && st.isEmpty() && n >= 0 })
                        @Ensures({ st.size() == n })
                        static void f(Set<Integer> st, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && st.size() == k })
                            @Decreases({ n - k })
                            while (k < n) { st.add(k % 3); k = k + 1 }
                        }
                    }''')],
        [group: 'P342 set << in a loop body', name: 'a wrong membership claim refutes', expect: ['Cannot prove postcondition', 'fails on: f([] as Set, 1)'],
         src: tc('''class C {
                        @Requires({ st != null && n >= 1 })
                        @Ensures({ st.contains(n) })
                        static void f(Set<Integer> st, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) { st.add(k); k = k + 1 }
                        }
                    }''')],
        [group: 'P342 set << in a loop body', name: 'a set remove in a loop', ok: true,
         src: tc('''class C {
                        @Requires({ st != null && n >= 0 })
                        @Ensures({ (0..<n).every { int p -> !st.contains(p) } })
                        static void f(Set<Integer> st, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && (0..<k).every { int p -> !st.contains(p) } })
                            @Decreases({ n - k })
                            while (k < n) { st.remove(k); k = k + 1 }
                        }
                    }''')],
        [group: 'P342 set << in a loop body', name: 'a set field add in a loop', ok: true,
         src: tc('''class C {
                        Set<Integer> seen = new HashSet<Integer>()
                        @Requires({ seen != null && n >= 1 })
                        @Ensures({ seen.contains(0) })
                        void f(int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && (k == 0 || seen.contains(0)) })
                            @Decreases({ n - k })
                            while (k < n) { seen.add(k); k = k + 1 }
                        }
                    }''')],
        [group: 'P342 set << in a loop body', name: 'a set field no longer stays empty after an add', expect: 'Cannot prove loop invariant is preserved',
         src: tc('''class C {
                        Set<Integer> seen = new HashSet<Integer>()
                        @Requires({ seen != null && seen.isEmpty() && n >= 1 })
                        @Ensures({ seen.isEmpty() })
                        void f(int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n && seen.isEmpty() })
                            @Decreases({ n - k })
                            while (k < n) { seen.add(k); k = k + 1 }
                        }
                    }''')],
        // clear went down the list path too (list size 0, set untouched); it is now refused.
        [group: 'P342 set << in a loop body', name: 'a set clear in a loop skips loudly', expect: 'Skipped loop verification',
         src: tc('''class C {
                        @Requires({ st != null && n >= 1 })
                        @Ensures({ st.contains(5) })
                        static void f(Set<Integer> st, int n) {
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) { st.clear(); k = k + 1 }
                        }
                    }''')],
    ]
}
