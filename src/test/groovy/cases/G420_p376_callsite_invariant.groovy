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
 * 'P376 call-site invariant' — a callee's precondition was checked at a call site from the caller's @Requires alone:
 * the class invariants, which every other check assumes on entry, weren't, so under `@Invariant({ data.length == n })`
 * a call `bump(data, i)` needing `i < a.length` was refuted with a state the invariant rules out (the ClearSplit
 * port's second finding). They are now assumed (not in a constructor, which hasn't established them), and a
 * `this.data` actual is the field's array as `data` is.
 */
class G420_p376_callsite_invariant {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 376: a callee precondition at a call site is checked under the class invariants (not in a constructor), and a `this.f` argument reads the field\'s oracles as `f` does.'

    static final String BUMP = '''
                        @Requires({ a != null && 0 <= i && i < a.length })
                        @Ensures({ result != null && result.length == a.length })
                        static int[] bump(int[] a, int i) { int[] r = new int[a.length]; r }'''

    static final List<Map> CASES = [

        // Before: refuted, falsely (`data.size() = 0, n = 1`).
        [group: "P376 call-site invariant", name: "an array field's length under the class invariant",
         ok: true,
         src: tc("""@Invariant({ n >= 0 && data != null && data.length == n })
                    class A {
                        int n
                        int[] data${BUMP}
                        @Requires({ 0 <= i && i < n })
                        void direct(int i) { data = bump(data, i) }
                    }""")],

        // Before: refuted, falsely.
        [group: "P376 call-site invariant", name: "… passed as this.data",
         ok: true,
         src: tc("""@Invariant({ n >= 0 && data != null && data.length == n })
                    class A {
                        int n
                        int[] data${BUMP}
                        @Requires({ 0 <= i && i < n })
                        void viaThis(int i) { data = bump(this.data, i) }
                    }""")],

        // Before: refuted, falsely.
        [group: "P376 call-site invariant", name: "… through a local alias",
         ok: true,
         src: tc("""@Invariant({ n >= 0 && data != null && data.length == n })
                    class A {
                        int n
                        int[] data${BUMP}
                        @Requires({ 0 <= i && i < n })
                        void viaLocal(int i) { int[] d = data; data = bump(d, i) }
                    }""")],

        // The invariant gives the length; the caller's own bound still has to meet it.
        [group: "P376 call-site invariant", name: "an index the invariant doesn't cover",
         expect: ["Cannot prove precondition of bump at this call site", "fails on: direct(0)"],
         src: tc("""@Invariant({ n >= 0 && data != null && data.length == n })
                    class A {
                        int n
                        int[] data${BUMP}
                        @Requires({ 0 <= i && i <= n })
                        void direct(int i) { data = bump(data, i) }
                    }""")],

        // Before: refuted, falsely (`cap = 0`).
        [group: "P376 call-site invariant", name: "a scalar field under the class invariant",
         ok: true,
         src: tc('''@Invariant({ cap > 0 })
                    class A {
                        int cap = 1
                        @Requires({ x > 0 })
                        static int g(int x) { 100.intdiv(x) }
                        int f() { g(cap) }
                    }''')],

        // The invariant holds at entry; a write before the call is replayed over it.
        [group: "P376 call-site invariant", name: "a field written before the call",
         expect: ["Cannot prove precondition of g at this call site", "fails on: f()"],
         src: tc('''@Invariant({ cap > 0 })
                    class A {
                        int cap = 1
                        @Requires({ x > 0 })
                        static int g(int x) { 100.intdiv(x) }
                        int f() {
                            cap = 0
                            g(cap)
                        }
                    }''')],

        // A constructor hasn't established the invariant: nothing is assumed of the fields there.
        [group: "P376 call-site invariant", name: "a constructor doesn't assume it",
         expect: "Cannot prove precondition of g at this call site",
         src: tc('''@Invariant({ cap > 0 })
                    class A {
                        int cap
                        @Requires({ x > 0 })
                        static int g(int x) { 100.intdiv(x) }
                        A() {
                            int q = g(cap)
                            cap = 1
                        }
                    }''')],
    ]
}
