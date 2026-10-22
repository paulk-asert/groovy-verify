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
 * 'P375 array re-assignment' — an array (or list) local re-assigned kept the OLD array's facts: only its scalar handle
 * was rebound, so its contents, length and nullity still read the array it held before. `v = grow(v)` in a loop
 * preserved a false `v.length == m`, and straight-line `v = grow(v); v.length` proved a false postcondition (reported
 * from the ClearSplit port, where a fold's conservation proof still verified with its key precondition deleted).
 * A re-assigned name now gets fresh oracles, constrained by a contracted call's {@code @Ensures} (with an argument
 * naming it read as it was before the call), by an allocation or literal, or shared with an aliased array; an array
 * formal reads its named actual, as a list formal does.
 */
class G419_p375_array_reassign {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 375: an array or list re-assigned (from a contracted call, another array, an allocation or a literal) takes the new value\'s contents, length and nullity, not the old one\'s; a callee\'s @Ensures binds `result` to it and reads an argument naming it as before the call; an array formal reads its named actual.'

    static final String GROW = '''
                        @Requires({ a != null })
                        @Ensures({ result != null && result.length == a.length + 1 })
                        static int[] grow(int[] a) { new int[a.length + 1] }'''

    static final String LGROW = '''
                        @Requires({ a != null })
                        @Ensures({ result != null && result.size() == a.size() + 1 })
                        static List<Integer> grow(List<Integer> a) { List<Integer> r = []; r.addAll(a); r.add(0); r }'''

    static final List<Map> CASES = [

        // Before: compiled cleanly — v kept the old length across `v = grow(v)`.
        [group: "P375 array re-assignment", name: "a false invariant across an array-returning call",
         expect: ["Cannot prove loop invariant is preserved by the loop body in m4", "fails on: m4(1, 1)"],
         src: tc("""class A {${GROW}
                        @Requires({ n >= 1 && m > 0 })
                        static int m4(int n, int m) {
                            int[] v = new int[m]
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && v != null && v.length == m })
                            @Decreases({ n - i })
                            while (i < n) {
                                v = grow(v)
                                i = i + 1
                            }
                            v.length
                        }
                    }""")],

        // Before: refuted, falsely (the callee's `result.length` wasn't v's).
        [group: "P375 array re-assignment", name: "the true invariant proves",
         ok: true,
         src: tc("""class A {${GROW}
                        @Requires({ n >= 1 && m > 0 })
                        @Ensures({ result == m + n })
                        static int m4(int n, int m) {
                            int[] v = new int[m]
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && v != null && v.length == m + i })
                            @Decreases({ n - i })
                            while (i < n) {
                                v = grow(v)
                                i = i + 1
                            }
                            v.length
                        }
                    }""")],

        // Before: the postcondition proved (no loop needed), beside a false warning on grow's `a != null`.
        [group: "P375 array re-assignment", name: "straight-line: a false postcondition after v = grow(v)",
         expect: ["Cannot prove postcondition of f", "fails on: f(1)"],
         src: tc("""class A {${GROW}
                        @Requires({ m > 0 })
                        @Ensures({ result == m })
                        static int f(int m) {
                            int[] v = new int[m]
                            v = grow(v)
                            v.length
                        }
                    }""")],

        // Before: refuted, falsely, beside a false warning on grow's `a != null`.
        [group: "P375 array re-assignment", name: "straight-line: the true postcondition proves",
         ok: true,
         src: tc("""class A {${GROW}
                        @Requires({ m > 0 })
                        @Ensures({ result == m + 1 })
                        static int f(int m) {
                            int[] v = new int[m]
                            int[] w = grow(v)
                            w.length
                        }
                    }""")],

        // Before: compiled cleanly — the contents, not just the length.
        [group: "P375 array re-assignment", name: "an element fact across the call",
         expect: "Cannot prove loop invariant is preserved by the loop body in f",
         src: tc('''class A {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ result != null && result.length == a.length && result[0] == a[0] + 1 })
                        static int[] inc0(int[] a) { int[] r = new int[a.length]; r[0] = a[0] + 1; r }
                        @Requires({ n >= 1 && m > 0 })
                        static int f(int n, int m) {
                            int[] v = new int[m]
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && v != null && v.length == m && v[0] == 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                v = inc0(v)
                                i = i + 1
                            }
                            v[0]
                        }
                    }''')],

        // Before: compiled cleanly — `v = w` kept v's own length.
        [group: "P375 array re-assignment", name: "an array alias in a loop",
         expect: "Cannot prove loop invariant is preserved by the loop body in f",
         src: tc('''class A {
                        @Requires({ n >= 1 && m > 0 })
                        static int f(int n, int m) {
                            int[] v = new int[m]
                            int[] w = new int[m + 1]
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && v != null && v.length == m })
                            @Decreases({ n - i })
                            while (i < n) {
                                v = w
                                i = i + 1
                            }
                            v.length
                        }
                    }''')],

        // An alias whose source is then written: a store rebinds only w's contents, so the loop is skipped loudly
        // (Phase 366's guard) rather than read v's as the old ones.
        [group: "P375 array re-assignment", name: "an alias whose source is written after",
         expect: "makes 'v' share its contents with 'w', and 'w' is written", refute: "Cannot prove",
         src: tc('''class A {
                        @Requires({ n >= 1 && m > 0 })
                        static int f(int n, int m) {
                            int[] v = new int[m]
                            int[] w = new int[m]
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && v != null && v.length == m && v[0] == 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                v = w
                                w[0] = 1
                                i = i + 1
                            }
                            v[0]
                        }
                    }''')],

        // The allocation reads the old length before v is the new array.
        [group: "P375 array re-assignment", name: "an allocation sized by the array it replaces",
         ok: true,
         src: tc('''class A {
                        @Requires({ n >= 1 && m > 0 })
                        @Ensures({ result == m + n })
                        static int f(int n, int m) {
                            int[] v = new int[m]
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && v != null && v.length == m + i })
                            @Decreases({ n - i })
                            while (i < n) {
                                v = new int[v.length + 1]
                                i = i + 1
                            }
                            v.length
                        }
                    }''')],

        // Before: refuted, falsely — the replayed `new int[m]` was havocked, and the formal's length wasn't v's.
        [group: "P375 array re-assignment", name: "a callee precondition over a local array's length",
         ok: true,
         src: tc('''class A {
                        @Requires({ a != null && a.length > 0 })
                        static int g(int[] a) { a[0] }
                        @Requires({ m > 0 })
                        static int f(int m) {
                            int[] v = new int[m]
                            g(v)
                        }
                    }''')],

        // Before: f passed silently (only grow's own body was reported).
        [group: "P375 array re-assignment", name: "a list parameter re-assigned from a call in a loop",
         expect: "Cannot prove loop invariant is preserved by the loop body in f",
         src: tc("""class A {${LGROW}
                        @Requires({ n >= 1 && xs != null })
                        static int f(int n, List<Integer> xs) {
                            int k = xs.size()
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && xs != null && xs.size() == k })
                            @Decreases({ n - i })
                            while (i < n) {
                                xs = grow(xs)
                                i = i + 1
                            }
                            xs.size()
                        }
                    }""")],

        // Before: refuted, falsely. (grow's own body is outside the fragment, which it says.)
        [group: "P375 array re-assignment", name: "… and its true invariant proves",
         expect: "Skipped verification of postcondition for grow", refute: ["Cannot prove", "Could not decide"],
         src: tc("""class A {${LGROW}
                        @Requires({ n >= 1 && xs != null })
                        static int f(int n, List<Integer> xs) {
                            int k = xs.size()
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && xs != null && xs.size() == k + i })
                            @Decreases({ n - i })
                            while (i < n) {
                                xs = grow(xs)
                                i = i + 1
                            }
                            xs.size()
                        }
                    }""")],

        // Before: compiled cleanly.
        [group: "P375 array re-assignment", name: "a list alias in a loop",
         expect: "Cannot prove loop invariant is preserved by the loop body in f",
         src: tc('''class A {
                        @Requires({ n >= 1 && xs != null && ys != null && xs.size() != ys.size() })
                        static int f(int n, List<Integer> xs, List<Integer> ys) {
                            int k = xs.size()
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && xs != null && xs.size() == k })
                            @Decreases({ n - i })
                            while (i < n) {
                                xs = ys
                                i = i + 1
                            }
                            xs.size()
                        }
                    }''')],

        // Before: refuted, with the old list's size. The callee's argument is v before the call.
        [group: "P375 array re-assignment", name: "a list literal re-assigned from a call on itself",
         expect: "Cannot prove postcondition of f",
         src: tc("""class A {${LGROW}
                        @Ensures({ result == 42 })
                        static int f() {
                            List<Integer> v = [1, 2]
                            v = grow(v)
                            v.size()
                        }
                    }""")],

        // Before: refuted, falsely.
        [group: "P375 array re-assignment", name: "… and its true size proves",
         expect: "Skipped verification of postcondition for grow", refute: ["Cannot prove", "Could not decide"],
         src: tc("""class A {${LGROW}
                        @Ensures({ result == 3 })
                        static int f() {
                            List<Integer> v = [1, 2]
                            v = grow(v)
                            v.size()
                        }
                    }""")],
    ]
}
