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
 * 'P462 a call's branch read where it's taken' — a call's @Requires was checked with its enclosing `if` conditions,
 * and the early-return guards before it, asserted over the method's entry values, the statements before the call
 * replayed after them. A condition over a value written first was read before the write: `n = n + 1; if (n != 1)
 * return g(n)` took `n != 1` of the entry `n` (so `g` needing `n != 2` passed, though `f(1)` calls `g(2)`). Each
 * condition is assumed now where the path passes it, in the replayed prefix.
 */
class G503_p462_call_site_branch_state {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 462 (soundness): a call's enclosing `if` conditions and the early-return guards before it are assumed where the path passes them, after the writes before them, where they were assumed over the method's entry values (`n = n + 1; if (n != 1) return g(n)` took `n != 1` before the increment, so a `g` needing `n != 2` passed)."

    static final List<Map> CASES = [

        // ---------- a condition over a value written first: passed before ----------
        [group: "P462 a call's branch read where it's taken", name: "an enclosing if after a write", expect: ['Cannot prove precondition of g', 'f(1)'],
         src: tc('''class A {
                        static int f(int n) {
                            n = n + 1
                            if (n != 1) return g(n)
                            return 0
                        }
                        @Requires({ n != 2 })
                        static int g(int n) { n }
                    }''')],

        [group: "P462 a call's branch read where it's taken", name: "… its else branch", expect: ['Cannot prove precondition of g', 'f(1)'],
         src: tc('''class A {
                        static int f(int n) {
                            n = n + 1
                            if (n == 1) return 0
                            else return g(n)
                        }
                        @Requires({ n != 2 })
                        static int g(int n) { n }
                    }''')],

        [group: "P462 a call's branch read where it's taken", name: "an early return after a write", expect: ['Cannot prove precondition of g', 'f(1)'],
         src: tc('''class A {
                        static int f(int n) {
                            n = n + 1
                            if (n == 1) return 0
                            return g(n)
                        }
                        @Requires({ n != 2 })
                        static int g(int n) { n }
                    }''')],

        [group: "P462 a call's branch read where it's taken", name: "a write between nested ifs", expect: ['Cannot prove precondition of g', 'f(4)'],
         src: tc('''class A {
                        static int f(int n) {
                            if (n > 0) {
                                n = n - 5
                                if (n != 4) return g(n)
                            }
                            return 0
                        }
                        @Requires({ n != -1 })
                        static int g(int n) { n }
                    }''')],

        [group: "P462 a call's branch read where it's taken", name: "a field written before the if", expect: ['Cannot prove precondition of g'],
         src: tc('''class A {
                        int x
                        void f() {
                            x = x + 1
                            if (x != 1) g(x)
                        }
                        @Requires({ v != 2 })
                        static void g(int v) { }
                    }''')],

        [group: "P462 a call's branch read where it's taken", name: "an if in an annotated loop after a write", expect: ['Cannot prove precondition of g'],
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            int i = 0
                            int s = 0
                            @Invariant({ 0 <= i && i <= n })
                            while (i < n) {
                                i++
                                if (i != 1) s += g(i)
                            }
                            return s
                        }
                        @Requires({ i != 2 })
                        static int g(int i) { i }
                    }''')],

        [group: "P462 a call's branch read where it's taken", name: "an if around an annotated loop that writes it", expect: ['Cannot prove precondition of g'],
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static int f(int n, int i) {
                            int s = 0
                            if (i == 0) {
                                @Invariant({ 0 <= i && i <= n })
                                while (i < n) { s += g(i); i++ }
                            }
                            return s
                        }
                        @Requires({ i == 0 })
                        static int g(int i) { i }
                    }''')],

        [group: "P462 a call's branch read where it's taken", name: "a write before an annotated loop", expect: ['Cannot prove precondition of g', 'f(1)'],
         src: tc('''class A {
                        @Requires({ n >= 1 })
                        static int f(int n) {
                            n = n - 1
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= 3 })
                            while (i < 3) { s += g(n); i++ }
                            return s
                        }
                        @Requires({ n >= 1 })
                        static int g(int n) { n }
                    }''')],

        // ---------- each condition read where it's taken proves ----------
        [group: "P462 a call's branch read where it's taken", name: "the enclosing if, read after the write", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            n = n + 1
                            if (n != 2) return g(n)
                            return 0
                        }
                        @Requires({ n != 2 })
                        static int g(int n) { n }
                    }''')],

        [group: "P462 a call's branch read where it's taken", name: "the early return, read after the write", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            n = n + 1
                            if (n == 2) return 0
                            return g(n)
                        }
                        @Requires({ n != 2 })
                        static int g(int n) { n }
                    }''')],

        [group: "P462 a call's branch read where it's taken", name: "a value written after the if keeps its fact", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            if (n > 0) {
                                int m = n
                                n = 0
                                return g(m)
                            }
                            return 0
                        }
                        @Requires({ m > 0 })
                        static int g(int m) { m }
                    }''')],

        [group: "P462 a call's branch read where it's taken", name: "the if in the annotated loop, read after the write", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            int i = 0
                            int s = 0
                            @Invariant({ 0 <= i && i <= n })
                            while (i < n) {
                                i++
                                if (i != 2) s += g(i)
                            }
                            return s
                        }
                        @Requires({ i != 2 })
                        static int g(int i) { i }
                    }''')],

        [group: "P462 a call's branch read where it's taken", name: "the write before the annotated loop, replayed", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            n = n + 1
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= 3 })
                            while (i < 3) { s += g(n); i++ }
                            return s
                        }
                        @Requires({ n >= 1 })
                        static int g(int n) { n }
                    }''')],

        [group: "P462 a call's branch read where it's taken", name: "a short-circuit guard in the call's statement", ok: true,
         src: tc('''class A {
                        static boolean f(int n) {
                            n = n + 1
                            return n != 2 && g(n)
                        }
                        @Requires({ n != 2 })
                        static boolean g(int n) { true }
                    }''')],
    ]
}
