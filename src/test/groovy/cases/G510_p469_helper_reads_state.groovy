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
 * 'P469 a helper's value in the state it reads' — a contract-free helper that writes nothing is a function to the
 * encoder: its call an uninterpreted symbol over its arguments, two calls with equal arguments one term. A helper that
 * READS state — a field, an array's, a list's, a map's or a set's contents — was such a function too, so a call before
 * a write and one after it were the same value: `x = get(); c = c + 1; if (x != get()) g(1)` never reached `g(1)`, and
 * a `g` refusing 1 passed. Its symbol now takes the current value of what it reads as further arguments (transitively
 * over the helpers it calls); where no snapshot names that state (another object's field, `new Random()`), each call is
 * its own value.
 */
class G510_p469_helper_reads_state {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 469 (soundness): a contract-free helper reading a field or a container's contents is a function of that state too — two calls agree only when nothing it reads was written between them (a getter read before and after `c = c + 1` was one value) — and one reading state nothing names is a new value at each call."

    static final List<Map> CASES = [

        // ---------- a write between two calls: passed before ----------
        [group: "P469 a helper's value in the state it reads", name: "a getter across a field write", expect: ['Cannot prove precondition of g'],
         src: tc('''final class A {
                        int c
                        int get() { c }
                        void f() {
                            int x = get()
                            c = c + 1
                            int y = get()
                            if (x != y) g(1)
                        }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P469 a helper's value in the state it reads", name: "… the second call in the condition", expect: ['Cannot prove precondition of g'],
         src: tc('''final class A {
                        int c
                        int get() { c }
                        void f() {
                            int x = get()
                            c = c + 1
                            if (x != get()) g(1)
                        }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P469 a helper's value in the state it reads", name: "a static getter across a static write", expect: ['Cannot prove precondition of g'],
         src: tc('''class A {
                        static int c
                        static int get() { c }
                        static void f() {
                            int x = get()
                            c = c + 1
                            if (x != get()) g(1)
                        }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P469 a helper's value in the state it reads", name: "a helper calling the getter", expect: ['Cannot prove precondition of g'],
         src: tc('''final class A {
                        int c
                        int get() { c }
                        int next() { get() + 1 }
                        void f() {
                            int x = next()
                            c = c + 1
                            if (x != next()) g(1)
                        }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P469 a helper's value in the state it reads", name: "an array's element across a store", expect: ['Cannot prove precondition of g'],
         src: tc('''class A {
                        static int first(int[] a) { a != null && a.length > 0 ? a[0] : 0 }
                        @Requires({ a != null && a.length > 0 })
                        static void f(int[] a) {
                            int x = first(a)
                            a[0] = a[0] + 1
                            if (x != first(a)) g(1)
                        }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P469 a helper's value in the state it reads", name: "a set's member across an add", expect: ['Cannot prove precondition of g'],
         src: tc('''final class A {
                        Set<Integer> s
                        boolean has(int k) { k in s }
                        @Requires({ s != null })
                        void f() {
                            boolean x = has(5)
                            s.add(5)
                            if (x != has(5)) g(1)
                        }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P469 a helper's value in the state it reads", name: "a state nothing names: a new value each call", expect: ['Cannot prove precondition of g'],
         src: tc('''class A {
                        static void f(int n) {
                            if (h(n) > 0 && h(n) <= 0) g(1)
                        }
                        static int h(int i) { new Random().nextInt() }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        // ---------- the same state: the calls still agree ----------
        [group: "P469 a helper's value in the state it reads", name: "two calls in one state", ok: true,
         src: tc('''final class A {
                        int c
                        int get() { c }
                        void f() {
                            if (get() != get()) g(1)
                        }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P469 a helper's value in the state it reads", name: "a write to a field it doesn't read", ok: true,
         src: tc('''final class A {
                        int c
                        int d
                        int get() { c }
                        void f() {
                            int x = get()
                            d = d + 1
                            if (x != get()) g(1)
                        }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P469 a helper's value in the state it reads", name: "a set read twice in one state", ok: true,
         src: tc('''final class A {
                        Set<Integer> s
                        boolean has(int k) { k in s }
                        @Requires({ s != null })
                        void f() {
                            boolean x = has(5)
                            if (x != has(5)) g(1)
                        }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P469 a helper's value in the state it reads", name: "a recursive count over a set, read twice in one state", ok: true,
         src: tc('''final class A {
                        Set<Integer> s
                        int d
                        int cnt(int k) { k <= 0 ? 0 : cnt(k - 1) + ((k - 1) in s ? 1 : 0) }
                        @Requires({ s != null })
                        void f(int n) {
                            int x = cnt(n)
                            d = d + 1
                            if (x != cnt(n)) g(1)
                        }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],

        [group: "P469 a helper's value in the state it reads", name: "an array read twice, another array written between", ok: true,
         src: tc('''class A {
                        static int first(int[] a) { a != null && a.length > 0 ? a[0] : 0 }
                        @Requires({ a != null && b != null && b.length > 0 })
                        static void f(int[] a, int[] b) {
                            int x = first(a)
                            b[0] = 7
                            if (x != first(a)) g(1)
                        }
                        @Requires({ i != 1 })
                        static void g(int i) { }
                    }''')],
    ]
}
