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
 * 'P404 field-array aliasing' — Phase 194's residual (c). The documented no-aliasing assumption is about parameters
 * ("distinct parameter names denote distinct objects"), but the model read every two array NAMES as two arrays: a
 * field, a static or a receiver's field written while a parameter (or another field) was read. `h.poke()` writing
 * `h.arr[0]` left `a[0]` as it was, so `result == old.a[0]` proved — `f(new Holder(arr: a), a)` returns 99. Where at
 * least one of the two is no parameter, a write into one is now a write into whichever of the others it may be (an
 * element type it could share): a postcondition over the other skips loudly, naming both (as Phase 194 does for two
 * parameters); an implicit obligation or assert reads its contents as unknown, and a failure that needs the two to be
 * one array shows no call. Two parameters keep the documented reading.
 *
 * Found on the way: the value-flow pass dropped element stores (`a[0] = 5; a[a[0]]` on a two-element array proved in
 * bounds) and every compound assignment or increment statement (`int x = 1; x += 5; assert x == 1` proved). Both are
 * steps now.
 */
class G446_p404_field_array_aliasing {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 404: an array field, static or receiver's field may be the array a parameter or another field holds — a write into one makes the other's contents unknown (a postcondition over it skips loudly, an obligation or assert reads it as unknown, with no call shown when the failure needs the two to be one) — and the value-flow pass replays element stores, compound assignments and increments (soundness fixes)."

    static final String HOLDER = '''
final class Holder {
    int[] arr
    void poke() { arr[0] = 0 }
}
'''

    static final List<Map> CASES = [

        // Unsound before: proved — f(new Holder(arr: a), a) returns 0
        [group: "P404 field-array aliasing", name: "a call writing a receiver's array field: a postcondition over a parameter array skips, naming both",
         expect: "call 'poke(…)' writes into the array 'h.arr', which may be the array 'a' this method reads",
         src: tc('''class A {
                        @Requires({ h != null && a != null && a.length > 0 })
                        @Ensures({ result == old.a[0] })
                        static int f(Holder h, int[] a) {
                            h.poke()
                            return a[0]
                        }
                    }''' + HOLDER)],

        // Unsound before: proved — `arr` may hold the array passed as `a`
        [group: "P404 field-array aliasing", name: "a store into the object's own array field",
         expect: "arrays 'arr' and 'a' may be one array",
         src: tc('''final class A {
                        int[] arr
                        @Requires({ arr != null && arr.length > 0 && a != null && a.length > 0 })
                        @Ensures({ result == old.a[0] })
                        int f(int[] a) {
                            arr[0] = 99
                            return a[0]
                        }
                    }''')],

        [group: "P404 field-array aliasing", name: "… and into a static array",
         expect: "arrays 'buf' and 'a' may be one array",
         src: tc('''class A {
                        static int[] buf = new int[4]
                        @Requires({ buf != null && buf.length > 0 && a != null && a.length > 0 })
                        @Ensures({ result == old.a[0] })
                        static int f(int[] a) {
                            buf[0] = 99
                            return a[0]
                        }
                    }''')],

        // The way back: declare them two arrays, as Phase 89 does for objects (`a !== b`) — each call site is held to it
        [group: "P404 field-array aliasing", name: "a declared `a !== arr` keeps them apart",
         ok: true,
         src: tc('''final class A {
                        int[] arr
                        @Requires({ a !== arr && arr != null && arr.length > 0 && a != null && a.length > 0 })
                        @Ensures({ result == old.a[0] })
                        int f(int[] a) {
                            arr[0] = 99
                            return a[0]
                        }
                    }''')],

        // P167's in-place reverse proved this before its `orig !== a`: `c.reverse(c.a, v, n)` meets the rest of its
        // precondition and leaves `a` reversed, so `a[it] == orig[a.length - 1 - it]` fails
        [group: "P404 field-array aliasing", name: "a helper writing the field array a parameter is compared with",
         expect: "call 'swap(…)' writes into the array 'a', which may be the array 'orig' this method reads",
         src: tc('''final class C {
                        int[] a
                        @Requires({ 0 <= i && i < a.length && 0 <= j && j < a.length })
                        @Modifies({ this.a })
                        @Ensures({ a[i] == old.a[j] && a[j] == old.a[i] })
                        void swap(int i, int j) { int t = a[i]; a[i] = a[j]; a[j] = t }

                        @Requires({ orig != null && orig.length == a.length && a.length > 1 && a[0] == orig[0] })
                        @Modifies({ this.a })
                        @Ensures({ a[a.length - 1] == orig[0] })
                        void f(int[] orig) {
                            swap(0, a.length - 1)
                        }
                    }''')],

        // Unsound before: proved. The failing run needs `arr` to be `a`, which no call built from fresh arguments is
        [group: "P404 field-array aliasing", name: "an assert over a parameter array after a field store: refuted, no call shown",
         expect: ["Assertion may not hold: (a[0] == 1)", "no failing call: the failure needs two of the arrays this method names to be one array"],
         refute: "fails on",
         src: tc('''final class A {
                        int[] arr
                        @Requires({ arr != null && arr.length > 0 && a != null && a.length > 0 && a[0] == 1 })
                        void f(int[] a) {
                            arr[0] = 0
                            assert a[0] == 1
                        }
                    }''')],

        // Unsound before: proved safe — under the alias poke() zeroes a[0]
        [group: "P404 field-array aliasing", name: "a division by a parameter's element after a call writing a receiver's array",
         expect: ["Possible ArithmeticException: Division by zero", "no failing call"],
         refute: "fails on",
         src: tc('''class A {
                        @Requires({ h != null && a != null && a.length > 0 && a[0] == 1 })
                        static int f(Holder h, int[] a) {
                            h.poke()
                            10 % a[0]
                        }
                    }''' + HOLDER)],

        // Precision kept: a failure that doesn't rest on the alias keeps its call
        [group: "P404 field-array aliasing", name: "a real failure beside a possible alias keeps its call",
         expect: ["Possible ArithmeticException: Division by zero", "fails on: f([1] as int[])"],
         src: tc('''final class A {
                        int[] arr
                        @Requires({ a != null && a.length > 0 && a[0] == 1 })
                        int f(int[] a) {
                            a[0] = 0
                            10 % a[0]
                        }
                    }''')],

        [group: "P404 field-array aliasing", name: "arrays of element types that can't be shared stay apart",
         ok: true,
         src: tc('''class A {
                        @Requires({ h != null && a != null && a.length > 0 })
                        @Ensures({ result == old.a[0] })
                        static long f(Holder h, long[] a) {
                            h.poke()
                            return a[0]
                        }
                    }''' + HOLDER)],

        [group: "P404 field-array aliasing", name: "a fresh local array is no other array",
         ok: true,
         src: tc('''class A {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ result == old.a[0] })
                        static int f(int[] a) {
                            int[] t = new int[3]
                            t[0] = 99
                            return a[0]
                        }
                    }''')],

        // The documented assumption: two parameter names are two arrays (Phase 194 is loud only for a direct store
        // read beside in a postcondition)
        [group: "P404 field-array aliasing", name: "two parameters keep the documented reading",
         ok: true,
         src: tc('''class A {
                        @Requires({ b != null && b.length > 0 })
                        static void w(int[] b) { b[0] = 99 }
                        @Requires({ a != null && a.length > 0 && c != null && c.length > 0 })
                        @Ensures({ result == old.c[0] })
                        static int f(int[] a, int[] c) {
                            w(a)
                            return c[0]
                        }
                    }''')],

        // ── the value-flow pass's dropped writes ──

        // Unsound before: proved in bounds — a[0] is 5, and a has two elements
        [group: "P404 field-array aliasing", name: "the value-flow pass reads an element store",
         expect: ["Possible IndexOutOfBoundsException", "fails on: f([1, 1] as int[])"],
         src: tc('''class A {
                        @Requires({ a != null && a.length > 1 && a[0] == 1 })
                        static int f(int[] a) {
                            a[0] = 5
                            a[a[0]]
                        }
                    }''')],

        // Unsound before: both proved
        [group: "P404 field-array aliasing", name: "… a compound element assignment",
         expect: ["Assertion may not hold: (a[0] == 1)", "fails on: f([1] as int[])"],
         src: tc('''class A {
                        @Requires({ a != null && a.length > 0 && a[0] == 1 })
                        static void f(int[] a) {
                            a[0] += 5
                            assert a[0] == 1
                        }
                    }''')],

        [group: "P404 field-array aliasing", name: "… an element increment",
         expect: ["Assertion may not hold: (a[0] == 1)", "fails on: f([1] as int[])"],
         src: tc('''class A {
                        @Requires({ a != null && a.length > 0 && a[0] == 1 })
                        static void f(int[] a) {
                            a[0]++
                            assert a[0] == 1
                        }
                    }''')],

        // Unsound before: proved. A local written twice is outside the value-flow fragment — loud, naming it
        [group: "P404 field-array aliasing", name: "… and a compound assignment to a local skips, naming it",
         expect: "Skipped assertion safety check (the method body is outside the value-flow fragment (re-assignment of 'x'))",
         src: tc('''class A {
                        static void f() {
                            int x = 1
                            x += 5
                            assert x == 1
                        }
                    }''')],
    ]
}
