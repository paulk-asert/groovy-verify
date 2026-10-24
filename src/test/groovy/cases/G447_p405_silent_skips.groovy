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
 * 'P405 silent skips' — a sweep of the statement walkers for writes they passed over without a word, after Phase 404
 * found two in the value-flow pass. Each shape below writes, then states what the write made false; each compiled
 * cleanly before. The value-flow pass ignored a call no handler framed (a library mutator, a generated setter), a
 * static helper's or a constructor's call (no MethodCallExpression), and `xs << v`; the frame inference read a
 * constructor as writing nothing of its arguments, and a setter's `this.v = v` as a write of its parameter `v` (and
 * dropped it); and in a method with an annotated loop no assert before or after the loop was checked at all.
 */
class G447_p405_silent_skips {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 405: the statement walkers drop no write — a call no handler frames havocs what it may write (a print or pure read writes nothing), a static helper, constructor or `<<` statement is a step, a constructor's frame is its writes through its parameters, a field a parameter shadows is its own frame name (`this.v`), and asserts before and after an annotated loop are checked (soundness fixes)."

    static final String FIELDS = '''
    int count
    int[] arr
    List<Integer> xs
'''

    static final List<Map> CASES = [

        // Unsound before (all compiled cleanly): an unframed call was a no-op in the value-flow pass
        [group: "P405 silent skips", name: "a library mutator's write is seen by a later assert",
         expect: ["Assertion may not hold: (xs.size() == 1)", "no failing call"],
         refute: "fails on",
         src: tc("""final class A {${FIELDS}
                        @Requires({ xs != null && xs.size() == 1 })
                        void f() {
                            xs.remove(0)
                            assert xs.size() == 1
                        }
                    }""")],

        [group: "P405 silent skips", name: "… a static library call writing its argument",
         expect: ["Assertion may not hold: (arr[0] == 1)", "no failing call"],
         src: tc("""final class A {${FIELDS}
                        @Requires({ arr != null && arr.length > 0 && arr[0] == 1 })
                        void f() {
                            Arrays.fill(arr, 5)
                            assert arr[0] == 1
                        }
                    }""")],

        [group: "P405 silent skips", name: "… a generated setter",
         expect: ["Assertion may not hold: (count == 1)", "no failing call"],
         src: tc("""final class A {${FIELDS}
                        @Requires({ count == 1 })
                        void f() {
                            setCount(5)
                            assert count == 1
                        }
                    }""")],

        [group: "P405 silent skips", name: "… and `xs << v`",
         expect: "Assertion may not hold: (xs.size() == 1)",
         src: tc("""final class A {${FIELDS}
                        @Requires({ xs != null && xs.size() == 1 })
                        void f() {
                            xs << 5
                            assert xs.size() == 1
                        }
                    }""")],

        // Unsound before: a static helper called from a static method is a StaticMethodCallExpression, and was dropped
        [group: "P405 silent skips", name: "a static helper's write through its argument",
         expect: ["Assertion may not hold: (a[0] == 1)", "fails on: f([1] as int[])"],
         src: tc('''class A {
                        static void w(int[] b) { if (b != null && b.length > 0) b[0] = 5 }
                        @Requires({ a != null && a.length > 0 && a[0] == 1 })
                        static void f(int[] a) {
                            w(a)
                            assert a[0] == 1
                        }
                    }''')],

        // Unsound before, twice: the statement was dropped, and the frame inference read a constructor as writing only
        // what its arguments' own expressions do
        [group: "P405 silent skips", name: "a constructor's write through its argument",
         expect: "Assertion may not hold: (a[0] == 1)",
         src: tc('''class A {
                        @Requires({ a != null && a.length > 0 && a[0] == 1 })
                        static void f(int[] a) {
                            new B(a)
                            assert a[0] == 1
                        }
                    }
                    class B {
                        B(int[] x) { if (x != null && x.length > 0) x[0] = 5 }
                    }''')],

        [group: "P405 silent skips", name: "… and through a helper that builds one",
         expect: ["Cannot prove postcondition of f", "no failing call: the failure rests on what a call leaves in"],
         src: tc('''class A {
                        static void h(int[] b) { new B(b) }
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ result == old.a[0] })
                        static int f(int[] a) {
                            h(a)
                            return a[0]
                        }
                    }
                    class B {
                        B(int[] x) { if (x != null && x.length > 0) x[0] = 5 }
                    }''')],

        // Precision kept: a constructor's own fields are the new object's (the monad factories' `new Maybe(v)`)
        [group: "P405 silent skips", name: "a constructor setting its own fields writes nothing of the caller's",
         ok: true,
         src: tc('''class A {
                        static Box of(int v) { new Box(v) }
                        @Requires({ a != null && a.length > 0 && a[0] == 1 })
                        static void f(int[] a, int x) {
                            of(x)
                            assert a[0] == 1
                        }
                    }
                    final class Box {
                        int v
                        Box(int v) { this.v = v }
                    }''')],

        // Unsound before: `this.v = v` was recorded as `v`, read as the int parameter, and dropped from the frame
        [group: "P405 silent skips", name: "a setter whose parameter shadows the field writes the field",
         expect: ["Cannot prove postcondition of f", "fails on: f(new C(v: 1))"],
         src: tc('''class A {
                        @Requires({ c != null && c.v == 1 })
                        @Ensures({ result == 1 })
                        static int f(C c) {
                            c.setIt(5)
                            return c.v
                        }
                    }
                    final class C {
                        int v
                        void setIt(int v) { this.v = v }
                    }''')],

        // Unsound before: in a method with an annotated loop, no assert outside the loop body was checked
        [group: "P405 silent skips", name: "an assert before an annotated loop is checked",
         expect: "Assertion may not hold: (n == 12345)",
         src: tc('''class A {
                        static void f(int n) {
                            assert n == 12345
                            int i = 0
                            @Invariant({ 0 <= i })
                            while (i < n) { i = i + 1 }
                        }
                    }''')],

        [group: "P405 silent skips", name: "… and one after it",
         expect: ["Assertion may not hold: (n == 12345)", "fails on: f(-1)"],
         src: tc('''class A {
                        static void f(int n) {
                            int i = 0
                            @Invariant({ 0 <= i })
                            while (i < n) { i = i + 1 }
                            assert n == 12345
                        }
                    }''')],

        [group: "P405 silent skips", name: "… a true one after it proves from the invariant and the exit",
         ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static void f(int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            while (i < n) { i = i + 1 }
                            assert i == n
                        }
                    }''')],

        // Precision kept: a print and a pure read write nothing
        [group: "P405 silent skips", name: "a print or a pure read keeps what the assert needs",
         ok: true,
         src: tc("""final class A {${FIELDS}
                        @Requires({ arr != null && arr.length > 0 && arr[0] == 1 && xs != null && xs.size() == 1 })
                        void f() {
                            println(arr)
                            Math.abs(count)
                            xs.size()
                            assert arr[0] == 1 && xs.size() == 1
                        }
                    }""")],
    ]
}
