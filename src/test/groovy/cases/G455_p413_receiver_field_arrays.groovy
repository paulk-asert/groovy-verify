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
 * 'P413 receiver-field arrays' — Phase 408 made `h.arr[0]` (an array a parameter's field holds) a loud skip, and its
 * `h.arr.length > 0` a precondition part left out. In a method that writes no array and nothing through an object
 * parameter, the field is now the named array `h$arr` — its length, nullity and elements — from entry to exit: its index
 * is checked, its precondition assumed, and a failing call rebuilds the holder (`new Holder(arr: [4, 4, 5] as int[])`),
 * pinned to the full precondition as a parameter array is. Only for an integral primitive array; a holder class shared
 * with another parameter (whose fields may alias), a field a getter may stand in for, and any method that may write an
 * array stay as they were: the index skips loudly.
 */
class G455_p413_receiver_field_arrays {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 413: an integral array a parameter's field holds (`h.arr`) is read as a named array in a method that writes no array — its index checked, its length and nullity assumed from @Requires, a failing call rebuilding the holder — while any method that may write an array keeps the loud skip."

    static final String HOLDER = '''
final class Holder {
    int[] arr
    void poke() { arr[0] = 0 }
}
'''

    static final List<Map> CASES = [

        // Skipped before (Phase 408): `h.arr[0]` had no obligation
        [group: "P413 receiver-field arrays", name: "a guarded read proves",
         ok: true,
         src: tc('''class A {
                        @Requires({ h != null && h.arr != null && h.arr.length > 0 })
                        static int f(Holder h) { h.arr[0] + h.arr[-1] }
                    }''' + HOLDER)],

        [group: "P413 receiver-field arrays", name: "an unguarded one refutes, rebuilding the holder",
         expect: ["Possible IndexOutOfBoundsException", "obligation: 0 <= 0 && 0 < h.arr.length",
                  "counterexample: h.arr.length = 0", "fails on: f(new Holder(arr: new int[0]))"],
         src: tc('''class A {
                        @Requires({ h != null && h.arr != null })
                        static int f(Holder h) { h.arr[0] }
                    }''' + HOLDER)],

        [group: "P413 receiver-field arrays", name: "a loop over it",
         ok: true,
         src: tc('''class A {
                        @Requires({ h != null && h.arr != null })
                        static int f(Holder h) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= h.arr.length })
                            @Decreases({ h.arr.length - i })
                            while (i < h.arr.length) { s = s + h.arr[i]; i = i + 1 }
                            return s
                        }
                    }''' + HOLDER)],

        [group: "P413 receiver-field arrays", name: "a postcondition over its elements",
         ok: true,
         src: tc('''class A {
                        @Requires({ h != null && h.arr != null && h.arr.length > 2 })
                        @Ensures({ result == h.arr[1] })
                        static int f(Holder h) { h.arr[1] }
                    }''' + HOLDER)],

        [group: "P413 receiver-field arrays", name: "… a wrong one refutes with its elements",
         expect: ["Cannot prove postcondition of f", "h.arr[2] = ", "fails on: f(new Holder(arr: ["],
         src: tc('''class A {
                        @Requires({ h != null && h.arr != null && h.arr.length > 2 })
                        @Ensures({ result == h.arr[2] })
                        static int f(Holder h) { h.arr[1] }
                    }''' + HOLDER)],

        // The call meets the quantified precondition the bounds check left out (Phase 337's re-check, now pinned)
        [group: "P413 receiver-field arrays", name: "a failing call meets the whole precondition",
         expect: ["Possible ArithmeticException: Division by zero", "fails on: f(new Holder(arr: [1] as int[]))"],
         src: tc('''class A {
                        @Requires({ h != null && h.arr != null && h.arr.length > 0 && (0..<h.arr.length).every { h.arr[it] > 0 } })
                        static int f(Holder h) { 10 % (h.arr[0] - 1) }
                    }''' + HOLDER)],

        // Phase 408's precondition part is no longer left out: the bug in `a` keeps its call
        [group: "P413 receiver-field arrays", name: "its precondition part is assumed, and the call shown",
         expect: ["Possible IndexOutOfBoundsException", "fails on: f(new Holder(arr: new int[1]), new int[0])"],
         refute: "no failing call",
         src: tc('''class A {
                        @Requires({ h != null && h.arr != null && h.arr.length > 0 && a != null })
                        static int f(Holder h, int[] a) { h.arr[0] + a[0] }
                    }''' + HOLDER)],

        // ── as they were: a method that may write an array, or a holder that may alias ──

        [group: "P413 receiver-field arrays", name: "a store into it keeps the loud skip",
         expect: "Skipped array index safety check ('h.arr[0]' indexes the array 'h.arr'",
         src: tc('''class A {
                        @Requires({ h != null && h.arr != null && h.arr.length > 0 })
                        static int f(Holder h) { h.arr[0] = 1; return h.arr[0] }
                    }''' + HOLDER)],

        [group: "P413 receiver-field arrays", name: "… and so does a call that may write an array",
         expect: "Skipped array index safety check ('h.arr[0]' indexes the array 'h.arr'",
         src: tc('''class A {
                        @Requires({ h != null && h.arr != null && h.arr.length > 0 })
                        static int f(Holder h) { h.poke(); return h.arr[0] }
                    }''' + HOLDER)],

        [group: "P413 receiver-field arrays", name: "… a write into a parameter array it may be",
         expect: "call 'w(…)' writes into the array 'a', which may be the array 'h.arr' this method reads",
         src: tc('''class A {
                        static void w(int[] b) { if (b != null && b.length > 0) b[0] = 5 }
                        @Requires({ h != null && h.arr != null && h.arr.length > 0 && h.arr[0] == 1 && a != null })
                        @Ensures({ result == 1 })
                        static int f(Holder h, int[] a) { w(a); return h.arr[0] }
                    }''' + HOLDER)],

        [group: "P413 receiver-field arrays", name: "… two holders of one class",
         expect: "Skipped array index safety check ('h.arr[0]' indexes the array 'h.arr'",
         src: tc('''class A {
                        @Requires({ h != null && g != null && h.arr != null && h.arr.length > 0 })
                        static int f(Holder h, Holder g) { h.arr[0] }
                    }''' + HOLDER)],

        [group: "P413 receiver-field arrays", name: "… and a holder a subclass may override",
         expect: "Skipped array index safety check ('h.arr[0]' indexes the array 'h.arr'",
         src: tc('''class A {
                        @Requires({ h != null && h.arr != null && h.arr.length > 0 })
                        static int f(OpenH h) { h.arr[0] }
                    }
                    class OpenH { int[] arr }''')],
    ]
}
