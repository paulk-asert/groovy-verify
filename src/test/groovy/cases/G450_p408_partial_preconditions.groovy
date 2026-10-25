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
 * 'P408 partial preconditions' — a @Requires was assumed whole or not at all: one conjunct outside the model (an open
 * getter's read, a receiver's array field's length) lost every other, so `c != null && c.count == 5` assumed neither and
 * `c.bump()` "failed on" `f(null)`. Each top-level conjunct that translates is assumed now; one that doesn't is a
 * witness taint, so a refutation still stands but shows no call the model built (it may not meet the dropped part),
 * naming the conjuncts it dropped.
 *
 * Found on the way: an index into an array that isn't a variable — a receiver's field (`h.arr[0]`), an inner array
 * (`g[0][0]`), `this.arr[0]` — made no obligation and said nothing. `this.arr[i]` is the field's index now; the others
 * skip loudly, naming the array.
 */
class G450_p408_partial_preconditions {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 408: a @Requires is assumed conjunct by conjunct, so one part outside the model no longer loses the rest (a refutation that rests on a dropped part shows no call, naming it); `this.arr[i]` has its bounds obligation, and an index into an array that is no variable (`h.arr[0]`, `g[0][0]`) skips loudly (soundness fixes)."

    static final String HOLDER = '''
final class Holder {
    int[] arr
}
'''

    static final List<Map> CASES = [

        // A false positive before: `c.count` is an open getter's read, so the whole precondition was dropped and
        // `c.bump()` dereferenced a possibly-null `c`
        [group: "P408 partial preconditions", name: "a conjunct outside the model keeps the others",
         ok: true,
         src: tc('''class A {
                        @Requires({ c != null && c.count == 5 })
                        static int f(Open c) {
                            c.bump()
                            return 1
                        }
                    }
                    class Open {
                        int count
                        void bump() { count = count + 1 }
                    }''')],

        // … and a receiver array's length doesn't lose `a.length > 0` (the store into `h.arr` itself skips, below)
        [group: "P408 partial preconditions", name: "… a receiver array's length keeps a parameter array's",
         expect: "Skipped array index safety check ('h.arr[0]' indexes the array 'h.arr'",
         refute: "Possible IndexOutOfBoundsException",
         src: tc('''class A {
                        @Requires({ h != null && h.arr != null && h.arr.length > 0 && a != null && a.length > 0 })
                        static int f(Holder h, int[] a) {
                            h.arr[0] = 99
                            return a[0]
                        }
                    }''' + HOLDER)],

        // A real failure (`a` may be empty) still refutes, but the model's call needn't meet the dropped conjuncts
        [group: "P408 partial preconditions", name: "a real failure under a partial precondition refutes, with no call",
         expect: ["Possible IndexOutOfBoundsException",
                  "no failing call: the precondition's 'h.arr != null', 'h.arr.length > 0' are outside what the verifier models"],
         refute: "fails on",
         src: tc('''class A {
                        @Requires({ h != null && h.arr != null && h.arr.length > 0 && a != null })
                        static int f(Holder h, int[] a) {
                            h.arr[0] = 99
                            return a[0]
                        }
                    }''' + HOLDER)],

        // ── indexes that made no obligation ──

        // Unchecked before, silently: `h.arr` may be empty
        [group: "P408 partial preconditions", name: "a store into a receiver's array field skips, naming it",
         expect: "Skipped array index safety check ('h.arr[0]' indexes the array 'h.arr', which isn't a variable or field the verifier models)",
         src: tc('''class A {
                        @Requires({ h != null && h.arr != null })
                        static int f(Holder h) {
                            h.arr[0] = 99
                            return 1
                        }
                    }''' + HOLDER)],

        [group: "P408 partial preconditions", name: "… and a read of one",
         expect: "Skipped array index safety check ('h.arr[0]' indexes the array 'h.arr'",
         src: tc('''class A {
                        @Requires({ h != null && h.arr != null })
                        static int f(Holder h) {
                            return h.arr[0]
                        }
                    }''' + HOLDER)],

        [group: "P408 partial preconditions", name: "… and an inner array's index",
         expect: "Skipped array index safety check ('g[0][0]' indexes the array 'g[0]'",
         src: tc('''class A {
                        @Requires({ g != null && g.length > 0 })
                        static int f(int[][] g) {
                            return g[0][0]
                        }
                    }''')],

        // Unchecked before, silently, though `arr[0]` refuted: `this.arr` is the field
        [group: "P408 partial preconditions", name: "`this.arr[0]` is checked as `arr[0]` is",
         expect: ["Possible IndexOutOfBoundsException", "fails on: f()"],
         src: tc('''final class A {
                        int[] arr
                        @Requires({ arr != null })
                        int f() {
                            return this.arr[0]
                        }
                    }''')],

        [group: "P408 partial preconditions", name: "… and proves when guarded",
         ok: true,
         src: tc('''final class A {
                        int[] arr
                        @Requires({ arr != null && arr.length > 0 })
                        int f() {
                            return this.arr[0]
                        }
                    }''')],
    ]
}
