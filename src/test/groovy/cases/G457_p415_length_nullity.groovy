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
 * 'P415 length nullity' — an array's `.length` had no obligation: `return a.length` verified on a possibly-null `a`,
 * and threw "Cannot get property 'length' on null object" (measured). A read of a parameter's or local's length
 * carries its receiver's nullity obligation now, as a subscript or a call on it does.
 *
 * What a path moved past didn't throw: an assignment's right side and a condition it took dereferenced no null, so
 * the receiver is non-null after it until it's rebound — `i < a.length` guards `a[i]`, and `int n = a.length` leaves
 * `a` non-null — and a null reports once, at its first dereference.
 */
class G457_p415_length_nullity {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 415: an array's `.length` on a parameter or local carries its receiver's null-dereference obligation, and what a path moved past (an assignment's right side, a condition taken) dereferenced no null after it, so a null reports once, at its first dereference (soundness fix)."

    static final List<Map> CASES = [

        // Verified before, silently: `f(null)` throws
        [group: "P415 length nullity", name: "a possibly-null array's length refutes",
         expect: ["Possible NullPointerException: Cannot get property 'length' on null object", "obligation: a != null",
                  "fails on: f(null)"],
         src: tc('''class A {
                        static int f(int[] a) { a.length }
                    }''')],

        [group: "P415 length nullity", name: "… a local's too",
         expect: ["Cannot get property 'length' on null object", "obligation: b != null"],
         src: tc('''class A {
                        static int[] mk() { null }
                        static int f() {
                            int[] b = mk()
                            return b.length
                        }
                    }''')],

        [group: "P415 length nullity", name: "a safe read has none",
         ok: true,
         src: tc('''class A {
                        static Integer f(int[] a) { a?.length }
                    }''')],

        [group: "P415 length nullity", name: "`a != null` discharges it",
         ok: true,
         src: tc('''class A {
                        @Requires({ a != null })
                        static int f(int[] a) { a.length }
                    }''')],

        // The precondition reads `a.length` before the body runs (Phase 414)
        [group: "P415 length nullity", name: "… as does a precondition that reads the length",
         ok: true,
         src: tc('''class A {
                        @Requires({ a.length > 0 })
                        static int f(int[] a) { a.length - 1 }
                    }''')],

        [group: "P415 length nullity", name: "… and a guard",
         ok: true,
         src: tc('''class A {
                        static int f(int[] a) {
                            if (a != null) return a.length
                            return 0
                        }
                    }''')],

        [group: "P415 length nullity", name: "a new array's length needs none",
         ok: true,
         src: tc('''class A {
                        static int f() {
                            int[] b = new int[3]
                            return b.length
                        }
                    }''')],

        // ── a null reports once, where it's first dereferenced ──

        // Both reported before this phase's survival facts: `a[i]` runs only after `i < a.length` didn't throw
        [group: "P415 length nullity", name: "a guard that reads the length guards the subscript",
         expect: ["Cannot get property 'length' on null object", "fails on: f(null, 0)"],
         refute: "getAt()",
         src: tc('''class A {
                        static int f(int[] a, int i) {
                            if (i >= 0 && i < a.length) return a[i]
                            return 0
                        }
                    }''')],

        // Evaluated whichever way it goes: the else branch's read is guarded too
        [group: "P415 length nullity", name: "… on either branch",
         expect: ["Cannot get property 'length' on null object", "@ line 5"],
         refute: "@ line 6",
         src: tc('''class A {
                        static int f(int[] a, int i) {
                            if (i >= a.length) return 0
                            else return a.length - i
                        }
                    }''')],

        [group: "P415 length nullity", name: "an assignment that reads it leaves the array non-null",
         expect: ["Cannot get property 'length' on null object", "@ line 5"],
         refute: "@ line 6",
         src: tc('''class A {
                        static int f(int[] a) {
                            int n = a.length
                            return n + a.length
                        }
                    }''')],

        // The same for a call that throws on null
        [group: "P415 length nullity", name: "… as does a call on a list",
         expect: ["Cannot invoke method size() on null object", "@ line 5"],
         refute: "@ line 6",
         src: tc('''class A {
                        static int f(List<Integer> xs) {
                            int n = xs.size()
                            return n + xs.size()
                        }
                    }''')],

        // Only until it's rebound: the `null` stored after the guard still fails
        [group: "P415 length nullity", name: "a rebinding after the guard still refutes",
         expect: "Cannot invoke method getAt() on null object",
         src: tc('''class A {
                        static int f(int[] a) {
                            if (a.length > 0) { a = null; return a[0] }
                            return 0
                        }
                    }''')],

        // Past the `if` its condition was false, so `a == null` was
        [group: "P415 length nullity", name: "an `||` guard proves by its left",
         ok: true,
         src: tc('''class A {
                        static int f(int[] a) {
                            if (a == null || a.length == 0) return 0
                            return a[0]
                        }
                    }''')],
    ]
}
