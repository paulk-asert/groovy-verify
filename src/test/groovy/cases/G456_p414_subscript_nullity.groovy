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
 * 'P414 subscript nullity' — a subscript had a bounds obligation but no null one: `a[i]` on a possibly-null array,
 * list, map or string verified, and threw "Cannot invoke method getAt() on null object" (measured: `putAt()` for a
 * store). Each subscript on a parameter or local carries its receiver's nullity obligation now, as a call on it does.
 *
 * A precondition the body never sees fail is checked before the body runs, and one that dereferences a reference
 * throws on a null there: `@Requires({ a.length > 0 })` admits no null `a`, so it discharges `a[0]`'s obligation (and
 * a call's) with no `a != null` written. Only what's evaluated whenever the precondition is counts — not the right of
 * an `||`, a ternary's arms or a closure's body — and a call null answers (`a.every { … }` is true on null, dispatched
 * dynamically) dereferences nothing.
 */
class G456_p414_subscript_nullity {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 414: a subscript on a parameter or local carries its receiver's null-dereference obligation (getAt/putAt on null throws), and a precondition that dereferences a reference wherever it's evaluated (`a.length > 0`, `xs[0] == 1`) admits no null there (soundness fix)."

    static final List<Map> CASES = [

        // Verified before, silently: `f(null)` throws at `a[1]` (`a.length` is read only when `a` isn't null, so the
        // precondition admits one)
        [group: "P414 subscript nullity", name: "a read through a possibly-null array refutes",
         expect: ["Possible NullPointerException: Cannot invoke method getAt() on null object", "obligation: a != null",
                  "fails on: f(null)"],
         refute: "a.length =",
         src: tc('''class A {
                        @Requires({ a == null || a.length > 1 })
                        static int f(int[] a) { a[1] }
                    }''')],

        [group: "P414 subscript nullity", name: "… and a store through one calls putAt",
         expect: ["Cannot invoke method putAt() on null object", "fails on: f(null)"],
         src: tc('''class A {
                        @Requires({ a == null || a.length > 1 })
                        static void f(int[] a) { a[1] = 1 }
                    }''')],

        // (a string's bounds read its length since Phase 416, so its null is the one that fails)
        [group: "P414 subscript nullity", name: "a list's, a map's and a string's subscripts too",
         expect: ["obligation: xs != null", "obligation: m != null", "obligation: s != null"],
         refute: "IndexOutOfBoundsException",
         src: tc('''class A {
                        @Requires({ xs == null || xs.size() > 0 })
                        static Object f(List<Integer> xs) { xs[0] }
                        static Object g(Map<String, Integer> m) { m['k'] }
                        @Requires({ s == null || s.size() > 0 })
                        static String h(String s) { s[0] }
                    }''')],

        // A non-null receiver's bounds are the index obligation's: its failing call is no null
        [group: "P414 subscript nullity", name: "an index out of bounds fails on an array, not a null",
         expect: ["Possible IndexOutOfBoundsException", "fails on: f(new int[0])"],
         src: tc('''class A {
                        static int f(int[] a) { a[0] }
                    }''')],

        [group: "P414 subscript nullity", name: "`a != null` discharges it",
         ok: true,
         src: tc('''class A {
                        @Requires({ a != null && a.length > 0 })
                        static int f(int[] a) { a[0] }
                    }''')],

        [group: "P414 subscript nullity", name: "… as does a guard",
         ok: true,
         src: tc('''class A {
                        static int f(int[] a) { a != null && a.length > 0 ? a[0] : 0 }
                    }''')],

        // ── a precondition that dereferences ──

        [group: "P414 subscript nullity", name: "a precondition that reads `a.length` admits no null `a`",
         ok: true,
         src: tc('''class A {
                        @Requires({ a.length > 0 })
                        static int f(int[] a) { a[0] }
                    }''')],

        // A false positive before, for a call: `xs.size() > 0` throws on a null `xs`, so `f(null)` never ran the body
        [group: "P414 subscript nullity", name: "… nor one that calls `xs.size()` a null `xs`",
         ok: true,
         src: tc('''class A {
                        @Requires({ xs.size() > 0 })
                        static int f(List<Integer> xs) { xs.get(0) }
                    }''')],

        [group: "P414 subscript nullity", name: "… nor one that subscripts it, under an `&&`",
         ok: true,
         src: tc('''class A {
                        @Requires({ n > 0 && m['k'] == n })
                        static int f(Map<String, Integer> m, int n) { m['k'] }
                    }''')],

        // `null.every { … }` is true, dispatched dynamically (measured)
        [group: "P414 subscript nullity", name: "a call null answers dereferences nothing",
         expect: ["Cannot invoke method getAt() on null object", "fails on: f(null)"],
         src: tc('''class A {
                        @Requires({ a.every { int x -> x > 0 } && (a == null || a.length > 0) })
                        static int f(int[] a) { a[0] }
                    }''')],

        // `a` is never rebound, so the loop's writes into it leave it non-null
        [group: "P414 subscript nullity", name: "the entry's non-null lasts through a loop that writes the contents",
         ok: true,
         src: tc('''class A {
                        @Requires({ a.length >= 0 })
                        static void zero(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) { a[i] = 0; i = i + 1 }
                        }
                    }''')],

        // A false positive before, for a postcondition over the maps: the precondition subscripts both
        [group: "P414 subscript nullity", name: "a postcondition's helper sees the precondition's non-null",
         ok: true,
         src: tc('''class A {
                        static boolean ok(Map<String, Integer> m) { m != null && m['k'] == 1 }
                        @Requires({ m['k'] == 1 })
                        @Ensures({ ok(m) })
                        static void f(Map<String, Integer> m) {}
                    }''')],

        // ── locals ──

        [group: "P414 subscript nullity", name: "a local array creation or clone is never null",
         ok: true,
         src: tc('''class A {
                        @Requires({ n > 0 && a.length > 0 })
                        static int f(int[] a, int n) {
                            int[] r = new int[n]
                            r[0] = 1
                            int[] c = a.clone()
                            return c.length > 0 ? r[0] + c[0] : r[0]
                        }
                    }''')],

        // Since Phase 415 the null is reported at its first dereference, `b.length`, which guards the store
        [group: "P414 subscript nullity", name: "… but a local from a call may be",
         expect: ["Cannot get property 'length' on null object", "obligation: b != null"],
         refute: "putAt()",
         src: tc('''class A {
                        static int[] mk() { new int[1] }
                        static void f() { int[] b = mk(); if (b.length > 0) b[0] = 1 }
                    }''')],
    ]
}
