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
 * 'P390 callable site frames' — since Phase 373 a helper that calls a callable parameter has an unbounded frame (its
 * body may write anything it reaches), so a caller's postcondition over `h({ … }, a)` was skipped. At a call site that
 * hands the parameter a closure literal (or a local bound only to one), the call runs that literal: what it writes
 * through its own parameters lands on the arguments it is handed, in the helper's frame, and what it writes of the
 * caller's (a field, a captured local, a parameter's contents) is havocked at the call. A callable that isn't a literal
 * at the site — a parameter passed through, one the helper reassigns or hands on — keeps the unbounded frame.
 */
class G433_p390_callable_site_frames {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 390: a call handing a helper a closure literal frames the helper by what that literal writes — through its parameters onto the arguments, and the caller's own captured state — instead of skipping the caller's postcondition."

    static final String POST = "Cannot prove postcondition of g"
    static final String UNBOUNDED = "whose body may write anything it reaches"

    static final List<Map> CASES = [

        // Before: `Skipped verification of postcondition for g (call 'h(…)' whose writes can't be bounded …)`.
        [group: "P390 callable site frames", name: "a literal that writes nothing leaves the argument framed",
         ok: true,
         src: tc('''final class A {
                        @Requires({ c != null })
                        static void h(Closure c, int[] b) { c.call(b) }
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) { h({ int[] x -> int y = 0 }, a) }
                    }''')],

        [group: "P390 callable site frames", name: "a literal writing its parameter writes the argument",
         expect: [POST, "fails on: g([7] as int[])"],
         src: tc('''final class A {
                        static void h(Closure c, int[] b) { c.call(b) }
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) { h({ int[] x -> x[0] = 1 }, a) }
                    }''')],

        // (the literal's own `x[0]` keeps its index obligation — its parameter's size is the closure's to know)
        [group: "P390 callable site frames", name: "… and only that argument",
         expect: "index may be out of bounds", refute: POST,
         src: tc('''final class A {
                        @Requires({ c != null && b != null && b.length > 0 })
                        static void h(Closure c, int[] b) { c.call(b) }
                        @Requires({ a != null && a.length > 0 && z != null && z.length > 0 && z[0] == 7 })
                        @Ensures({ z[0] == 7 })
                        static void g(int[] a, int[] z) { h({ int[] x -> x[0] = 1 }, a) }
                    }''')],

        [group: "P390 callable site frames", name: "the helper's own writes still count",
         expect: [POST, "fails on: g([7] as int[])"],
         src: tc('''final class A {
                        static void h(Closure c, int[] b) { c.call(b); b[0] = 3 }
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) { h({ int[] x -> int y = x[0] }, a) }
                    }''')],

        [group: "P390 callable site frames", name: "a literal writing the caller's field",
         expect: [POST, "count (after a call)", "fails on: g()"],
         src: tc('''class A {
                        int count
                        static void h(Closure c) { c.call() }
                        @Ensures({ count == 0 })
                        void g() {
                            count = 0
                            h({ count = 1 })
                        }
                    }''')],

        [group: "P390 callable site frames", name: "… a captured local",
         expect: [POST, "fails on: g()"],
         src: tc('''class A {
                        static void h(Closure c) { c.call() }
                        @Ensures({ result == 0 })
                        static int g() {
                            int n = 0
                            h({ n = 5 })
                            return n
                        }
                    }''')],

        [group: "P390 callable site frames", name: "… through a method of the caller's class",
         expect: [POST, "fails on: g()"],
         src: tc('''final class A {
                        int count
                        void bump() { count = count + 1 }
                        static void h(Closure c) { c.call() }
                        @Ensures({ count == 0 })
                        void g() {
                            count = 0
                            h({ bump() })
                        }
                    }''')],

        [group: "P390 callable site frames", name: "a local bound to a literal",
         expect: [POST, "fails on: g([7] as int[])"],
         src: tc('''final class A {
                        static void h(Closure c, int[] b) { c.call(b) }
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) {
                            Closure k = { int[] x -> x[0] = 1 }
                            h(k, a)
                        }
                    }''')],

        [group: "P390 callable site frames", name: "a lambda for a Function parameter",
         ok: true,
         src: tc('''final class A {
                        @Requires({ f != null })
                        static int h(java.util.function.Function<int[], Integer> f, int[] b) { f.apply(b) }
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) { h((int[] x) -> x.length, a) }
                    }''')],

        [group: "P390 callable site frames", name: "… and one that writes",
         expect: [POST, "fails on: g([7] as int[])"],
         src: tc('''final class A {
                        static int h(java.util.function.Function<int[], Integer> f, int[] b) { f.apply(b) }
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) { h({ int[] x -> x[0] = 1; 0 } as java.util.function.Function<int[], Integer>, a) }
                    }''')],

        // Unbounded still: the callable isn't a literal at the site, or the helper doesn't just call it
        [group: "P390 callable site frames", name: "a callable parameter passed through stays unbounded",
         expect: UNBOUNDED,
         src: tc('''class A {
                        int count
                        static void h(Closure c) { c.call() }
                        @Requires({ c != null })
                        @Ensures({ count == 0 })
                        void g(Closure c) {
                            count = 0
                            h(c)
                        }
                    }''')],

        [group: "P390 callable site frames", name: "… as does one the helper reassigns",
         expect: UNBOUNDED,
         src: tc('''final class A {
                        static void h(Closure c, int[] b) { c = { int[] x -> x[0] = 2 }; c.call(b) }
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) { h({ int[] x -> int y = 0 }, a) }
                    }''')],

        [group: "P390 callable site frames", name: "… or hands on",
         expect: UNBOUNDED,
         src: tc('''final class A {
                        static void h2(Closure c, int[] b) { c.call(b) }
                        static void h(Closure c, int[] b) { h2(c, b) }
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) { h({ int[] x -> x[0] = 1 }, a) }
                    }''')],

        [group: "P390 callable site frames", name: "… or a literal running the caller's own callable",
         expect: UNBOUNDED,
         src: tc('''final class A {
                        static void h(Closure c) { c.call() }
                        @Requires({ a != null && a.length > 0 && a[0] == 7 && k != null })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a, Closure k) { h({ k.call(a) }) }
                    }''')],

        // Before: `Skipped verification of precondition for h (actual argument '{ int[] x -> ... }' is outside fragment)`.
        [group: "P390 callable site frames", name: "a closure literal discharges a callable's non-null precondition",
         refute: "Skipped verification of precondition for h", ok: true,
         src: tc('''final class A {
                        @Requires({ c != null })
                        static void h(Closure c, int[] b) { c.call(b) }
                        @Requires({ a != null && a.length > 0 })
                        static void g(int[] a) { h({ int[] x -> int y = 0 }, a) }
                    }''')],
    ]
}
