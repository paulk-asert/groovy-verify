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
 * 'P393 helper closure facts' — a closure literal handed to a helper had its own obligations checked with its
 * parameters free (`h({ int[] x -> x[0] = 1 }, a)` warned on `x[0]` whatever the caller knew of `a`). When the helper
 * only calls the parameter, always passing the same formal it never reassigns, the literal's parameter IS the caller's
 * actual: equal to it (a value), or the same object (an array's length, a reference's nullity — not its contents).
 * Phase 380's range facts, for helpers.
 */
class G436_p393_helper_closure_facts {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 393: a closure literal handed to a helper that only calls it on one of its own arguments has that argument's facts for its parameter (a value's, an array's length and nullity) when its obligations are checked."

    static final String OOB = "index may be out of bounds"
    static final String DIV = "Possible ArithmeticException: Division by zero"

    static final List<Map> CASES = [

        // Before: `index may be out of bounds … 0 < x.size()`, the closure's parameter free.
        [group: "P393 helper closure facts", name: "a helper's array argument bounds its literal's index",
         ok: true,
         src: tc('''final class A {
                            @Requires({ c != null })
                            static void h(Closure c, int[] b) { c.call(b) }
                            @Requires({ a != null && a.length > 0 })
                            static void g(int[] a) { h({ int[] x -> x[0] = 1 }, a) }
                        }''')],

        [group: "P393 helper closure facts", name: "… and an unbounded one still warns",
         expect: [OOB],
         src: tc('''final class A {
                            @Requires({ c != null })
                            static void h(Closure c, int[] b) { c.call(b) }
                            @Requires({ a != null })
                            static void g(int[] a) { h({ int[] x -> x[0] = 1 }, a) }
                        }''')],

        [group: "P393 helper closure facts", name: "… its nullity too",
         ok: true,
         src: tc('''final class A {
                            @Requires({ c != null })
                            static void h(Closure c, int[] b) { c.call(b) }
                            @Requires({ a != null })
                            static int g(int[] a) { int r = 0; h({ int[] x -> r = x.length }, a); return r }
                        }''')],

        // Before: the divisor `x` was free, and the coerced literal skipped h's `f != null`.
        [group: "P393 helper closure facts", name: "a helper's scalar argument is the literal's parameter",
         ok: true,
         src: tc('''final class A {
                            @Requires({ f != null })
                            static int h(java.util.function.Function<Integer, Integer> f, int d) { f.apply(d) }
                            @Requires({ d != 0 })
                            static int g(int d) { h({ Integer x -> 100.intdiv(x) } as java.util.function.Function<Integer, Integer>, d) }
                        }''')],

        [group: "P393 helper closure facts", name: "… and an unconstrained one still warns",
         expect: [DIV],
         src: tc('''final class A {
                            @Requires({ f != null })
                            static int h(java.util.function.Function<Integer, Integer> f, int d) { f.apply(d) }
                            static int g(int d) { h({ Integer x -> 100.intdiv(x) } as java.util.function.Function<Integer, Integer>, d) }
                        }''')],

        [group: "P393 helper closure facts", name: "a helper calling the literal on something else gives no fact",
         expect: [OOB],
         src: tc('''final class A {
                            @Requires({ c != null })
                            static void h(Closure c, int[] b) { c.call(new int[0]) }
                            @Requires({ a != null && a.length > 0 })
                            static void g(int[] a) { h({ int[] x -> x[0] = 1 }, a) }
                        }''')],

        [group: "P393 helper closure facts", name: "… nor one calling it on two different arguments",
         expect: [OOB],
         src: tc('''final class A {
                            @Requires({ c != null })
                            static void h(Closure c, int[] b, int[] e) { c.call(b); c.call(e) }
                            @Requires({ a != null && a.length > 0 && z != null })
                            static void g(int[] a, int[] z) { h({ int[] x -> x[0] = 1 }, a, z) }
                        }''')],

        [group: "P393 helper closure facts", name: "… nor one that keeps the callable",
         expect: [OOB],
         src: tc('''final class A {
                            static Closure saved
                            @Requires({ c != null })
                            static void h(Closure c, int[] b) { saved = c; c.call(b) }
                            @Requires({ a != null && a.length > 0 })
                            static void g(int[] a) { h({ int[] x -> x[0] = 1 }, a) }
                        }''')],

        [group: "P393 helper closure facts", name: "… nor one that reassigns the argument first",
         expect: [OOB],
         src: tc('''final class A {
                            @Requires({ c != null })
                            static void h(Closure c, int[] b) { b = new int[0]; c.call(b) }
                            @Requires({ a != null && a.length > 0 })
                            static void g(int[] a) { h({ int[] x -> x[0] = 1 }, a) }
                        }''')],

        [group: "P393 helper closure facts", name: "… nor one an override may replace",
         expect: [OOB],
         src: tc('''class A {
                            void h(Closure c, int[] b) { c.call(b) }
                            @Requires({ a != null && a.length > 0 })
                            void g(int[] a) { h({ int[] x -> x[0] = 1 }, a) }
                        }''')],

        // Conservative: the literal writes `d`, which it was handed, so the fact isn't read past the havoc.
        [group: "P393 helper closure facts", name: "an actual the literal itself writes gives no fact",
         expect: [DIV],
         src: tc('''final class A {
                            @Requires({ c != null })
                            static void h(Closure c, int d) { c.call(d) }
                            @Requires({ d != 0 })
                            static int g(int d) {
                                int r = 0
                                h({ int x -> r = 100.intdiv(x); d = 0 }, d)
                                return r
                            }
                        }''')],
    ]
}
