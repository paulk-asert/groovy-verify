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
 * 'P369 cleanup' — loose ends from Phases 365–368, each wrong or misleading output: a non-null object argument was
 * rendered `null` in the failing call (`g(null)` under `@Requires({ c != null })`) and its fields shown as the
 * encoder's `c$count`; Groovy's negative indices count from the end (`xs[-1]` is the last element), which the encoder
 * read as an index below 0, and a list subscript past the end reads null rather than throwing, which the warning
 * claimed; `apply`/`call` were reads whose arguments were never written; and a closure literal's generated class
 * stood in as an override of `Closure.call`, naming its own `doCall` as the reason.
 */
class G413_p369_cleanup {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 369 cleanup: a failing call builds a non-null object argument (new C(count: 5)) and shows its fields as c.count; a negative constant index counts from the end (xs[-1], a[-2] = v); a list subscript out of range is reported as reading null, not throwing; apply/call may write their arguments; a closure literal\'s generated class is no override of Closure.call.'

    static final List<Map> CASES = [

        // Before: `fails on: g(null)` — a non-null object argument rendered as null, against the @Requires.
        [group: "P369 cleanup", name: "a non-null object argument is built, not rendered null",
         expect: "fails on: g(new C(count: 5))",
         src: tc('''final class A {
                        @Requires({ c != null && c.count > 3 })
                        @Ensures({ result < 5 })
                        static int g(C c) { c.count }
                    }
                    final class C { int count }''')],

        // Before: `c$count = 5`, the encoder's name for the field.
        [group: "P369 cleanup", name: "… and its field is shown as the source spells it",
         expect: "counterexample: c.count = 5",
         src: tc('''final class A {
                        @Requires({ c != null && c.count > 3 })
                        @Ensures({ result < 5 })
                        static int g(C c) { c.count }
                    }
                    final class C { int count }''')],

        // Before: a bounds warning — Groovy's xs[-1] is the last element, which the encoder read as index -1.
        [group: "P369 cleanup", name: "xs[-1] is the last element", ok: true,
         src: tc('''final class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result == xs[xs.size() - 1] })
                        static int g(List<Integer> xs) { xs[-1] }
                    }''')],

        // Before: a bounds warning.
        [group: "P369 cleanup", name: "… and a[-2] the last but one", ok: true,
         src: tc('''final class A {
                        @Requires({ a != null && a.length > 1 })
                        @Ensures({ result == a[a.length - 2] })
                        static int g(int[] a) { a[-2] }
                    }''')],

        // Before: a bounds warning, and the store landed at index -1.
        [group: "P369 cleanup", name: "… and a store through a negative index writes there", ok: true,
         src: tc('''final class A {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ a[a.length - 1] == 9 })
                        static void g(int[] a) { a[-1] = 9 }
                    }''')],

        [group: "P369 cleanup", name: "xs[-1] on a possibly-empty list still throws, and says so",
         expect: "obligation: 0 <= xs.size() - 1",
         src: tc('''final class A {
                        @Requires({ xs != null })
                        static int g(List<Integer> xs) { xs[-1] }
                    }''')],

        // Before: 'Possible IndexOutOfBoundsException' — but a list subscript past the end reads null.
        [group: "P369 cleanup", name: "a list subscript out of range is named for what it does",
         expect: "List index may be outside [0, size)",
         src: tc('''final class A {
                        @Requires({ xs != null })
                        static int g(List<Integer> xs, int i) { xs[i] }
                    }''')],

        [group: "P369 cleanup", name: "… while get(i), which does throw, keeps the exception",
         expect: "Possible IndexOutOfBoundsException",
         src: tc('''final class A {
                        @Requires({ xs != null })
                        static int g(List<Integer> xs, int i) { xs.get(i) }
                    }''')],

        // Before: verified — `apply` is a read of the function, so what it is handed was never written. Phase 373: the
        // function may write anything it reaches, not only its argument, so h's frame is unbounded and g is skipped.
        [group: "P369 cleanup", name: "applying a function may write its argument",
         expect: "a call of the callable 'f', whose body may write anything it reaches",
         src: tc('''final class A {
                        @Requires({ f != null })
                        static int h(java.util.function.Function<int[], Integer> f, int[] b) { f.apply(b) }
                        @Requires({ f != null && a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(java.util.function.Function<int[], Integer> f, int[] a) { h(f, a) }
                    }''')],

        // Phase 373 — this verified, unsoundly: f may capture the very array g is handed (`h({ x -> a[0] = 1; x }, a)`),
        // so an immutable argument doesn't bound what it writes.
        [group: "P369 cleanup", name: "… nor does an immutable argument bound it",
         expect: "a call of the callable 'f', whose body may write anything it reaches", refute: "Cannot prove",
         src: tc('''final class A {
                        @Requires({ f != null })
                        static int h(java.util.function.Function<Integer, Integer> f, int[] b) { f.apply(1) }
                        @Requires({ f != null && a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(java.util.function.Function<Integer, Integer> f, int[] a) { h(f, a) }
                    }''')],

        // Before: the reason named the generated closure class's `doCall` (`a call on 'error.getStackTrace()'`).
        // Phase 373: the reason is h's call of the closure it is handed. Phase 390: at this site h runs the literal,
        // which writes `x[0] = 1` through the `b` it is handed, so the frame is {b} and `a[0] == 7` refutes.
        [group: "P369 cleanup", name: "a closure literal handed to a helper runs where it is called",
         expect: ["Cannot prove postcondition of g", "fails on: g([7] as int[])"], refute: "doCall",
         src: tc('''final class A {
                        @Requires({ c != null })
                        static void h(Closure c, int[] b) { c.call(b) }
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) { h({ int[] x -> x[0] = 1 }, a) }
                    }''')],
    ]
}
