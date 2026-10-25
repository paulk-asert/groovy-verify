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
 * 'P357 an alias through an expression' — a helper's inferred frame (Phase 347) followed a local only when it was
 * assigned a parameter or field by name (Phase 351): `int[] b = f ? a : c; b[0] = 5` left the frame empty, so a
 * caller's claim that `a` was unchanged verified, falsely. A local's sources are now read from any right-hand side —
 * either branch of a ternary or elvis, a cast's operand, the owner of a field or element read, a for-in variable's
 * collection — and one the inference can't name (a call's result, a view like `subList`) makes the frame unbounded,
 * loudly, once something is written through the local. Rebinding a local (`b = …`) is not a write through it. Fixed
 * too: a helper's `h.n = v` on an object parameter recorded the field name `n`, not `h`, so the write was dropped.
 */
class G401_p357_alias_through_expression {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 357 an alias through an expression: a contract-free helper that writes through a local assigned a ternary, elvis, cast, field or element read of its parameters writes each of them, a for-in variable aliases its collection, a local whose source is a call or a view makes the frame unbounded loudly when written through, and rebinding a local writes nothing. Fixed: a helper writing a field of an object parameter (`h.n = 5`) had the write dropped from its frame.'

    static final List<Map> CASES = [

        // Before: compiled cleanly — the frame missed `a`, so the caller kept `a[0] == 0` across the call.
        [group: "P357 an alias through an expression", name: "a write through a ternary alias reaches the caller", expect: "Cannot prove postcondition of g",
         src: tc('''class A {
                        static void put0(int[] a, int[] c, boolean f) { int[] b = f ? a : c; if (b.length > 0) b[0] = 5 }
                        @Requires({ a.length > 0 && a[0] == 0 && c.length > 0 })
                        @Ensures({ a[0] == 0 })
                        static void g(int[] a, int[] c) { put0(a, c, true) }
                    }''')],
        [group: "P357 an alias through an expression", name: "… and an array outside both branches stays framed", ok: true,
         src: tc('''class A {
                        static void put0(int[] a, int[] c, int[] d, boolean f) { int[] b = f ? a : c; if (b != null && b.length > 0) b[0] = 5 }
                        @Requires({ d.length > 0 && d[0] == 0 })
                        @Ensures({ d[0] == 0 })
                        static void g(int[] a, int[] c, int[] d) { put0(a, c, d, true) }
                    }''')],
        // Before: compiled cleanly.
        [group: "P357 an alias through an expression", name: "an elvis alias", expect: "Cannot prove postcondition of g",
         src: tc('''class A {
                        static void put0(int[] a, int[] c) { int[] b = c ?: a; if (b.length > 0) b[0] = 5 }
                        @Requires({ a.length > 0 && a[0] == 0 && c.length > 0 })
                        @Ensures({ a[0] == 0 })
                        static void g(int[] a, int[] c) { put0(a, c) }
                    }''')],
        // Before: compiled cleanly.
        [group: "P357 an alias through an expression", name: "a cast alias", expect: "Cannot prove postcondition of g",
         src: tc('''class A {
                        static void put0(int[] a) { int[] b = (int[]) a; if (b.length > 0) b[0] = 5 }
                        @Requires({ a.length > 0 && a[0] == 0 })
                        @Ensures({ a[0] == 0 })
                        static void g(int[] a) { put0(a) }
                    }''')],
        // Before: compiled cleanly.
        [group: "P357 an alias through an expression", name: "a def local holding a ternary", expect: "Cannot prove postcondition of g",
         src: tc('''class A {
                        static void put0(int[] a, int[] c, boolean f) { def b = f ? a : c; if (b.length > 0) b[0] = 5 }
                        @Requires({ a.length > 0 && a[0] == 0 && c.length > 0 })
                        @Ensures({ a[0] == 0 })
                        static void g(int[] a, int[] c) { put0(a, c, true) }
                    }''')],
        // Before: compiled cleanly.
        [group: "P357 an alias through an expression", name: "a local holding a view is unbounded, loudly",
         expect: "a write through the local 'b', assigned from 'xs.subList(0, 1)', which may alias a parameter or field",
         src: tc('''class A {
                        static void put0(List<Integer> xs) { if (xs != null && xs.size() > 0) { List<Integer> b = xs.subList(0, 1); if (b != null) b.clear() } }
                        @Requires({ xs != null && xs.size() == 2 })
                        @Ensures({ xs.size() == 2 })
                        static void g(List<Integer> xs) { put0(xs) }
                    }''')],
        // Before: compiled cleanly — both, since only a plain-name source was followed.
        [group: "P357 an alias through an expression", name: "… as is one holding a call's result",
         expect: "a write through the local 'b', assigned from 'A.id(a)'",
         src: tc('''class A {
                        static int[] id(int[] a) { a }
                        static void put0(int[] a) { int[] b = id(a); if (b != null && b.length > 0) b[0] = 5 }
                        @Requires({ a.length > 0 && a[0] == 0 })
                        @Ensures({ a[0] == 0 })
                        static void g(int[] a) { put0(a) }
                    }''')],
        // Rebinding is not writing: `List rest = f(…)` read only (the recursive pruneWindow shape) keeps the frame empty.
        [group: "P357 an alias through an expression", name: "a call's result only read keeps the frame", ok: true,
         src: tc('''class A {
                        static int[] id(int[] a) { a }
                        static int len(int[] a) { int[] b = id(a); return b == null ? 0 : b.length }
                        @Requires({ a.length > 0 && a[0] == 0 })
                        @Ensures({ a[0] == 0 })
                        static void g(int[] a) { len(a) }
                    }''')],
        [group: "P357 an alias through an expression", name: "a local of value type copies", ok: true,
         src: tc('''class A {
                        static int pick(int[] a, int x, int y, boolean f) { int n = f ? x : y; n++; int m = a != null && a.length > 0 ? a[0] : 0; m++; return n + m }
                        @Requires({ a.length > 0 && a[0] == 0 })
                        @Ensures({ a[0] == 0 })
                        static void g(int[] a) { pick(a, 1, 2, true) }
                    }''')],
        // Before: compiled cleanly — `h.n = 5` was recorded as a write of a field `n` of A, which has none, so dropped.
        [group: "P357 an alias through an expression", name: "a helper writing an object parameter's field", expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static void put0(Box h) { if (h != null) h.n = 5 }
                        @Requires({ h != null && h.n == 0 })
                        @Ensures({ h.n == 0 })
                        static void g(Box h) { put0(h) }
                    }
                    final class Box { int n }''')],
        // Before: compiled cleanly.
        [group: "P357 an alias through an expression", name: "… or incrementing it", expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static void bump(Box h) { if (h != null) h.n++ }
                        @Requires({ h != null && h.n == 0 })
                        @Ensures({ h.n == 0 })
                        static void g(Box h) { bump(h) }
                    }
                    final class Box { int n }''')],
        [group: "P357 an alias through an expression", name: "… or writing it through a local", expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static void put0(Box h) { Box b = h; if (b != null) b.n = 5 }
                        @Requires({ h != null && h.n == 0 })
                        @Ensures({ h.n == 0 })
                        static void g(Box h) { put0(h) }
                    }
                    final class Box { int n }''')],
        // Before: compiled cleanly.
        [group: "P357 an alias through an expression", name: "an object ternary meets the Phase 194 boundary",
         expect: "writes through 'h' — parameter 'k' of the same class may alias it",
         src: tc('''final class A {
                        static void put0(Box h, Box k, boolean f) { Box b = f ? h : k; if (b != null) b.n = 5 }
                        @Requires({ h != null && h.n == 0 })
                        @Ensures({ h.n == 0 })
                        static void g(Box h, Box k) { put0(h, k, true) }
                    }
                    final class Box { int n }''')],
        // Before: compiled cleanly — a declared frame missing `h` passed the Phase 347 check.
        [group: "P357 an alias through an expression", name: "a declared frame missing the written object", expect: "Method 'put0' writes 'h', which is not in its @Modifies clause [k]",
         src: tc('''final class A {
                        @Modifies({ k })
                        static void put0(Box h, int[] k) { if (h != null) h.n = 5 }
                    }
                    final class Box { int n }''')],
        [group: "P357 an alias through an expression", name: "… and one naming it", ok: true,
         src: tc('''final class A {
                        @Modifies({ h })
                        static void put0(Box h) { if (h != null) h.n = 5 }
                    }
                    final class Box { int n }''')],
        // Before: compiled cleanly (the loop itself is outside the loop fragment, which says so).
        [group: "P357 an alias through an expression", name: "a for-in variable aliases its collection", expect: "Method 'zap' writes 'bs', which is not in its @Modifies clause [k]",
         src: tc('''final class A {
                        @Modifies({ k })
                        static void zap(List<Box> bs, int[] k) { if (bs != null) for (Box r in bs) { if (r != null) r.n = 5 } }
                    }
                    final class Box { int n }''')],
    ]
}
