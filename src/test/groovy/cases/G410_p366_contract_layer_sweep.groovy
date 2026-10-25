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
 * 'P366 contract-layer sweep' — Phase 365 swept how calls are framed; this sweeps what a method's own body and its
 * contracts are taken to mean. The encoder keeps an array, collection or map by NAME, so a local, parameter or field
 * holding another name's container (`int[] b = a`, a ternary of names, a call that may return its argument, an
 * `instanceof` pattern variable) was a second, independent object: a store through one left the other as it was,
 * and a read through one after a store into the other read the old contents. Such an alias is now loud wherever
 * the body mutates either side (a read-only alias is a faithful copy and still proves), and a helper's pattern
 * variable is an alias of what it tests. And a contract runs when it is checked: one calling a method that writes
 * (or whose writes can't be bounded) is now an error on the contract — a callee's @Requires that writes ran at every
 * call, unseen by the caller's proof.
 */
class G410_p366_contract_layer_sweep {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 366 contract-layer sweep: a container local, parameter or field that may share another name\'s contents (a copy of a name, a ternary, a call that may return its argument, an instanceof pattern variable) is loud wherever the body mutates either side, a read-only alias still proves; a helper\'s pattern variable aliases what it tests; and a @Requires, @Ensures or @Invariant calling a method that writes is an error.'

    static final List<Map> CASES = [

        // Before: verified — `b` got its own element oracles, so the store through it left `a` as it was.
        [group: "P366 contract-layer sweep", name: "a store through a local alias of a parameter is loud",
         expect: "'int[] b = a' makes 'b' share its contents with 'a', and 'b' is written",
         src: tc('''final class A {
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) { int[] b = a; b[0] = 1 }
                    }''')],

        // Before: verified — the read through `b` saw `a` as it was before the store.
        [group: "P366 contract-layer sweep", name: "… as is a read through it after a store into the original",
         expect: "and 'a' is written",
         src: tc('''final class A {
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ result == 7 })
                        static int g(int[] a) { int[] b = a; a[0] = 1; b[0] }
                    }''')],

        // Before: verified.
        [group: "P366 contract-layer sweep", name: "… a ternary of names",
         expect: "share its contents with 'a' or 'c'",
         src: tc('''final class A {
                        @Requires({ a != null && a.length > 0 && a[0] == 7 && c != null && c.length > 0 })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a, int[] c, boolean f) { int[] b = f ? a : c; b[0] = 1 }
                    }''')],

        // Before: verified — a call returning its argument was a fresh list.
        [group: "P366 contract-layer sweep", name: "… a call that may return what it is handed",
         expect: "share its contents with a value the verifier can't name",
         src: tc('''final class A {
                        static List<Integer> id(List<Integer> a) { a }
                        @Requires({ xs != null && xs.size() == 0 })
                        @Ensures({ xs.size() == 0 })
                        static void g(List<Integer> xs) { List<Integer> ys = id(xs); ys << 1 }
                    }''')],

        // Before: verified.
        [group: "P366 contract-layer sweep", name: "… a field assigned a parameter",
         expect: "makes 'buf' share its contents with 'a'",
         src: tc('''final class A {
                        int[] buf
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        void g(int[] a) { buf = a; buf[0] = 1 }
                    }''')],

        // Before: verified — the `instanceof` pattern variable is the object tested.
        [group: "P366 contract-layer sweep", name: "… an instanceof pattern variable",
         expect: "makes 'b' share its contents with 'a'",
         src: tc('''final class A {
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(Object o, int[] a) { if (a instanceof int[] b) { b[0] = 1 } }
                    }''')],

        // Before: verified — a loop's stores through the alias.
        [group: "P366 contract-layer sweep", name: "… and in a loop",
         expect: "Skipped loop verification for g ('int[] b = a' makes 'b' share its contents with 'a'",
         src: tc('''final class A {
                        @Requires({ a != null && a.length == 3 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) {
                            int[] b = a
                            @Invariant({ 0 <= i && i <= 3 })
                            @Decreases({ 3 - i })
                            for (int i = 0; i < 3; i++) { b[i] = 1 }
                        }
                    }''')],

        // Before: refuted — over-strict, `b` had a length of its own.
        [group: "P366 contract-layer sweep", name: "a read-only alias is a faithful copy, and still proves", ok: true,
         src: tc('''final class A {
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ result == 7 })
                        static int g(int[] a) { int[] b = a; b.length > 0 ? b[0] : 0 }
                    }''')],

        [group: "P366 contract-layer sweep", name: "… as does a local from a call that returns a fresh array", ok: true,
         src: tc('''final class A {
                        static int[] mk() { new int[1] }
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) { int[] b = mk(); if (b != null && b.length > 0) b[0] = 1 }
                    }''')],

        // Before: verified — a helper's write through its pattern variable was a write to a local.
        [group: "P366 contract-layer sweep", name: "a helper writing through an instanceof pattern variable writes its argument",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static void h(Object o) { if (o instanceof int[] b) { if (b.length > 0) b[0] = 1 } }
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) { h(a) }
                    }''')],

        // Before: verified.
        [group: "P366 contract-layer sweep", name: "… a list too",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static void h(Object o) { if (o instanceof List b) { b.clear() } }
                        @Requires({ xs != null && xs.size() == 1 })
                        @Ensures({ xs.size() == 1 })
                        static void g(List<Integer> xs) { h(xs) }
                    }''')],

        // Before: skipped (the precondition was outside the fragment) — now named for what it is.
        [group: "P366 contract-layer sweep", name: "a @Requires calling a method that writes is an error",
         expect: "The @Requires of g calls 'bump(…)', which writes 'a'",
         src: tc('''final class A {
                        static boolean bump(int[] a) { if (a.length > 0) a[0] = 1; true }
                        @Requires({ a != null && a.length > 0 && a[0] == 7 && bump(a) })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) { }
                    }''')],

        // Before: skipped.
        [group: "P366 contract-layer sweep", name: "… an @Ensures",
         expect: "The @Ensures of g calls 'peek(…)', which writes 'n'",
         src: tc('''final class A {
                        static int n
                        static boolean peek() { n = 1; true }
                        @Requires({ n == 7 })
                        @Ensures({ peek() && n == 7 })
                        static void g() { }
                    }''')],

        // Before: g verified — h's precondition was skipped, but it still runs `bump(a)` at every call.
        [group: "P366 contract-layer sweep", name: "… a callee's @Requires, which runs at the caller's call",
         expect: "The @Requires of h calls 'bump(…)', which writes 'a'",
         src: tc('''final class A {
                        static boolean bump(int[] a) { if (a.length > 0) a[0] = 1; true }
                        @Requires({ a != null && bump(a) })
                        static void h(int[] a) { }
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) { h(a) }
                    }''')],

        // Before: skipped.
        [group: "P366 contract-layer sweep", name: "… or an @Invariant",
         expect: "The @Invariant of A calls 'touch(…)', which writes 'k'",
         src: tc('''@Invariant({ n >= 0 && touch() })
                    final class A {
                        int n
                        int k
                        boolean touch() { k = 1; true }
                        void g() { n = 1 }
                    }''')],

        [group: "P366 contract-layer sweep", name: "a contract calling a method that writes nothing is fine", ok: true,
         src: tc('''final class A {
                        static boolean seven(int x) { x == 7 }
                        @Requires({ a != null && a.length > 0 && seven(a[0]) })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) { }
                    }''')],
    ]
}
