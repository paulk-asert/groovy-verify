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
 * 'P358 a copy is a read, a user method is not' — the write collector reads a call it doesn't know as writing its
 * receiver (Phase 347), so `a.clone()` counted as a write of `a`: a helper copying an array before writing the copy
 * lost its caller's facts about the original, and a loop holding a clone dropped every loop-stable precondition over
 * it. `clone`, `toSorted` and `toUnique` are reads now, with the GDK's `grep`, `findResult(s)`, `countBy`, `indexed`
 * and `collectNested` in callee inference. The other side of the same name test was unsound: a name on the read
 * lists was taken as the library's method whatever the receiver, so a sibling class's own `size()` that writes was a
 * read — in a helper's frame and in a method body loop's write set — and the caller kept a stale field. A method the
 * receiver's own class (compiled from source) declares is now never read by its name; a receiver with no declared
 * type defers to any class of the source declaring the name. And an unknown method on a receiver with no name
 * (`id(h).size()`) wrote nothing: it is unbounded, loudly, unless the receiver is a fresh value.
 */
class G402_p358_copy_reads {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 358 a copy is a read, a user method is not: `clone()`, `toSorted()` and `toUnique()` (and in a helper `grep`, `findResult(s)`, `countBy`, `indexed`, `collectNested`) no longer count as writing their receiver, so a helper or loop writing a copy keeps the facts about the original. Fixed: a method named like a library read but declared by the receiver\'s own class — a sibling\'s `size()` that writes — was taken as a pure read in a helper\'s frame and a loop\'s write set; and an unknown method on a receiver with no name (`id(h).size()`) wrote nothing, now loud unless the receiver is fresh.'

    static final List<Map> CASES = [

        // Before: "Cannot prove postcondition of g" — `a.clone()` was read as writing `a`, so `a` was havocked.
        [group: "P358 a copy is a read, a user method is not", name: "a helper writing a clone keeps the original", ok: true,
         src: tc('''class A {
                        static void put0(int[] a) { if (a != null) { int[] b = a.clone(); if (b.length > 0) b[0] = 5 } }
                        @Requires({ a != null && a.length > 0 && a[0] == 0 })
                        @Ensures({ a[0] == 0 })
                        static void g(int[] a) { put0(a) }
                    }''')],
        [group: "P358 a copy is a read, a user method is not", name: "… and writing the original still refutes", expect: "Cannot prove postcondition of g",
         src: tc('''class A {
                        static void put0(int[] a) { if (a != null) { int[] b = a.clone(); if (a.length > 0) a[0] = b.length } }
                        @Requires({ a != null && a.length > 0 && a[0] == 0 })
                        @Ensures({ a[0] == 0 })
                        static void g(int[] a) { put0(a) }
                    }''')],
        // Before: "Cannot prove postcondition of g" — the size oracle was havocked as for a mutator.
        [group: "P358 a copy is a read, a user method is not", name: "clearing a sorted copy keeps the list's size", ok: true,
         src: tc('''class A {
                        static void put0(List<Integer> xs) { if (xs != null) { List<Integer> b = xs.toSorted(); if (b != null) b.clear() } }
                        @Requires({ xs != null && xs.size() == 2 })
                        @Ensures({ xs.size() == 2 })
                        static void g(List<Integer> xs) { put0(xs) }
                    }''')],
        // Before: "Cannot prove postcondition of g" — the loop's write set bailed on the call, dropping `a[0] == 0`.
        [group: "P358 a copy is a read, a user method is not", name: "a loop taking a clone keeps a loop-stable precondition", ok: true,
         src: tc('''class A {
                        @Requires({ a != null && a.length > 0 && a[0] == 0 && k >= 0 })
                        @Ensures({ a[0] == 0 })
                        static void g(int[] a, int k) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= k })
                            @Decreases({ k - i })
                            while (i < k) { int[] b = a.clone(); i = i + 1 }
                        }
                    }''')],
        // Before: compiled cleanly — `size` is on the read list, so Box's own size() was taken as List.size().
        [group: "P358 a copy is a read, a user method is not", name: "a sibling's own size() that writes, in a helper", expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static int peek(Box h) { h == null ? 0 : h.size() }
                        @Requires({ h != null && h.n == 0 })
                        @Ensures({ h.n == 0 })
                        static void g(Box h) { peek(h) }
                    }
                    final class Box { int n; int size() { n = n + 1; return n } }''')],
        // Before: compiled cleanly.
        [group: "P358 a copy is a read, a user method is not", name: "… through a local", expect: "Cannot prove postcondition of g",
         src: tc('''class A {
                        static int peek(Box h) { Box b = h; b == null ? 0 : b.size() }
                        @Requires({ h != null && h.n == 0 })
                        @Ensures({ h.n == 0 })
                        static void g(Box h) { peek(h) }
                    }
                    class Box { int n; int size() { n = n + 1; return n } }''')],
        // Before: compiled cleanly — the loop's write set read `h.size()` as pure, so `h.n == 0` stayed loop-stable.
        [group: "P358 a copy is a read, a user method is not", name: "… in a method body loop", expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        @Requires({ h != null && h.n == 0 && k >= 0 })
                        @Ensures({ h.n == 0 })
                        static void g(Box h, int k) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= k })
                            @Decreases({ k - i })
                            while (i < k) { h.size(); i = i + 1 }
                        }
                    }
                    final class Box { int n; int size() { n = n + 1; return n } }''')],
        // Before: compiled cleanly.
        [group: "P358 a copy is a read, a user method is not", name: "… through a def local", expect: "Cannot prove postcondition of g",
         src: tc('''class A {
                        static int peek(Box h) { def b = h; b == null ? 0 : b.size() }
                        @Requires({ h != null && h.n == 0 })
                        @Ensures({ h.n == 0 })
                        static void g(Box h) { peek(h) }
                    }
                    class Box { int n; int size() { n = n + 1; return n } }''')],
        // Before: compiled cleanly — a receiver with no name contributed only its own writes, though `id(h)` is `h`.
        [group: "P358 a copy is a read, a user method is not", name: "a call on a call's result is unbounded, loudly",
         expect: "a call on 'A.id(h)', which may be a parameter or field and may write it",
         src: tc('''class A {
                        static Box id(Box h) { h }
                        static int peek(Box h) { id(h)?.size() ?: 0 }
                        @Requires({ h != null && h.n == 0 })
                        @Ensures({ h.n == 0 })
                        static void g(Box h) { peek(h) }
                    }
                    class Box { int n; int size() { n = n + 1; return n } }''')],
        [group: "P358 a copy is a read, a user method is not", name: "a sibling's own clone() that writes", expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static void dup(Box h) { if (h != null) h.clone() }
                        @Requires({ h != null && h.n == 0 })
                        @Ensures({ h.n == 0 })
                        static void g(Box h) { dup(h) }
                    }
                    final class Box { int n; Box clone() { n = 1; return new Box() } }''')],
        [group: "P358 a copy is a read, a user method is not", name: "a sibling's own size() that only reads is framed by its body", ok: true,
         src: tc('''final class A {
                        static int peek(Box h) { h == null ? 0 : h.size() }
                        @Requires({ h != null && h.n == 0 })
                        @Ensures({ h.n == 0 })
                        static void g(Box h) { peek(h) }
                    }
                    final class Box { int n; int size() { n } }''')],
    ]
}
