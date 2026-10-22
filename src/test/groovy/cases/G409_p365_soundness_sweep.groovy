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
 * 'P365 soundness sweep' — a sweep of shapes neighbouring Phases 357–364 found four families of silent holes.
 * A callee was resolved by name and arity, so an overload's contract, frame or value stood in for the one STC chose.
 * A frame names fields bare, so a write to a field another class owns — the caller's static written from another
 * class, an outer class's field written from an inner one — was read as the writer's own, or as a local. A written
 * formal handed `this` havocked nothing. And an unknown library call was read as writing its receiver only, though
 * many fill what they are handed. Now overloads follow the call's STC target (several with no target: none is
 * assumed), another unit class's static keeps its `Sib$field` name in a frame and maps back to the caller that owns
 * it, an enclosing instance's field and a `this` actual are loud, and an unknown call's mutable arguments are written.
 */
class G409_p365_soundness_sweep {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 365 soundness sweep: an overloaded callee is the overload STC chose (its contract, frame and value); a write to another class\'s static is framed for the caller that owns it, an enclosing instance\'s field and a written `this` are loud, and an unknown call may write the arguments it is handed (nextBytes, getChars, read, drainTo, collect(dst), a closure call).'

    static final List<Map> CASES = [

        // Before: verified — `h(a)` resolved by name + arity to the first overload, h(Object), whose frame is empty.
        [group: "P365 soundness sweep", name: "an overloaded callee's frame is the overload STC chose",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static void h(Object o) { }
                        static void h(int[] a) { a[0] = 1 }
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) { h(a) }
                    }''')],

        // Before: verified — h(long)'s body was evaluated as the value of `h(1)`, which runs h(int).
        [group: "P365 soundness sweep", name: "… and so is its value",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static int h(long x) { 0 }
                        static int h(int x) { 1 }
                        @Ensures({ result == 0 })
                        static int g() { h(1) }
                    }''')],

        // Before: verified — h(long)'s @Ensures was assumed for a call of h(int).
        [group: "P365 soundness sweep", name: "… and its @Ensures",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        @Ensures({ result == 0 }) static int h(long x) { 0 }
                        @Ensures({ result == 1 }) static int h(int x) { 1 }
                        @Ensures({ result == 0 })
                        static int g() { h(1) }
                    }''')],

        // Before: refuted — over-strict, h(long)'s result == 0 was assumed.
        [group: "P365 soundness sweep", name: "… which proves what the chosen overload ensures", ok: true,
         src: tc('''final class A {
                        @Ensures({ result == 0 }) static int h(long x) { 0 }
                        @Ensures({ result == 1 }) static int h(int x) { 1 }
                        @Ensures({ result == 1 })
                        static int g() { h(1) }
                    }''')],

        // Before: verified — h(Object)'s declared @Modifies({ [] }) framed a call of h(int[]).
        [group: "P365 soundness sweep", name: "… and its @Modifies",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        @Modifies({ [] }) static void h(Object o) { }
                        @Modifies({ a }) static void h(int[] a) { a[0] = 1 }
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) { h(a) }
                    }''')],

        // Before: verified — the same on another class's instance method.
        [group: "P365 soundness sweep", name: "an overload on a receiver of another class",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        @Requires({ c != null && a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(C c, int[] a) { c.h(a) }
                    }
                    final class C { void h(Object o) { } ; void h(int[] a) { a[0] = 1 } }''')],

        // Before: verified — C's write to A.n was recorded as C's own `n`, dropped as no location of the caller's.
        [group: "P365 soundness sweep", name: "another class writing the caller's static",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static int n
                        @Requires({ n == 7 })
                        @Ensures({ n == 7 })
                        static void g() { C.s() }
                    }
                    final class C { static void s() { A.n = 1 } }''')],

        // Before: verified — through an instance receiver too.
        [group: "P365 soundness sweep", name: "… through an instance method",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static int n
                        @Requires({ c != null && n == 7 })
                        @Ensures({ n == 7 })
                        static void g(C c) { c.w() }
                    }
                    final class C { void w() { A.n = 1 } }''')],

        // Before: verified — and through a call on to A's own setter, recorded as `A$n` and dropped from C's frame.
        [group: "P365 soundness sweep", name: "… or a call back into the caller's class",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static int n
                        static void setN(int v) { n = v }
                        @Requires({ n == 7 })
                        @Ensures({ n == 7 })
                        static void g() { C.s() }
                    }
                    final class C { static void s() { A.setN(1) } }''')],

        // Before: verified — a static nested class's bare `n = 1` (the outer class's static) read as a local of the nested class.
        [group: "P365 soundness sweep", name: "a nested class writing its outer class's static",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static int n
                        static final class In { static void w() { n = 1 } }
                        @Requires({ n == 7 })
                        @Ensures({ n == 7 })
                        static void g() { In.w() }
                    }''')],

        // Before: verified — a superclass method writing the static its subclass inherits was framed as the receiver's field `c$k`.
        [group: "P365 soundness sweep", name: "a superclass's write to the static a subclass caller inherits",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class D extends C {
                        @Requires({ c != null && k == 7 })
                        @Ensures({ k == 7 })
                        static void g(C c) { c.w() }
                    }
                    sealed class C permits D { static int k; final void w() { k = 1 } }''')],

        [group: "P365 soundness sweep", name: "… while another class's same-named static is still its own", ok: true,
         src: tc('''final class A {
                        static int k
                        @Requires({ k == 7 })
                        @Ensures({ k == 7 })
                        static void g() { C.s() }
                    }
                    final class C { static int k; static void s() { k = 1 } }''')],

        // Before: verified — an inner class's `n = 1` writes the enclosing instance's field, read as a local of the inner class.
        [group: "P365 soundness sweep", name: "an inner class writing its enclosing instance's field is loud",
         expect: "a field of A, which a frame of A.In can't name",
         src: tc('''final class A {
                        int n
                        final class In { void w() { n = 1 } }
                        @Requires({ n == 7 })
                        @Ensures({ n == 7 })
                        void g() { new In().w() }
                    }''')],

        // Before: verified — `A.this.n = 1` likewise.
        [group: "P365 soundness sweep", name: "… as is `A.this.n = …`",
         expect: "a field of the enclosing A instance",
         src: tc('''final class A {
                        int n
                        final class In { void w() { A.this.n = 1 } }
                        @Requires({ i != null && n == 7 })
                        @Ensures({ n == 7 })
                        void g(In i) { i.w() }
                    }''')],

        // Before: verified — a written formal handed `this` havocked a variable named `this`, leaving the caller's fields framed.
        [group: "P365 soundness sweep", name: "a callee writing the `this` it is handed is loud",
         expect: "which is passed 'this'",
         src: tc('''final class A {
                        int n
                        @Requires({ c != null && n == 7 })
                        @Ensures({ n == 7 })
                        void g(C c) { c.w(this) }
                    }
                    final class C { void w(A a) { a.n = 1 } }''')],

        // Before: verified — an unknown call was read as writing its receiver only: `nextBytes` fills `b`.
        [group: "P365 soundness sweep", name: "a library call filling its argument writes it",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static void h(byte[] b) { new Random().nextBytes(b) }
                        @Requires({ a != null && a.length == 2 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(byte[] a) { h(a) }
                    }''')],

        // Before: verified.
        [group: "P365 soundness sweep", name: "… `getChars` into a buffer",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static void h(char[] b) { 'xy'.getChars(0, 2, b, 0) }
                        @Requires({ a != null && a.length == 2 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(char[] a) { h(a) }
                    }''')],

        // Before: verified.
        [group: "P365 soundness sweep", name: "… `read` into a buffer",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static void h(char[] b) { new StringReader('xy').read(b) }
                        @Requires({ a != null && a.length == 2 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(char[] a) { h(a) }
                    }''')],

        // Before: verified — toArray was on the pure-read list whatever its arguments.
        [group: "P365 soundness sweep", name: "… `toArray` into an array, a read name whose collector overload writes",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static void h(Integer[] b) { [1, 2].toArray(b) }
                        @Requires({ a != null && a.length == 2 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(Integer[] a) { h(a) }
                    }''')],

        // Before: verified.
        [group: "P365 soundness sweep", name: "… a Consumer handed it",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static void h(int[] b) { java.util.function.Consumer<int[]> f = { int[] x -> x[0] = 1 } as java.util.function.Consumer<int[]>; f.accept(b) }
                        @Requires({ a != null && a.length == 2 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) { h(a) }
                    }''')],

        // Before: verified — a closure field called by name (`k(b)`) counted only the writes of its definition, not to `b`.
        [group: "P365 soundness sweep", name: "a callable called with an argument may write it",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static Closure k = { int[] b -> b[0] = 1 }
                        static void h(int[] b) { k(b) }
                        @Requires({ a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(int[] a) { h(a) }
                    }''')],

        // Before: verified — collect is a read; its collector overload isn't.
        [group: "P365 soundness sweep", name: "`collect(dst) { … }` fills and resizes `dst`",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static void h(List<Integer> src, List<Integer> dst) { src.collect(dst) { it } }
                        @Requires({ s != null && d != null && d.size() == 0 })
                        @Ensures({ d.size() == 0 })
                        static void g(List<Integer> s, List<Integer> d) { h(s, d) }
                    }''')],

        // Before: verified.
        [group: "P365 soundness sweep", name: "… `collectEntries(map) { … }`",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static void h(List<Integer> src, Map<Integer,Integer> dst) { src.collectEntries(dst) { [it, it] } }
                        @Requires({ s != null && d != null && d.size() == 0 })
                        @Ensures({ d.size() == 0 })
                        static void g(List<Integer> s, Map<Integer,Integer> d) { h(s, d) }
                    }''')],

        // Before: verified — `drainTo(ys)` writes and resizes its argument.
        [group: "P365 soundness sweep", name: "… `drainTo(ys)`",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static void h(java.util.concurrent.BlockingQueue<Integer> q, List<Integer> ys) { q.drainTo(ys) }
                        @Requires({ q != null && xs != null && xs.size() == 0 })
                        @Ensures({ xs.size() == 0 })
                        static void g(java.util.concurrent.BlockingQueue<Integer> q, List<Integer> xs) { h(q, xs) }
                    }''')],

        [group: "P365 soundness sweep", name: "… while plain `collect { … }` is still a read", ok: true,
         src: tc('''final class A {
                        @Requires({ src != null })
                        static int h(List<Integer> src, List<Integer> dst) { src.collect { it }.size() }
                        @Requires({ s != null && d != null && d.size() == 0 })
                        @Ensures({ d.size() == 0 })
                        static void g(List<Integer> s, List<Integer> d) { h(s, d) }
                    }''')],

        [group: "P365 soundness sweep", name: "… and an immutable argument isn't written", ok: true,
         src: tc('''final class A {
                        @Requires({ sb != null && b != null })
                        static void h(StringBuilder sb, int[] b) { sb.append(b.length) }
                        @Requires({ sb != null && a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(StringBuilder sb, int[] a) { h(sb, a) }
                    }''')],
    ]
}
