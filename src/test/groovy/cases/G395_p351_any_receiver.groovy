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
 * 'P351 a call through any receiver lands on that receiver' — the call framing read a callee's fields as the CALLER's
 * same-named locations whenever the receiver wasn't an object parameter (Phase 350). That is right only for `this`.
 * The probe found it proving false claims through an object field, a local alias of a parameter, a parameter of the
 * caller's own class, and another class's static. Now an object field of another class is a receiver like a
 * parameter, a local declared from a modelled receiver (and never reassigned) IS that receiver, any other explicit
 * receiver whose callee writes or reads its fields is loud, a foreign static's own statics are no location of the
 * caller's, a receiver of another class resolves on that class first, and the write collector follows a local that
 * holds a parameter or field.
 */
class G395_p351_any_receiver {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 351 a call through any receiver lands on that receiver: an object field of another class is framed like an object parameter (`c$count`), a local declared from a modelled receiver and never reassigned is that receiver (calls and reads), `this.c.incr()` is `c`; any other explicit receiver (a parameter of the caller class, which may be `this`; a fresh object; a reassigned field) whose callee writes or reads its fields skips loudly; a static on another class writes its own statics, not the caller ones; a receiver of another class resolves on that class before the caller same-named method; and a helper that aliases a parameter (`int[] b = a; b[0] = 5`) writes it. Fixed (unsound before): each of those shapes framed or assumed the callee fields as the caller same-named ones, proving false postconditions.'

    static final List<Map> CASES = [

        // An object FIELD of another class is a receiver like an object parameter (`c$count`). Before, `c.count` in a
        // contract was outside the fragment.
        [group: 'P351 a call through any receiver lands on that receiver', name: 'a call on an object field havocs the field object\'s state', expect: ["Cannot prove postcondition of f", "c.count (after a call) = 4"],
         src: tc('''final class A {
                        Counter c = new Counter()
                        @Requires({ c != null && c.count == 3 })
                        @Ensures({ result == 3 })
                        int f() { c.incr(); return c.count }
                    }
                    final class Counter { int count = 0; void incr() { count = count + 1 } }''')],
        [group: 'P351 a call through any receiver lands on that receiver', name: '… and the callee\'s @Ensures reaches the caller', ok: true,
         src: tc('''final class A {
                        Counter c = new Counter()
                        @Requires({ c != null && c.count == 3 })
                        @Ensures({ result == 4 })
                        int f() { c.incr(); return c.count }
                    }
                    final class Counter {
                        int count = 0
                        @Ensures({ count == old.count + 1 })
                        void incr() { count = count + 1 }
                    }''')],
        // Fixed (unsound before): the callee's `hits == old.hits + 1` was asserted about A's own `hits`, so f verified.
        [group: 'P351 a call through any receiver lands on that receiver', name: 'a field call\'s @Ensures no longer lands on the caller\'s same-named field', expect: "Cannot prove postcondition of f",
         src: tc('''final class A {
                        int hits = 0
                        Counter c = new Counter()
                        @Requires({ c != null })
                        @Ensures({ hits == old.hits + 1 })
                        void f() { c.incr() }
                    }
                    final class Counter {
                        int hits = 0
                        @Ensures({ hits == old.hits + 1 })
                        void incr() { hits = hits + 1 }
                    }''')],
        [group: 'P351 a call through any receiver lands on that receiver', name: '`this.c.incr()` is the same receiver', expect: ["Cannot prove postcondition of f", "c.count (after a call) = 4"],
         src: tc('''final class A {
                        Counter c = new Counter()
                        @Requires({ c != null && c.count == 3 })
                        @Ensures({ result == 3 })
                        int f() { this.c.incr(); return c.count }
                    }
                    final class Counter { int count = 0; void incr() { count = count + 1 } }''')],
        [group: 'P351 a call through any receiver lands on that receiver', name: 'a field the method reassigns is not modelled, and the call through it is loud', expect: "call 'c.incr(…)' writes its receiver's field 'count', but 'c' isn't a receiver the verifier models",
         src: tc('''final class A {
                        Counter c = new Counter()
                        @Requires({ c != null && o != null })
                        @Ensures({ result == 0 })
                        int f(Counter o) { c = o; c.incr(); return 0 }
                    }
                    final class Counter { int count = 0; void incr() { count = count + 1 } }''')],
        [group: 'P351 a call through any receiver lands on that receiver', name: 'a field and a parameter of the same class may alias: the Phase 194 boundary', expect: "call through 'c' — parameter 'o' of the same class may alias the receiver",
         src: tc('''final class A {
                        Counter c = new Counter()
                        @Requires({ c != null && o != null && o.count == 3 })
                        @Ensures({ result == 3 })
                        int f(Counter o) { c.incr(); return o.count }
                    }
                    final class Counter { int count = 0; void incr() { count = count + 1 } }''')],
        // Fixed (unsound before): `d` is `c`, but the call through it havoced the caller's `count` (none here) and left
        // `c$count` at 3, so f verified. A local declared from a modelled receiver and never reassigned IS that receiver.
        [group: 'P351 a call through any receiver lands on that receiver', name: 'a local alias of a parameter: a value call', expect: ["Cannot prove postcondition of f", "c.count (after a call) = 4"], refute: 'c = 0',
         src: tc('''final class A {
                        @Requires({ c != null && c.count == 3 })
                        @Ensures({ result == 3 })
                        static int f(Counter c) { Counter d = c; int x = d.bump(); return c.count }
                    }
                    final class Counter { int count = 0; int bump() { count = count + 1; return count } }''')],
        [group: 'P351 a call through any receiver lands on that receiver', name: '… a statement call', expect: ["Cannot prove postcondition of f", "c.count (after a call) = 4"],
         src: tc('''final class A {
                        @Requires({ c != null && c.count == 3 })
                        @Ensures({ result == 3 })
                        static int f(Counter c) { Counter d = c; d.incr(); return c.count }
                    }
                    final class Counter { int count = 0; void incr() { count = count + 1 } }''')],
        [group: 'P351 a call through any receiver lands on that receiver', name: '… with the callee\'s @Ensures off the caller\'s same-named field', expect: "Cannot prove postcondition of f",
         src: tc('''final class A {
                        int hits = 0
                        @Requires({ c != null })
                        @Ensures({ hits == old.hits + 1 })
                        void f(Counter c) { Counter d = c; d.incr() }
                    }
                    final class Counter {
                        int hits = 0
                        @Ensures({ hits == old.hits + 1 })
                        void incr() { hits = hits + 1 }
                    }''')],
        // Before: `d.count` was outside the fragment.
        [group: 'P351 a call through any receiver lands on that receiver', name: '… and a read through it is the receiver\'s field', ok: true,
         src: tc('''final class A {
                        @Requires({ c != null && c.count == 3 })
                        @Ensures({ result == 3 })
                        static int f(Counter c) { Counter d = c; return d.count }
                    }
                    final class Counter { int count = 0 }''')],
        // Fixed (unsound before): `o.incr()` framed and assumed `count == old.count + 1` about `this.count`, so f verified
        // (false for any `o` that isn't `this`).
        [group: 'P351 a call through any receiver lands on that receiver', name: 'a parameter of the caller\'s own class may be `this`: loud', expect: "call 'o.incr(…)' writes its receiver's field 'count', but 'o' isn't a receiver the verifier models",
         src: tc('''final class A {
                        int count = 0
                        @Ensures({ count == old.count + 1 })
                        void incr() { count = count + 1 }
                        @Requires({ o != null })
                        @Ensures({ count == old.count + 1 })
                        void f(A o) { o.incr() }
                    }''')],
        [group: 'P351 a call through any receiver lands on that receiver', name: 'a fresh object as the receiver of a writer: loud', expect: "call 'new Counter().incr(…)' writes its receiver's field 'count'",
         src: tc('''final class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int f(int n) { new Counter().incr(); return n }
                    }
                    final class Counter { int count = 0; void incr() { count = count + 1 } }''')],
        // Before: `c.incr()` resolved to A's own `incr` (the caller's final class was searched first): A's `count` was havoced
        // and Counter's @Ensures never assumed.
        [group: 'P351 a call through any receiver lands on that receiver', name: 'a receiver of another class resolves on that class, not on the caller\'s same-named method', ok: true,
         src: tc('''final class A {
                        int count = 0
                        void incr() { count = count + 2 }
                        @Requires({ c != null && c.count == 3 && count == 0 })
                        @Ensures({ result == 4 && count == 0 })
                        int f(Counter c) { c.incr(); return c.count }
                    }
                    final class Counter {
                        int count = 0
                        @Ensures({ count == old.count + 1 })
                        void incr() { count = count + 1 }
                    }''')],
        // Before: Util's `total` was framed as A's `total`, havoced, and `total == 0` refuted.
        [group: 'P351 a call through any receiver lands on that receiver', name: 'a static on another class writes its own statics, not the caller\'s', ok: true,
         src: tc('''class A {
                        static int total = 0
                        @Requires({ total == 0 })
                        @Ensures({ total == 0 })
                        static void f() { Util.set7() }
                    }
                    class Util {
                        static int total = 0
                        static void set7() { total = 7 }
                    }''')],
        // Fixed (unsound before): Util's `total == 7` was assumed about A's `total`, so f verified.
        [group: 'P351 a call through any receiver lands on that receiver', name: '… and an @Ensures over them is loud', expect: "call 'Util.set7(…)' has an @Ensures over its class's field 'total', which the caller can't name",
         src: tc('''class A {
                        static int total = 0
                        @Ensures({ total == 7 })
                        static void f() { Util.set7() }
                    }
                    class Util {
                        static int total = 0
                        @Ensures({ total == 7 })
                        static void set7() { total = 7 }
                    }''')],
        // Fixed (unsound before, the collector's recorded blind spot): `b[0] = 5` was a write to a local, so put0's frame
        // was empty and f verified. A local assigned a parameter or field now writes it.
        [group: 'P351 a call through any receiver lands on that receiver', name: 'a helper aliasing its array parameter writes it', expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        static void put0(int[] a) { int[] b = a; if (b.length > 0) b[0] = 5 }
                        @Requires({ a.length > 0 && a[0] == 0 })
                        @Ensures({ a[0] == 0 })
                        static int f(int[] a) { put0(a); return 0 }
                    }''')],
        [group: 'P351 a call through any receiver lands on that receiver', name: 'a helper aliasing its object parameter writes it', expect: ["Cannot prove postcondition of f", "c.count (after a call) = 4"],
         src: tc('''final class A {
                        @Requires({ c != null })
                        static void twice(Counter c) { Counter d = c; d.incr() }
                        @Requires({ c != null && c.count == 3 })
                        @Ensures({ result == 3 })
                        static int f(Counter c) { twice(c); return c.count }
                    }
                    final class Counter { int count = 0; void incr() { count = count + 1 } }''')],
        // `int n = x` copies a value: an int parameter is no reference, so `n = n + 1` writes nothing of the caller's.
        [group: 'P351 a call through any receiver lands on that receiver', name: 'a helper copying a value, not a reference, writes nothing', ok: true,
         src: tc('''class A {
                        static int inc(int x) { int n = x; n = n + 1; return n }
                        @Requires({ k == 5 })
                        @Ensures({ result == 5 })
                        static int f(int k) { int r = inc(k); return k }
                    }''')],
        // Before: `x = x + 1` put `x` in the frame, so the caller's `k` was havoced at the call (imprecise, not unsound).
        [group: 'P351 a call through any receiver lands on that receiver', name: 'a helper reassigning its int parameter leaves the caller\'s argument alone', ok: true,
         src: tc('''class A {
                        static int inc(int x) { x = x + 1; return x }
                        @Requires({ k == 5 })
                        @Ensures({ result == 5 })
                        static int f(int k) { int r = inc(k); return k }
                    }''')],
    ]
}
