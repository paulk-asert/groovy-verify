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
 * 'P350 a cross-class call is framed by its writes' — the last "still out" of Phase 347. A call on a class-typed
 * PARAMETER (`c.bump()`) resolved its callee on the receiver's class but framed it as if same-class: the callee's
 * fields were the caller's same-named ones (a wrong location, havoced; its @Ensures asserted about the wrong
 * variable) and the receiver's own `c$field` entities stayed at their entry values — a value call `int x = c.bump()`
 * verified `c.count == 3` past the increment. Now the callee's frame maps onto the receiver (`c$field`, Phase 45's
 * naming; a formal onto its actual), its @Ensures is assumed under the receiver context (bare `count` is `c$count`,
 * `old.count` the snapshot at the call), the receiver's class invariants are re-assumed, and the statement form goes
 * the same way (Phase 45's all-fields havoc is the fallback for a callee with no body). A same-class helper that
 * writes THROUGH an object parameter has it in its frame, and a written object parameter at a call site means its
 * fields. A contract-free static on a sibling class of the compilation unit unfolds as a function when its frame is
 * empty. The Phase 194 alias boundary stands.
 */
class G394_p350_cross_class {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 350 a cross-class call is framed by its writes: a call on a class-typed parameter (`c.bump()`, as a value or a statement) havocs exactly the receiver fields its callee writes (`c$count (after a call)`), binds the callee @Ensures under the receiver (bare `count` is `c$count`, `old.count` the snapshot at the call) and re-assumes the receiver class invariants; a same-class helper writing through an object parameter havocs its fields at the call; a contract-free static on a sibling class unfolds as a function when its frame is empty. Fixed (unsound before): a value call on an object parameter framed the callee fields as the caller same-named ones and left the receiver state stale, so `c.count == 3` verified past `c.bump()`; and the callee @Ensures was asserted about the caller variable. The Phase 194 alias boundary stands.'

    static final List<Map> CASES = [

        // Fixed (unsound before): `int x = c.bump()` routed through the generic call framing, which havoced the CALLER's
        // `count` (there is none here) and left `c.count` at its entry value, so `result == 3` verified.
        [group: 'P350 a cross-class call is framed by its writes', name: 'a value call on an object parameter havocs the fields its callee writes', expect: ["Cannot prove postcondition of f", "c\$count (after a call) = 4"],
         src: tc('''final class A {
                        @Requires({ c != null && c.count == 3 })
                        @Ensures({ result == 3 })
                        static int f(Counter c) { int x = c.bump(); return c.count }
                    }
                    final class Counter { int count = 0; int bump() { count = count + 1; return count } }''')],
        // Phase 45 havoced every field of the receiver; the callee's inferred frame says which (here the only one).
        [group: 'P350 a cross-class call is framed by its writes', name: 'a statement call does the same, by the callee\'s frame now', expect: ["Cannot prove postcondition of f", "c\$count (after a call) = 4"],
         src: tc('''final class A {
                        @Requires({ c != null && c.count == 3 })
                        @Ensures({ result == 3 })
                        static int f(Counter c) { c.incr(); return c.count }
                    }
                    final class Counter { int count = 0; void incr() { count = count + 1 } }''')],
        // Phase 45's recorded limit ("the callee's @Ensures is currently not assumed cross-class"): its bare `count` is
        // `c$count` and its `old.count` the snapshot at the call.
        [group: 'P350 a cross-class call is framed by its writes', name: 'the callee\'s @Ensures reaches the caller under the receiver', ok: true,
         src: tc('''final class A {
                        @Requires({ c != null && c.count == 3 })
                        @Ensures({ result == 4 })
                        static int f(Counter c) { c.incr(); return c.count }
                    }
                    final class Counter {
                        int count = 0
                        @Ensures({ count == old.count + 1 })
                        void incr() { count = count + 1 }
                    }''')],
        [group: 'P350 a cross-class call is framed by its writes', name: '… and a wrong claim against it refutes', expect: ["Cannot prove postcondition of f", "c\$count (after a call) = 4"],
         src: tc('''final class A {
                        @Requires({ c != null && c.count == 3 })
                        @Ensures({ result == 5 })
                        static int f(Counter c) { c.incr(); return c.count }
                    }
                    final class Counter {
                        int count = 0
                        @Ensures({ count == old.count + 1 })
                        void incr() { count = count + 1 }
                    }''')],
        // Before: the callee's `count` was framed as the caller's `count` (havoced, `count == 0` refuted).
        [group: 'P350 a cross-class call is framed by its writes', name: 'a same-named field of the caller is not the callee\'s', ok: true,
         src: tc('''final class A {
                        int count = 0
                        @Requires({ c != null && count == 0 })
                        @Ensures({ count == 0 })
                        int f(Counter c) { int x = c.bump(); return x }
                    }
                    final class Counter { int count = 0; int bump() { count = count + 1; return count } }''')],
        // Before: `count == old.count + 1` was asserted about the CALLER's `count` — a fact about the wrong variable.
        [group: 'P350 a cross-class call is framed by its writes', name: '… and the callee\'s @Ensures binds to the receiver, not to it', ok: true,
         src: tc('''final class A {
                        int count = 0
                        @Requires({ c != null && count == 0 && c.count == 0 })
                        @Ensures({ result == 1 && count == 0 })
                        int f(Counter c) { int x = c.bump(); return x }
                    }
                    final class Counter {
                        int count = 0
                        @Ensures({ result == old.count + 1 && count == old.count + 1 })
                        int bump() { count = count + 1; return count }
                    }''')],
        [group: 'P350 a cross-class call is framed by its writes', name: 'a getter\'s @Ensures reads the receiver\'s field', ok: true,
         src: tc('''final class A {
                        @Requires({ c != null && c.count == 3 })
                        @Ensures({ result == 3 })
                        static int f(Counter c) { int x = c.get(); return x }
                    }
                    final class Counter {
                        int count = 0
                        @Ensures({ result == count })
                        int get() { count }
                    }''')],
        [group: 'P350 a cross-class call is framed by its writes', name: 'a callee without @Ensures gives an opaque result', expect: "Cannot prove postcondition of f",
         src: tc('''final class A {
                        @Requires({ c != null && c.count == 3 })
                        @Ensures({ result == 4 })
                        static int f(Counter c) { int x = c.bump(); return x }
                    }
                    final class Counter { int count = 0; int bump() { count = count + 1; return count } }''')],
        // The callee preserved its final class invariant on exit (Phase 15); the caller may assume it over the havoced field.
        [group: 'P350 a cross-class call is framed by its writes', name: 'the receiver\'s class invariant is re-assumed after a contract-free writer', ok: true,
         src: tc('''final class A {
                        @Requires({ c != null })
                        @Ensures({ result >= 0 })
                        static int f(Counter c) { c.reset(); return c.count }
                    }
                    @Invariant({ count >= 0 })
                    final class Counter {
                        int count = 0
                        void reset() { count = 0 }
                    }''')],
        [group: 'P350 a cross-class call is framed by its writes', name: '… without the invariant the claim refutes', expect: ["Cannot prove postcondition of f", "c\$count (after a call) = -1"],
         src: tc('''final class A {
                        @Requires({ c != null })
                        @Ensures({ result >= 0 })
                        static int f(Counter c) { c.reset(); return c.count }
                    }
                    final class Counter {
                        int count = 0
                        void reset() { count = 0 }
                    }''')],
        // Phase 45 would have havoced `c.count` too (every field, whatever the callee did).
        [group: 'P350 a cross-class call is framed by its writes', name: 'a callee writing only its formal leaves the receiver alone', ok: true,
         src: tc('''final class A {
                        @Requires({ c != null && c.count == 3 && a.length > 0 })
                        @Ensures({ result == 3 })
                        static int f(Counter c, int[] a) { c.fill(a); return c.count }
                    }
                    final class Counter {
                        int count = 0
                        void fill(int[] a) { if (a.length > 0) a[0] = count }
                    }''')],
        [group: 'P350 a cross-class call is framed by its writes', name: 'a callee whose writes can\'t be bounded is loud', expect: ["call 'weird(…)' whose writes can't be bounded from its body: multiple assignment", "declare @Modifies on weird"],
         src: tc('''final class A {
                        @Requires({ c != null && c.count == 3 })
                        @Ensures({ result == 3 })
                        static int f(Counter c) { c.weird(); return c.count }
                    }
                    final class Counter {
                        int count = 0
                        void weird() { def (a, b) = [count, count]; count = a + b }
                    }''')],
        [group: 'P350 a cross-class call is framed by its writes', name: 'the Phase 194 alias boundary stands', expect: "call through 'c' — parameter 'd' of the same class may alias the receiver",
         src: tc('''final class A {
                        @Requires({ c != null && d != null && d.count == 3 })
                        @Ensures({ result == 3 })
                        static int f(Counter c, Counter d) { int x = c.bump(); return d.count }
                    }
                    final class Counter { int count = 0; int bump() { count = count + 1; return count } }''')],
        // The collector reads `c.incr()` by incr's frame: a written field is the receiver, so twice's frame is {c}, and a
        // written OBJECT parameter at the call site means its fields.
        [group: 'P350 a cross-class call is framed by its writes', name: 'a same-class helper writing through an object parameter havocs its fields', expect: ["Cannot prove postcondition of f", "c\$count (after a call) = 4"],
         src: tc('''final class A {
                        @Requires({ c != null })
                        static void twice(Counter c) { c.incr(); c.incr() }
                        @Requires({ c != null && c.count == 3 })
                        @Ensures({ result == 3 })
                        static int f(Counter c) { twice(c); return c.count }
                    }
                    final class Counter { int count = 0; void incr() { count = count + 1 } }''')],
        [group: 'P350 a cross-class call is framed by its writes', name: '… and one only reading it leaves them alone', ok: true,
         src: tc('''final class A {
                        @Requires({ c != null })
                        static int peek(Counter c) { c.get() }
                        @Requires({ c != null && c.count == 3 })
                        @Ensures({ result == 3 })
                        static int f(Counter c) { int x = peek(c); return c.count }
                    }
                    final class Counter { int count = 0; int get() { count } }''')],
        // Its body is in the compilation unit and its frame is empty, like a same-class helper (symbol `Util$tweak`).
        [group: 'P350 a cross-class call is framed by its writes', name: 'a contract-free static on a sibling class unfolds as a function', ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n + 1 })
                        static int f(int n) { Util.tweak(n) }
                    }
                    class Util { static int tweak(int x) { x + 1 } }''')],
        // A writer is not a function: its result is opaque (and `Util.total` is no location of the caller's).
        [group: 'P350 a cross-class call is framed by its writes', name: '… not when it writes its own class', expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n + 1 })
                        static int f(int n) { Util.tweak(n) }
                    }
                    class Util { static int total = 0; static int tweak(int x) { total = total + x; x + 1 } }''')],
        [group: 'P350 a cross-class call is framed by its writes', name: 'a sibling static that stores into an array argument', expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Requires({ a.length > 0 && a[0] == 0 })
                        @Ensures({ a[0] == 0 })
                        static int f(int[] a) { Util.put0(a, 1); return 0 }
                    }
                    class Util { static void put0(int[] a, int v) { if (a.length > 0) a[0] = v } }''')],
    ]
}
