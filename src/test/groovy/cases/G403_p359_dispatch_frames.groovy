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
 * 'P359 a call is framed by what it may dispatch to' — a call's frame came from the method its receiver's declared
 * type names: a library read by its name (Phase 358 refused it only when the declared type itself was a source
 * class), or a source method's own body (Phases 347/350). A virtual call runs the receiver's runtime override, so a
 * `Comparable<Box>` parameter holding a Box whose compareTo writes, or a `Base` holding a `Sub` whose get() writes,
 * verified a caller's false claim that the field was unchanged. The world is closed over the compilation unit: a
 * call's frame now unions in every override a class of the unit declares for it, formals mapped by position, and
 * an override whose writes can't be bounded leaves the call unmodelled, loudly. And a same-class instance helper
 * that a subclass overrides was inlined as its call's value (Phase 8a) from the base body: it is no function now.
 */
class G403_p359_dispatch_frames {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 359 a call is framed by what it may dispatch to: a call on a receiver declared as a library interface or a source superclass takes in the frames of every override a class of the compilation unit declares, in a helper\'s inferred frame, a loop\'s write set and at the call site, with an override\'s parameters mapped by position; an override whose writes can\'t be bounded is loud. Fixed: a `Comparable` or base-class parameter holding a subclass whose override writes a field verified a false claim that the field was unchanged, and an overridden same-class helper was inlined as its call\'s value from the base body.'

    static final List<Map> CASES = [

        // Before: compiled cleanly — `compareTo` on a Comparable was the library's read.
        [group: "P359 a call is framed by what it may dispatch to", name: "a Comparable holding a class whose compareTo writes", expect: "Cannot prove postcondition of g",
         src: tc('''class A {
                        static int cmp(Comparable<Box> c, Box o) { c == null ? 0 : c.compareTo(o) }
                        @Requires({ b != null && b.n == 0 })
                        @Ensures({ b.n == 0 })
                        static void g(Box b) { cmp(b, b) }
                    }
                    class Box implements Comparable<Box> { int n; int compareTo(Box o) { n = 1; return 0 } }''')],
        // Before: compiled cleanly — the helper's frame came from Base.get(), which writes nothing.
        [group: "P359 a call is framed by what it may dispatch to", name: "a base-class parameter holding a subclass that writes", expect: "Cannot prove postcondition of g",
         src: tc('''class A {
                        static int peek(Base h) { h == null ? 0 : h.get() }
                        @Requires({ s != null && s.n == 0 })
                        @Ensures({ s.n == 0 })
                        static void g(Sub s) { peek(s) }
                    }
                    class Base { int get() { 0 } }
                    class Sub extends Base { int n; int get() { n = n + 1; return n } }''')],
        // Before: compiled cleanly.
        [group: "P359 a call is framed by what it may dispatch to", name: "… through a same-class call in the base", expect: "Cannot prove postcondition of g",
         src: tc('''class A {
                        static int peek(Base h) { h == null ? 0 : h.twice() }
                        @Requires({ s != null && s.n == 0 })
                        @Ensures({ s.n == 0 })
                        static void g(Sub s) { peek(s) }
                    }
                    class Base { int get() { 0 }; int twice() { get() + get() } }
                    class Sub extends Base { int n; int get() { n = n + 1; return n } }''')],
        // Before: compiled cleanly — the caller's own call was framed by Base.get() alone.
        [group: "P359 a call is framed by what it may dispatch to", name: "a call on a base-class parameter in the caller", expect: "Cannot prove postcondition of g",
         src: tc('''class A {
                        @Requires({ h != null && h.n == 0 })
                        @Ensures({ h.n == 0 })
                        static void g(Base h) { h.get() }
                    }
                    class Base { int n; int get() { n } }
                    class Sub extends Base { int get() { n = n + 1; return n } }''')],
        // Before: compiled cleanly — and the override's parameter is named differently, so it maps by position.
        [group: "P359 a call is framed by what it may dispatch to", name: "an override writing its parameter", expect: "Cannot prove postcondition of g",
         src: tc('''class A {
                        @Requires({ h != null && a.length > 0 && a[0] == 0 })
                        @Ensures({ a[0] == 0 })
                        static void g(Base h, int[] a) { h.put(a) }
                    }
                    class Base { void put(int[] a) { } }
                    class Sub extends Base { void put(int[] b) { if (b.length > 0) b[0] = 5 } }''')],
        [group: "P359 a call is framed by what it may dispatch to", name: "an override whose writes can't be bounded is loud",
         expect: "may dispatch to Sub.get(…), whose writes can't be bounded from its body",
         src: tc('''class A {
                        @Requires({ h != null && h.n == 0 })
                        @Ensures({ h.n == 0 })
                        static void g(Base h) { h.get() }
                    }
                    class Base { int n; int get() { n } }
                    class Sub extends Base { int get() { System.gc(); return n } }''')],
        [group: "P359 a call is framed by what it may dispatch to", name: "an override that only reads keeps the frame", ok: true,
         src: tc('''class A {
                        static int peek(Base h) { h == null ? 0 : h.get() }
                        @Requires({ s != null && s.n == 0 })
                        @Ensures({ s.n == 0 })
                        static void g(Sub s) { peek(s) }
                    }
                    class Base { int get() { 0 } }
                    class Sub extends Base { int n; int get() { n } }''')],
        [group: "P359 a call is framed by what it may dispatch to", name: "… as does a Comparable whose compareTo only reads", ok: true,
         src: tc('''class A {
                        static int cmp(Comparable<Box> c, Box o) { c == null || o == null ? 0 : c.compareTo(o) }
                        @Requires({ b != null && b.n == 0 })
                        @Ensures({ b.n == 0 })
                        static void g(Box b, Box o) { cmp(o, b) }
                    }
                    class Box implements Comparable<Box> { int n; int compareTo(Box o) { n - o.n } }''')],
        // Before: compiled cleanly — Base.get()'s body was inlined as the call's value (Phase 8a), though a Sub
        // receiver runs Sub.get(), which returns 1.
        [group: "P359 a call is framed by what it may dispatch to", name: "an overridden helper's body is not its value", expect: "Cannot prove postcondition of foo",
         src: tc('''class Base {
                        int get() { 0 }
                        @Ensures({ result == 0 })
                        int foo() { get() }
                    }
                    class Sub extends Base { int get() { 1 } }''')],
        [group: "P359 a call is framed by what it may dispatch to", name: "… while one no class overrides still is", ok: true,
         src: tc('''class Base {
                        int get() { 0 }
                        @Ensures({ result == 0 })
                        int foo() { get() }
                    }''')],
    ]
}
