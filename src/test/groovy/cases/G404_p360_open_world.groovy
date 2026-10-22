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
 * 'P360 an overridable body is no contract' — a contract-free method's body was read as its call's frame (Phase 347)
 * and, when it wrote nothing, as its value (Phase 8a). Phase 359 took in the overrides a class of the compilation
 * unit declares, but a subclass compiled elsewhere — an app extending a verified library class — can override the
 * method unseen, and Groovy classes and methods are open by default. Now the verifier trusts a body only where it
 * can't be overridden: a static, private or final method, or a method of a final class, an enum, a record, or a
 * sealed hierarchy whose permitted subclasses are closed. Elsewhere the call's frame is unknown — loud, naming the
 * method — and its value is opaque. A declared @Modifies (and @Ensures, for a value) is what an override is held to,
 * so it restores the call.
 */
class G404_p360_open_world {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 360 an overridable body is no contract: a contract-free instance method that a subclass compiled elsewhere could override has neither its frame nor its value read off its body; a static, private or final method, a final class, an enum, a record or a closed sealed hierarchy is trusted, and a declared @Modifies (with @Ensures for a value) restores the call.'

    static final List<Map> CASES = [

        // Before: verified — Counter.incr()'s body {count} framed the call, though an app's subclass may override it.
        // (The claim is about an array: a caller reading the open class's own fields meets Phase 361's getter rule first.)
        [group: "P360 an overridable body is no contract", name: "an open class's writer leaves the call unmodelled, loudly",
         expect: "'Counter.incr(…)' can be overridden by a subclass compiled elsewhere, so its body isn't its frame",
         src: tc('''final class A {
                        @Requires({ c != null && a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(Counter c, int[] a) { c.incr() }
                    }
                    class Counter { int count; int total; void incr() { count = count + 1 } }''')],
        [group: "P360 an overridable body is no contract", name: "… while a final class is trusted", ok: true,
         src: tc('''final class A {
                        @Requires({ c != null && a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(Counter c, int[] a) { c.incr() }
                    }
                    final class Counter { int count; int total; void incr() { count = count + 1 } }''')],
        [group: "P360 an overridable body is no contract", name: "… and so is a final method", ok: true,
         src: tc('''final class A {
                        @Requires({ c != null && a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(Counter c, int[] a) { c.incr() }
                    }
                    class Counter { int count; int total; final void incr() { count = count + 1 } }''')],
        [group: "P360 an overridable body is no contract", name: "… or a declared @Modifies, which an override is held to", ok: true,
         src: tc('''final class A {
                        @Requires({ c != null && a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(Counter c, int[] a) { c.incr() }
                    }
                    class Counter { int count; int total; @Modifies({ this.count }) void incr() { count = count + 1 } }''')],
        // Before: verified — Base.get()'s body was inlined as the value, though a subclass may return anything.
        [group: "P360 an overridable body is no contract", name: "an open helper's body is neither its frame nor its value",
         expect: "'Base.get(…)' can be overridden by a subclass compiled elsewhere",
         src: tc('''class Base {
                        int get() { 0 }
                        @Ensures({ result == 0 })
                        int foo() { get() }
                    }''')],
        [group: "P360 an overridable body is no contract", name: "… a private one is", ok: true,
         src: tc('''class Base {
                        private int get() { 0 }
                        @Ensures({ result == 0 })
                        int foo() { get() }
                    }''')],
        [group: "P360 an overridable body is no contract", name: "… and an open one's @Ensures and @Modifies restore the call", ok: true,
         src: tc('''class Base {
                        @Ensures({ result == 0 })
                        @Modifies({ [] })
                        int get() { 0 }
                        @Ensures({ result == 0 })
                        int foo() { get() }
                    }''')],
        [group: "P360 an overridable body is no contract", name: "a sealed hierarchy of final classes is closed", ok: true,
         src: tc('''final class A {
                        static int peek(Base h) { h == null ? 0 : h.get() }
                        @Requires({ s != null && s.n == 0 })
                        @Ensures({ s.n == 0 })
                        static void g(Sub s) { peek(s) }
                    }
                    sealed class Base { int get() { 0 } }
                    final class Sub extends Base { int n; int get() { n } }''')],
        // Before: compiled cleanly.
        [group: "P360 an overridable body is no contract", name: "… a non-sealed subclass reopens it",
         expect: "'Base.get(…)' can be overridden by a subclass compiled elsewhere",
         src: tc('''final class A {
                        static int peek(Base h) { h == null ? 0 : h.get() }
                        @Requires({ s != null && a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(Sub s, int[] a) { peek(s) }
                    }
                    sealed class Base { int get() { 0 } }
                    non-sealed class Sub extends Base { int n; int get() { n } }''')],
    ]
}
