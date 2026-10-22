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
 * 'P363 an override is held to its ancestor's skeleton' — slice 3a of the open-world plan. A precompiled ancestor's
 * skeleton — a relied one (`META-INF/groovy-verify/relied/<fqn>.groovy`, the shape Phase 362's reliances will be
 * written in) or a spec one (`specs/`, the JDK-specs dialect) — is now an ancestor declaration for contract
 * inheritance: an override compiled with the checker inherits its @Modifies (a @Pure one as `@Modifies({ [] })`),
 * frame-checked with the skeleton named, and its @Ensures, which the override must prove (a source ancestor's reach
 * it through groovy-contracts' own inheritance, as before). Found on the way, all silent before: a call to an
 * inherited PRECOMPILED method from a helper (implicitly or as `super.m(…)`) wrote nothing, a same-class instance
 * method named like a library mutator (`fill`) was read as writing its receiver `this` rather than by its body, and
 * a skeleton without imports said nothing.
 */
class G407_p363_override_skeletons {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 363 an override is held to its ancestor\'s skeleton: a precompiled supertype\'s relied or spec skeleton is inherited like a source ancestor\'s contract, so an override compiled with the checker is frame-checked against its @Modifies (or @Pure) and must prove its @Ensures. Fixed: a helper calling an inherited precompiled method (or `super.m(…)`) was read as writing nothing, a same-class method named like a library mutator lost its own frame, and a skeleton without imports was silently empty.'

    static final String RELIED_INCR = '''package fixture
                    class LibCounter { @Modifies({ this.count }) void incr() {} }'''

    static final List<Map> CASES = [

        [group: "P363 an override is held to its ancestor's skeleton", name: "an override writing outside a relied frame",
         expect: "Method 'incr' writes 'log', which is not in its @Modifies clause [count]. A method may modify only the locations it declares (@Modifies({ [] }) means none). The clause is inherited from the skeleton of fixture.LibCounter#incr, which this override is held to.",
         relied: ['fixture.LibCounter': RELIED_INCR],
         src: tc('''class Noisy extends fixture.LibCounter {
                        void incr() { log = log + 1; count = count + 1 }
                    }''')],
        [group: "P363 an override is held to its ancestor's skeleton", name: "… and one within it", ok: true,
         relied: ['fixture.LibCounter': RELIED_INCR],
         src: tc('''class Ok extends fixture.LibCounter {
                        void incr() { count = count + 2 }
                    }''')],
        [group: "P363 an override is held to its ancestor's skeleton", name: "a spec skeleton's @Pure is an empty frame",
         expect: "Method 'get' writes 'log', which is not in its @Modifies clause []",
         specs: ['fixture.LibCounter': '''package fixture
                    class LibCounter { @Pure int get() {} }'''],
         src: tc('''class Noisy extends fixture.LibCounter {
                        int get() { log = log + 1; return count }
                    }''')],
        [group: "P363 an override is held to its ancestor's skeleton", name: "an inherited @Ensures is proved on the override",
         expect: "Cannot prove postcondition of get",
         relied: ['fixture.LibCounter': '''package fixture
                    class LibCounter { @Ensures({ result == count }) @Modifies({ [] }) int get() {} }'''],
         src: tc('''class Offset extends fixture.LibCounter {
                        int get() { count + 100 }
                    }''')],
        [group: "P363 an override is held to its ancestor's skeleton", name: "… and one meeting it passes", ok: true,
         relied: ['fixture.LibCounter': '''package fixture
                    class LibCounter { @Ensures({ result == count }) @Modifies({ [] }) int get() {} }'''],
         src: tc('''class Same extends fixture.LibCounter {
                        int get() { count }
                    }''')],
        // Unchanged, for contrast: a SOURCE ancestor's contract reaches the implementer through groovy-contracts' own
        // inheritance (copied onto the method), so it was proved before; a skeleton's is now proved the same way.
        [group: "P363 an override is held to its ancestor's skeleton", name: "an implementer proves a source interface's @Ensures, as before",
         expect: "Cannot prove postcondition of f",
         src: tc('''final class C implements I { int f() { -1 } }
                    interface I {
                        @Ensures({ result >= 0 })
                        int f()
                    }''')],
        // Before: compiled cleanly — `fill` is on the mutator list, so the instance call `fill(a)` was read as writing
        // its receiver `this` (no caller-visible name, so dropped) rather than by fill's own frame.
        [group: "P363 an override is held to its ancestor's skeleton", name: "a same-class method named like a mutator is framed by its body",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        void fill(int[] a) { if (a != null && a.length > 0) a[0] = 9 }
                        void put(int[] a) { fill(a) }
                        @Requires({ a != null && a.length > 0 && a[0] == 0 })
                        @Ensures({ a[0] == 0 })
                        void g(int[] a) { put(a) }
                    }''')],
        // Before: compiled cleanly — the inherited precompiled `fill` has no body, read as writing nothing.
        [group: "P363 an override is held to its ancestor's skeleton", name: "a helper calling an inherited precompiled method is loud",
         expect: "'LibCounter.fill(…)' is compiled elsewhere, with no contract or skeleton giving its frame",
         src: tc('''final class A {
                        @Requires({ n != null && a != null && a.length > 0 && a[0] == 0 })
                        @Ensures({ a[0] == 0 })
                        static void g(Noisy n, int[] a) { n.wrap(a) }
                    }
                    final class Noisy extends fixture.LibCounter { void wrap(int[] a) { fill(a) } }''')],
        // Before: compiled cleanly — `super` was recorded as the written name, and dropped.
        [group: "P363 an override is held to its ancestor's skeleton", name: "… as is one through super",
         expect: "'LibCounter.fill(…)' is compiled elsewhere, with no contract or skeleton giving its frame",
         src: tc('''final class A {
                        @Requires({ n != null && a != null && a.length > 0 && a[0] == 0 })
                        @Ensures({ a[0] == 0 })
                        static void g(Noisy n, int[] a) { n.wrap(a) }
                    }
                    final class Noisy extends fixture.LibCounter { void wrap(int[] a) { super.fill(a) } }''')],
        [group: "P363 an override is held to its ancestor's skeleton", name: "… and a skeleton frames it", expect: "Cannot prove postcondition of g",
         relied: ['fixture.LibCounter': '''package fixture
                    class LibCounter { @Modifies({ a }) void fill(int[] a) {} }'''],
         src: tc('''final class A {
                        @Requires({ n != null && a != null && a.length > 0 && a[0] == 0 })
                        @Ensures({ a[0] == 0 })
                        static void g(Noisy n, int[] a) { n.wrap(a) }
                    }
                    final class Noisy extends fixture.LibCounter { void wrap(int[] a) { super.fill(a) } }''')],
        [group: "P363 an override is held to its ancestor's skeleton", name: "… exactly: an array it doesn't name stays framed", ok: true,
         relied: ['fixture.LibCounter': '''package fixture
                    class LibCounter { @Modifies({ a }) void fill(int[] a) {} }'''],
         src: tc('''final class A {
                        @Requires({ n != null && a != null && b != null && b.length > 0 && b[0] == 0 })
                        @Ensures({ b[0] == 0 })
                        static void g(Noisy n, int[] a, int[] b) { n.wrap(a) }
                    }
                    final class Noisy extends fixture.LibCounter { void wrap(int[] a) { super.fill(a) } }''')],
    ]
}
