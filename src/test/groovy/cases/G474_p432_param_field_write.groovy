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
 * 'P432 field write through a parameter' — `c.n = 1` through a lone object parameter skipped the postcondition path
 * (`field write 'c.n = 1' is outside fragment`): only Phase 89's two-of-a-class identity map took a field write. A
 * primitive int or boolean field written through the parameter (or a local alias of it) now holds the value, read back
 * by a later `c.n` and by the postcondition. Callers already saw the write: the frame records a write through `c`
 * (Phase 357), and the caller havocs `c.n` at the call — shown now as `c.n (after a call)`, not the encoder's `c$n`.
 *
 * Declined, loudly with the reason: a class whose setter may not be the field (Phase 361). A class with an `@Invariant`
 * was declined too until Phase 433, which re-proves it at the exit.
 */
class G474_p432_param_field_write {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 432: a write through an object parameter (`c.n = 1`, `c.on = true`, or through a local alias) to a primitive int or boolean field is modelled on the postcondition path, where it skipped; a class with an @Invariant or an overridable setter is declined with the reason, and a call's framed field shows as `c.n (after a call)`."

    static final List<Map> CASES = [

        // Each skipped: "field write 'c.n = 1' is outside fragment"
        [group: "P432 field write through a parameter", name: "an int and a boolean field written",
         ok: true,
         src: tc('''class A {
                        @Requires({ c != null })
                        @Ensures({ c.n == 1 && c.on })
                        static void f(C c) { c.n = 1; c.on = true }
                        @Requires({ c != null && p > 0 })
                        @Ensures({ result > 0 })
                        static int h(C c, int p) { c.n = p; return c.n }
                        @Requires({ c != null })
                        @Ensures({ c.n == 5 })
                        static void k(C c) { C d = c; d.n = 5 }
                    }
                    final class C { boolean on; int n }''')],

        [group: "P432 field write through a parameter", name: "… and a wrong claim about it refutes",
         expect: ["Cannot prove postcondition of g", "ensured: (c.n == 2)", "fails on: g(new C())"],
         src: tc('''class A {
                        @Requires({ c != null })
                        @Ensures({ c.n == 2 })
                        static void g(C c) { c.n = 1 }
                    }
                    final class C { boolean on; int n }''')],

        // The callee's write reaches its caller through the frame; the havocked field is shown as written
        [group: "P432 field write through a parameter", name: "a caller sees the write",
         expect: ["Cannot prove postcondition of f", "ensured: (result == 0)", "c.n (after a call) = 1"],
         refute: ['c$n', "Cannot prove postcondition of g", "Cannot prove postcondition of set1"],
         src: tc('''class A {
                        @Requires({ c != null })
                        @Ensures({ c.n == 1 })
                        static void set1(C c) { c.n = 1 }
                        @Requires({ c != null && c.n == 0 })
                        @Ensures({ result == 0 })
                        static int f(C c) { set1(c); return c.n }
                        @Requires({ c != null })
                        @Ensures({ result == 1 })
                        static int g(C c) { set1(c); return c.n }
                    }
                    final class C { int n }''')],

        // Phase 433 — declined here at first; the invariant is re-proved at the exit now
        [group: "P432 field write through a parameter", name: "a class with an @Invariant is re-proved",
         ok: true,
         src: tc('''class A {
                        @Requires({ c != null })
                        @Ensures({ c.n == 1 })
                        static void f(C c) { c.n = 1 }
                    }
                    @Invariant({ n >= 0 })
                    final class C { int n }''')],

        [group: "P432 field write through a parameter", name: "an overridable setter is declined",
         expect: ["field write 'c.n = 1' is outside fragment — 'C' can be subclassed elsewhere", "setter 'setN'"],
         src: tc('''class A {
                        @Requires({ c != null })
                        @Ensures({ c.n == 1 })
                        static void f(C c) { c.n = 1 }
                    }
                    class C { int n }''')],
    ]
}
