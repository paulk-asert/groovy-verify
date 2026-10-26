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
 * 'P431 object boolean field' — an object parameter's field was always an Int (`c$on`), so a boolean one skipped the
 * method: `internal: Cannot cast object 'c$on' with class 'com.microsoft.z3.IntExpr' to class 'com.microsoft.z3.BoolExpr'`.
 * Found writing Phase 430's cases. A boolean field of an object parameter is a Bool now, read, written and assumed as
 * one, shown as `c.on = false` and built into the failing call as `new C(on: false)`.
 */
class G473_p431_object_boolean_field {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 431: an object parameter's boolean field (`c.on`) is modelled as a boolean, where it skipped the method with an internal sort error; a failure shows it as `c.on = false` and calls `f(new C(on: false))`."

    static final List<Map> CASES = [

        // It skipped: "internal: Cannot cast object 'c$on' … IntExpr to … BoolExpr"
        [group: "P431 object boolean field", name: "a boolean field read proves",
         ok: true,
         src: tc('''class A {
                        @Requires({ c != null && c.on })
                        @Ensures({ result > 0 })
                        static int f(C c) { return c.on ? 1 : 0 }
                    }
                    final class C { boolean on; int n }''')],

        [group: "P431 object boolean field", name: "… and refutes, the field false",
         expect: ["Cannot prove postcondition of f", "c.on = false", "fails on: f(new C(on: false"],
         refute: ["internal:", "c.on = 0"],
         src: tc('''class A {
                        @Requires({ c != null })
                        @Ensures({ result > 0 })
                        static int f(C c) { return c.on ? 1 : 0 }
                    }
                    final class C { boolean on; int n }''')],

        [group: "P431 object boolean field", name: "a class invariant over the boolean field is assumed",
         ok: true,
         src: tc('''class A {
                        @Requires({ c != null && c.on })
                        @Ensures({ result > 0 })
                        static int f(C c) { return c.n }
                    }
                    @Invariant({ !on || n > 0 })
                    final class C { boolean on; int n }''')],

        [group: "P431 object boolean field", name: "a boolean field mixed with ints in one condition",
         expect: ["Cannot prove postcondition of f", "fails on: f(new C("],
         refute: "internal:",
         src: tc('''class A {
                        @Requires({ c != null })
                        @Ensures({ result >= 0 })
                        static int f(C c) { return c.on && c.n > 0 ? c.n : c.n - 1 }
                    }
                    final class C { boolean on; int n }''')],

        [group: "P431 object boolean field", name: "through a call's @Ensures",
         ok: true,
         src: tc('''class A {
                        @Requires({ c != null })
                        @Ensures({ result == c.on })
                        static boolean get(C c) { return c.on }
                        @Requires({ c != null && c.on })
                        @Ensures({ result })
                        static boolean f(C c) { return get(c) }
                    }
                    final class C { boolean on; int n }''')],

        // Two of a class: Phase 89's identity model is for Int fields; a boolean one stays per-name
        [group: "P431 object boolean field", name: "two parameters of the class",
         expect: ["Cannot prove postcondition of g", "a.on = false, b.on = false",
                  "fails on: g(new C(on: false), new C(on: false))"],
         src: tc('''class A {
                        @Requires({ a != null && b != null && a.on })
                        @Ensures({ result })
                        static boolean f(C a, C b) { return a.on || b.on }
                        @Requires({ a != null && b != null })
                        @Ensures({ result })
                        static boolean g(C a, C b) { return a.on || b.on }
                    }
                    final class C { boolean on; int n }''')],
    ]
}
