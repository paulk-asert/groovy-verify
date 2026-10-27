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
 * 'P436 shared-class fields in the identity map' — two parameters of one class read an int field through Phase 89's
 * identity-keyed map; a boolean field was read by name (Phase 431), and its write through one of them declined (Phase
 * 434), since a by-name write misses the other when they are one object. A boolean field is a 0/1 cell of the map
 * now, read as `cell == 1`, so `a.on = true` reaches `b.on` when `a === b`.
 *
 * Fixed with it: a map cell isn't a model variable, so a counterexample never showed a field read through the map, and
 * the failing call built `new C()` without it — `intWit(new C(), new C())` for a method requiring `a.n == 5`, a call that
 * breaks its own precondition. Each field read or written shows its entry value (`a.n = 5`), and the call builds it.
 */
class G478_p436_shared_class_booleans {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 436: a boolean field of two parameters sharing a class is read and written through the identity map, so a write through one reaches the other when they are one object; and a field read through the map shows its entry value, so the failing call builds it (`f(new C(n: 5), new C())`)."

    static final List<Map> CASES = [

        // Declined in Phase 434
        [group: "P436 shared-class fields in the identity map", name: "a boolean field written and read",
         ok: true,
         src: tc('''class A {
                        @Requires({ a != null && b != null })
                        @Ensures({ a.on })
                        static void setOn(C a, C b) { a.on = true }
                        @Requires({ a != null && b != null && a.on })
                        @Ensures({ result == 1 })
                        static int rd(C a, C b) { return a.on ? 1 : 0 }
                        @Requires({ a != null && b != null && a === b })
                        @Ensures({ b.on })
                        static void through(C a, C b) { a.on = true }
                    }
                    final class C { int n; boolean on }''')],

        [group: "P436 shared-class fields in the identity map", name: "… and apart, the other keeps its value",
         ok: true,
         src: tc('''class A {
                        @Requires({ a != null && b != null && a !== b && !b.on })
                        @Ensures({ !b.on })
                        static void apart(C a, C b) { a.on = true }
                    }
                    final class C { int n; boolean on }''')],

        // It built `intWit(new C(), new C())`, which breaks `a.n == 5`
        [group: "P436 shared-class fields in the identity map", name: "an int field read through the map is in the call",
         expect: ["Cannot prove postcondition of intWit", "counterexample: a.n = 5", "fails on: intWit(new C(n: 5), new C())"],
         src: tc('''class A {
                        @Requires({ a != null && b != null && a.n == 5 })
                        @Ensures({ result == 0 })
                        static int intWit(C a, C b) { return a.n }
                    }
                    final class C { int n; boolean on }''')],

        [group: "P436 shared-class fields in the identity map", name: "… and a boolean field's",
         expect: ["Cannot prove postcondition of boolWit", "counterexample: a.on = true", "fails on: boolWit(new C(on: true), new C())"],
         src: tc('''class A {
                        @Requires({ a != null && b != null && a.on })
                        @Ensures({ result == 0 })
                        static int boolWit(C a, C b) { return a.on ? 1 : 0 }
                    }
                    final class C { int n; boolean on }''')],

        // An invariant over a boolean field, re-proved after a write through the map (Phase 434)
        [group: "P436 shared-class fields in the identity map", name: "a boolean field in the invariant",
         expect: ["Cannot prove class invariant of C holds for 'a' at exit of g", "fails on: g(new C(n: 0, on: false), new C("],
         src: tc('''class A {
                        @Requires({ a != null && b != null })
                        static void f(C a, C b) { a.n = 1; a.on = true }
                        @Requires({ a != null && b != null })
                        static void g(C a, C b) { a.on = true }
                    }
                    @Invariant({ !on || n > 0 })
                    final class C { int n; boolean on }''')],
    ]
}
