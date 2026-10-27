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
 * 'P434 writes through parameters of one class' — two parameters of one class read and write an int field through
 * Phase 89's identity-keyed map, so a write through `a` reaches `b` when they are one object. Phase 433 re-proved a
 * written parameter's class invariant only on the lone-parameter store; this store re-proves it too now.
 *
 * Fixed with it (unsound before, Phase 432): a boolean field written through such a parameter was bound by name, so
 * `a.on = true` left `b.on` false even when `a === b` and `!b.on` proved; and a write through a local alias of one
 * (`C d = a; d.n = 5`) bound a name its reads, through the map, never saw. The alias's write goes through the map now,
 * and a boolean's was declined (Phase 436 maps it too). The map store also checks the setter is the field (Phase 361), as the other did.
 *
 * A failure that needs the two to be one object said `a$id = 3, b$id = 3` and printed `same(new C(), new C())`, a
 * call that never fails: it says `note: 'a' and 'b' are one object here` and withholds the call.
 */
class G476_p434_shared_class_writes {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 434: a write through one of two parameters of a class re-proves the class invariant at the exit; a write through a local alias of one reaches the identity map, a boolean field's is declined (both unsound before), and a failure needing the two to be one object says so and withholds the call."

    static final List<Map> CASES = [

        [group: "P434 writes through parameters of one class", name: "the invariant is re-proved",
         ok: true,
         src: tc('''class A {
                        @Requires({ a != null && b != null && p >= 0 })
                        static void f(C a, C b, int p) { a.n = p }
                    }
                    @Invariant({ n >= 0 })
                    final class C { int n }''')],

        // Unchecked before: Phase 433 covered the lone parameter's store only
        [group: "P434 writes through parameters of one class", name: "… and refutes when the write breaks it",
         expect: ["Cannot prove class invariant of C holds for 'a' at exit of g", "fails on: g(new C(n: 0), new C("],
         src: tc('''class A {
                        @Requires({ a != null && b != null })
                        static void g(C a, C b, int p) { a.n = p }
                    }
                    @Invariant({ n >= 0 })
                    final class C { int n }''')],

        // It said `a$id = 3, b$id = 3` and `fails on: same(new C(), new C())`
        [group: "P434 writes through parameters of one class", name: "a failure that needs one object says so",
         expect: ["Cannot prove postcondition of same", "note: 'a' and 'b' are one object here",
                  "no failing call: the failure needs 'a' and 'b' to be one object"],
         refute: ['$id', "fails on:"],
         src: tc('''class A {
                        @Requires({ a != null && b != null && b.n == 0 })
                        @Ensures({ b.n == 0 })
                        static void same(C a, C b) { a.n = 5 }
                    }
                    final class C { int n }''')],

        // Unsound before: the alias's write bound `a$n`, which the map read of `a.n` never saw
        [group: "P434 writes through parameters of one class", name: "a write through a local alias reaches the map",
         expect: ["Cannot prove postcondition of viaAlias", "ensured: (a.n == 0)"],
         src: tc('''class A {
                        @Requires({ a != null && b != null && a.n == 0 })
                        @Ensures({ a.n == 0 })
                        static void viaAlias(C a, C b) { C d = a; d.n = 5 }
                    }
                    final class C { int n }''')],

        [group: "P434 writes through parameters of one class", name: "… and proves what it wrote",
         ok: true,
         src: tc('''class A {
                        @Requires({ a != null && b != null })
                        @Ensures({ a.n == 5 })
                        static void viaAlias(C a, C b) { C d = a; d.n = 5 }
                    }
                    final class C { int n }''')],

        // Unsound before: `a.on = true` was bound by name, so `!b.on` proved though `a === b` makes it true. Declined
        // here at first; Phase 436 stores it in the identity map, so it refutes on the shared object
        [group: "P434 writes through parameters of one class", name: "a boolean field's write reaches the other",
         expect: ["Cannot prove postcondition of boolw", "note: 'a' and 'b' are one object here"],
         src: tc('''class A {
                        @Requires({ a != null && b != null && !b.on })
                        @Ensures({ !b.on })
                        static void boolw(C a, C b) { a.on = true }
                    }
                    final class C { int n; boolean on }''')],
    ]
}
