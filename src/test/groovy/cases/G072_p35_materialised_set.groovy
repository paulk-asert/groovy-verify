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

/** 'P35 materialised set' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G072_p35_materialised_set {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A materialised set Set u = a op b mints u as a first-class set whose membership follows the iff axiom.'

    static final List<Map> CASES = [

        // ---------- Phase 35: materialised set ops (Set u = a + b as first-class set) ----------
        // Materialised union: the new local `u` is a first-class set with the membership iff axiom.
        // The body uses `ADMIN in u` to drive the return value; under @Requires({ ADMIN in a }) the
        // iff makes `ADMIN in u` provably true, so result == 1 is verified.
        // (@Ensures can't reference body-locals through the @TypeChecked closure scope, so we drive
        //  the postcondition via the result instead — the meaningful work happens in the body.)
        [group: 'P35 materialised set', name: 'materialised union: member follows from operand member', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ Role.ADMIN in a })
                        @Ensures({ result == 1 })
                        static int f(Set<Role> a, Set<Role> b) {
                            Set<Role> u = a + b
                            Role.ADMIN in u ? 1 : 0
                        }
                    }''')],
        // Materialised intersection: ADMIN in u requires ADMIN in BOTH operands.
        // The intersect's GDK signature returns Collection, so the assignment needs an explicit
        // `as Set<Role>` cast — setBinopFor unwraps the outer CastExpression. Explicit non-null
        // guards on a/b because `.intersect` is a method call (implicit-NPE obligation), unlike `+`.
        [group: 'P35 materialised set', name: 'materialised intersection: member requires both operands', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ a != null && b != null && Role.ADMIN in a && Role.ADMIN in b })
                        @Ensures({ result == 1 })
                        static int f(Set<Role> a, Set<Role> b) {
                            Set<Role> u = a.intersect(b) as Set<Role>
                            Role.ADMIN in u ? 1 : 0
                        }
                    }''')],
        // Soundness: when neither operand contains ADMIN, the body's branch must go to 0 — but
        // the @Ensures result == 1 fails. The refute confirms the iff axiom isn't over-strong.
        [group: 'P35 materialised set', name: 'materialised union: member refuted when neither operand has it',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Ensures({ result == 1 })
                        static int f(Set<Role> a, Set<Role> b) {
                            Set<Role> u = a + b
                            Role.ADMIN in u ? 1 : 0
                        }
                    }''')],
        // Pigeonhole on the materialised set: `u.size() <= 3` auto-holds via the enum-domain axioms
        // (set u is a Set<Role> with N=3 constants, so card(u) ≤ N is asserted on mint).
        [group: 'P35 materialised set', name: 'materialised union: pigeonhole on size', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Ensures({ u.size() <= 3 })
                        static int f(Set<Role> a, Set<Role> b) {
                            Set<Role> u = a + b
                            0
                        }
                    }''')],
        // containsAll composes through the materialised set: if a covers z then so does a + b.
        // The iff axiom on u gives every-element-of-u-is-in-a-or-b; combined with a.containsAll(z),
        // every-element-of-z-is-in-u follows.
        [group: 'P35 materialised set', name: 'materialised union: containsAll composes through u', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ a.containsAll(z) })
                        @Ensures({ u.containsAll(z) })
                        static int f(Set<Role> a, Set<Role> b, Set<Role> z) {
                            Set<Role> u = a + b
                            0
                        }
                    }''')],
        // equals through the materialised set: a + b = b + a (commutativity), verified via mutual
        // containsAll on the materialised forms.
        [group: 'P35 materialised set', name: 'materialised union: commutativity via equals', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Ensures({ u.equals(v) })
                        static int f(Set<Role> a, Set<Role> b) {
                            Set<Role> u = a + b
                            Set<Role> v = b + a
                            0
                        }
                    }''')],
    ]
}
