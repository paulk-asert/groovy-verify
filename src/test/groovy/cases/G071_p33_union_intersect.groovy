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

/** 'P33 union/intersect' — 8 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G071_p33_union_intersect {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Inline set algebra membership: union is a disjunction, intersection a conjunction of operand memberships.'

    static final List<Map> CASES = [

        // ---------- Phase 33: inline set union / intersection (lazy lowering on .contains, .containsAll) ----------
        // Union .contains: membership in (a + b) follows from membership in either operand.
        [group: 'P33 union/intersect', name: 'union: contains is disjunction of operand memberships', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ Role.ADMIN in a })
                        @Ensures({ Role.ADMIN in (a + b) })
                        static int f(Set<Role> a, Set<Role> b) { 0 }
                    }''')],
        // Soundness: union .contains refuted when neither operand contains the element.
        [group: 'P33 union/intersect', name: 'union: contains refuted when neither operand has it',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Ensures({ Role.ADMIN in (a + b) })
                        static int f(Set<Role> a, Set<Role> b) { 0 }
                    }''')],
        // Intersection .contains: membership in (a ∩ b) requires membership in BOTH operands.
        [group: 'P33 union/intersect', name: 'intersect: contains is conjunction', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ Role.ADMIN in a && Role.ADMIN in b })
                        @Ensures({ Role.ADMIN in a.intersect(b) })
                        static int f(Set<Role> a, Set<Role> b) { 0 }
                    }''')],
        // Soundness: intersection refuted when only one operand contains the element.
        [group: 'P33 union/intersect', name: 'intersect: contains refuted with only one operand',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ Role.ADMIN in a })
                        @Ensures({ Role.ADMIN in a.intersect(b) })
                        static int f(Set<Role> a, Set<Role> b) { 0 }
                    }''')],
        // Union .containsAll: every element of u is in a OR in b.
        [group: 'P33 union/intersect', name: 'union: containsAll via finite conjunction', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ a.containsAll(u) })
                        @Ensures({ (a + b).containsAll(u) })
                        static int f(Set<Role> a, Set<Role> b, Set<Role> u) { 0 }
                    }''')],
        // Intersection .containsAll: every element of u must be in BOTH a and b.
        [group: 'P33 union/intersect', name: 'intersect: containsAll via finite conjunction', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ a.containsAll(u) && b.containsAll(u) })
                        @Ensures({ a.intersect(b).containsAll(u) })
                        static int f(Set<Role> a, Set<Role> b, Set<Role> u) { 0 }
                    }''')],
        // Soundness anchor: union .containsAll refutes when neither operand alone covers u.
        [group: 'P33 union/intersect', name: 'union: containsAll refuted with neither operand covering',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Ensures({ (a + b).containsAll(u) })
                        static int f(Set<Role> a, Set<Role> b, Set<Role> u) { 0 }
                    }''')],
        [group: 'P33 union/intersect', name: 'inline intersection in  (a & b)', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && b != null })
                        @Ensures({ result == ((3 in a && 3 in b) ? 1 : 0) })
                        static int common(Set<Integer> a, Set<Integer> b) { (3 in (a & b)) ? 1 : 0 }
                    }''')],
    ]
}
