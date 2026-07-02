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

/** 'P30 subset' — 7 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G068_p30_subset {

    static final List<Map> CASES = [

        // ---------- Phase 30: s.containsAll(t) — subset reasoning over enum-element sets ----------
        // Subset assumption carries through: granted ⊇ required ∧ x ∈ required ⟹ x ∈ granted.
        [group: 'P30 subset', name: 'containsAll: subset entails membership transfer', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ granted.containsAll(required) && Role.ADMIN in required })
                        @Ensures({ Role.ADMIN in granted })
                        static int check(Set<Role> granted, Set<Role> required) { 0 }
                    }''')],
        // Soundness: if granted does NOT contain all of required, the claim can refute.
        [group: 'P30 subset', name: 'containsAll: membership without subset refuted',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ Role.ADMIN in required })
                        @Ensures({ Role.ADMIN in granted })
                        static int check(Set<Role> granted, Set<Role> required) { 0 }
                    }''')],
        // Reflexivity — every set contains all of itself (every constant ∈ s ⟹ ∈ s, trivially).
        [group: 'P30 subset', name: 'containsAll: reflexivity', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Ensures({ s.containsAll(s) })
                        static int f(Set<Role> s) { 0 }
                    }''')],
        // Transitivity: a ⊇ b ∧ b ⊇ c ⟹ a ⊇ c. Each containsAll lowers to a per-constant
        // implication; the conjunction chain gives transitive ⟹ for each constant.
        [group: 'P30 subset', name: 'containsAll: transitivity', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ a.containsAll(b) && b.containsAll(c) })
                        @Ensures({ a.containsAll(c) })
                        static int f(Set<Role> a, Set<Role> b, Set<Role> c) { 0 }
                    }''')],
        // Empty subset: `granted.containsAll(required)` when required.size() == 0. Verifies via
        // the empty iff `card(s) == 0 ⟺ no enum constant ∈ s` — so the per-constant implications
        // `c ∈ required ⟹ c ∈ granted` are all vacuously true.
        [group: 'P30 subset', name: 'containsAll: empty subset', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ required.size() == 0 })
                        @Ensures({ granted.containsAll(required) })
                        static int f(Set<Role> granted, Set<Role> required) { 0 }
                    }''')],
        // Composition with @Modifies: a grant operation that adds a role preserves the subset
        // claim against a stable `required` set.
        [group: 'P30 subset', name: 'containsAll: add preserves subset', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        Set<Role> granted
                        @Requires({ granted.containsAll(required) })
                        @Modifies({ this.granted })
                        @Ensures({ granted.containsAll(required) })
                        void grant(Set<Role> required, Role r) { granted.add(r) }
                    }''')],
        // Int-element subset WITHOUT a bound on the subset operand still skips honestly.
        [group: 'P30 subset', name: 'containsAll: Int-element subset without bound skipped',
         expect: 'outside fragment',
         src: tc('''class C {
                        @Requires({ a.containsAll(b) })
                        @Ensures({ true })
                        static int f(Set<Integer> a, Set<Integer> b) { 0 }
                    }''')],
    ]
}
