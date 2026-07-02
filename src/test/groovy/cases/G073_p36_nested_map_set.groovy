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

/** 'P36 nested map<set>' — 8 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G073_p36_nested_map_set {

    static final List<Map> CASES = [

        // ---------- Phase 36: Map<K, Set<V>> nesting (read-only) ----------
        // Enum key + enum value set: x in m[k] over Map<Role, Set<Role>> lowers to membership in
        // the inner set, an SMT array term (no named handle minted). Round-trip identity.
        [group: 'P36 nested map<set>', name: 'enum/enum: in m[k] round-trip', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ Role.USER in m[Role.ADMIN] })
                        @Ensures({ Role.USER in m[Role.ADMIN] })
                        static int f(Map<Role, Set<Role>> m) { 0 }
                    }''')],
        // m[k].contains(x) as method-form sibling of `in` — same lowering through
        // translateMethodCall instead of translateBinary.
        [group: 'P36 nested map<set>', name: 'enum/enum: m[k].contains round-trip', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ m[Role.ADMIN].contains(Role.USER) })
                        @Ensures({ m[Role.ADMIN].contains(Role.USER) })
                        static int f(Map<Role, Set<Role>> m) { 0 }
                    }''')],
        // Soundness: m[k] at one key tells us nothing about m[k'] at another key.
        [group: 'P36 nested map<set>', name: 'enum/enum: distinct keys do not leak membership',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ Role.USER in m[Role.ADMIN] })
                        @Ensures({ Role.USER in m[Role.GUEST] })
                        static int f(Map<Role, Set<Role>> m) { 0 }
                    }''')],
        // containsAll on the nested set: m[k] covers an enum-element subset s ⟹ every constant of
        // s is in m[k]. Finite conjunction over the inner enum domain.
        [group: 'P36 nested map<set>', name: 'enum/enum: m[k].containsAll(s) over enum V', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ m[Role.ADMIN].containsAll(s) && Role.USER in s })
                        @Ensures({ Role.USER in m[Role.ADMIN] })
                        static int f(Map<Role, Set<Role>> m, Set<Role> s) { 0 }
                    }''')],
        // Non-enum inner element type: Map<Role, Set<Integer>>. Membership lowers through the
        // Int sort cleanly; .containsAll over Int element domain is out of scope (needs
        // bounded universal with intSubsetBounds on a transient receiver — known limit).
        [group: 'P36 nested map<set>', name: 'enum/Int: in m[k] over Set<Integer> values', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ 42 in m[Role.ADMIN] })
                        @Ensures({ 42 in m[Role.ADMIN] })
                        static int f(Map<Role, Set<Integer>> m) { 0 }
                    }''')],
        // Composes with Phase 32a's containsKey: m.containsKey rides the independent key-set,
        // which is unaffected by the nested-value-sort change.
        [group: 'P36 nested map<set>', name: 'enum/enum: m.containsKey still works alongside nested values', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ m.containsKey(Role.ADMIN) && Role.USER in m[Role.ADMIN] })
                        @Ensures({ m.containsKey(Role.ADMIN) })
                        static int f(Map<Role, Set<Role>> m) { 0 }
                    }''')],
        // README example anchor: RBAC over Map<Role, Set<Perm>>. ADMIN covering the required
        // permission set implies a specific requested perm is in ADMIN's grant set via the
        // finite conjunction over Perm constants.
        [group: 'P36 nested map<set>', name: 'README RBAC: adminMayWrite verifies', ok: true,
         src: tc('''class Acl {
                        enum Role { ADMIN, USER, GUEST }
                        enum Perm { READ, WRITE, DELETE }
                        @Requires({ grants[Role.ADMIN].containsAll(required) })   // ADMIN covers required …
                        @Ensures({ (Perm.WRITE in required) ==> (Perm.WRITE in grants[Role.ADMIN]) })   // … so WRITE, when requested, is held
                        static int adminMayWrite(Map<Role, Set<Perm>> grants, Set<Perm> required) { 0 }
                    }''')],
        // Soundness anchor: without the containsAll precondition, the postcondition refutes.
        [group: 'P36 nested map<set>', name: 'README RBAC: refutes without containsAll',
         expect: 'Cannot prove postcondition',
         src: tc('''class Acl {
                        enum Role { ADMIN, USER, GUEST }
                        enum Perm { READ, WRITE, DELETE }
                        @Ensures({ (Perm.WRITE in required) ==> (Perm.WRITE in grants[Role.ADMIN]) })
                        static int adminMayWrite(Map<Role, Set<Perm>> grants, Set<Perm> required) { 0 }
                    }''')],
    ]
}
