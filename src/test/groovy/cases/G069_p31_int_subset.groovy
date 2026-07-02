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

/** 'P31 int-subset' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G069_p31_int_subset {

    static final List<Map> CASES = [

        // ---------- Phase 31: Int-element s.containsAll(t) via bounded-domain context ----------
        // With Sets.boundedBy(t, n) registered, subset entails membership transfer for any in-domain
        // element — the bounded-universal lowering instantiates at the in-bounds witness.
        [group: 'P31 int-subset', name: 'Int subset with Sets.boundedBy verifies membership transfer', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(required, n) && granted.containsAll(required) &&
                                    0 <= u && u < n && u in required })
                        @Ensures({ u in granted })
                        static int f(Set<Integer> granted, Set<Integer> required, int n, int u) { 0 }
                    }''')],
        // Soundness: without the containsAll, membership in required doesn't transfer to granted.
        [group: 'P31 int-subset', name: 'Int subset: membership without subset refuted',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(required, n) && 0 <= u && u < n && u in required })
                        @Ensures({ u in granted })
                        static int f(Set<Integer> granted, Set<Integer> required, int n, int u) { 0 }
                    }''')],
        // Reflexivity: s.containsAll(s) once s is bounded — the bounded universal degenerates
        // to ∀i. 0<=i<n ⟹ (i ∈ s ⟹ i ∈ s), trivially true.
        [group: 'P31 int-subset', name: 'Int subset: reflexivity', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(s, n) })
                        @Ensures({ s.containsAll(s) })
                        static int f(Set<Integer> s, int n) { 0 }
                    }''')],
        // Transitivity: a ⊇ b ∧ b ⊇ c ⟹ a ⊇ c, when all three are bounded by the same n. Z3
        // chains the bounded universals via the shared range guard.
        [group: 'P31 int-subset', name: 'Int subset: transitivity', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(b, n) && Sets.boundedBy(c, n) &&
                                    a.containsAll(b) && b.containsAll(c) })
                        @Ensures({ a.containsAll(c) })
                        static int f(Set<Integer> a, Set<Integer> b, Set<Integer> c, int n) { 0 }
                    }''')],
        // Bound on the SUPERSET (not the subset operand) doesn't unblock — the universal needs
        // to range over the subset's domain. Honest skip.
        [group: 'P31 int-subset', name: 'Int subset: bound on superset only still skips',
         expect: 'outside fragment',
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(granted, n) && granted.containsAll(required) })
                        @Ensures({ true })
                        static int f(Set<Integer> granted, Set<Integer> required, int n) { 0 }
                    }''')],
    ]
}
