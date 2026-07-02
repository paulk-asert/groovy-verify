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

/** 'set algebra' — 12 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G205_set_algebra {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Int-element set algebra membership: x in (a-b) / (a^b) follows from operand memberships.'

    static final List<Map> CASES = [

        // ---------- Set algebra: union (+) / intersection (.intersect) / difference (-) / symmetric difference (^) ----------
        // Each `a <op> b` is one membership combine — x∈(a∪b)=x∈a∨x∈b, x∈(a∩b)=∧, x∈(a\b)=x∈a∧x∉b,
        // x∈(a^b)=xor. Pointwise membership (`x in (a op b)`) works for any element sort; the *bounded*
        // forms — `(a op b).containsAll(u)` and a materialised `Set u = a op b` — lower over the [0,n)
        // domain of a prior `Sets.boundedBy` (Int) or the finite enum domain (enum).

        // Pointwise membership, Int — no bound needed (the combine is per-element).
        [group: 'set algebra', name: 'Int: x in a, !in b => x in (a - b)', ok: true,
         src: tc('''class C {
                        @Requires({ x in a && x !in b })
                        @Ensures({ x in (a - b) })
                        static int f(Set<Integer> a, Set<Integer> b, int x) { 0 }
                    }''')],
        [group: 'set algebra', name: 'Int: x in exactly one => x in (a ^ b)', ok: true,
         src: tc('''class C {
                        @Requires({ x in a && x !in b })
                        @Ensures({ x in (a ^ b) })
                        static int f(Set<Integer> a, Set<Integer> b, int x) { 0 }
                    }''')],
        [group: 'set algebra', name: 'Int: x in both => x !in (a ^ b)', ok: true,
         src: tc('''class C {
                        @Requires({ x in a && x in b })
                        @Ensures({ x !in (a ^ b) })
                        static int f(Set<Integer> a, Set<Integer> b, int x) { 0 }
                    }''')],
        [group: 'set algebra', name: 'Int: x in b => x !in (a - b)', ok: true,
         src: tc('''class C {
                        @Requires({ x in b })
                        @Ensures({ x !in (a - b) })
                        static int f(Set<Integer> a, Set<Integer> b, int x) { 0 }
                    }''')],
        // Soundness: x in a alone does NOT entail x in (a ^ b) — it may be in b too.
        [group: 'set algebra', name: 'Int: x in a alone does not give x in (a ^ b) (refute)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ x in a })
                        @Ensures({ x in (a ^ b) })
                        static int f(Set<Integer> a, Set<Integer> b, int x) { 0 }
                    }''')],
        // Bounded containsAll on a union receiver (Int) — a ⊆ a ∪ b over [0, n).
        [group: 'set algebra', name: 'Int: (a + b).containsAll(a) with bound', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(a, n) })
                        @Ensures({ (a + b).containsAll(a) })
                        static int f(Set<Integer> a, Set<Integer> b, int n) { 0 }
                    }''')],
        // Materialised Int union — subset of an operand transfers through the bounded iff.
        [group: 'set algebra', name: 'Int: materialise u = a + b, u.containsAll(a)', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(a, n) && Sets.boundedBy(b, n) })
                        @Ensures({ u.containsAll(a) })
                        static Set<Integer> f(Set<Integer> a, Set<Integer> b, int n) {
                            Set<Integer> u = a + b
                            u
                        }
                    }''')],
        // Enum difference / symmetric difference — the same combine over the finite enum domain.
        [group: 'set algebra', name: 'enum: ADMIN in a, !in b => ADMIN in (a ^ b)', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ Role.ADMIN in a && Role.ADMIN !in b })
                        @Ensures({ Role.ADMIN in (a ^ b) })
                        static int f(Set<Role> a, Set<Role> b) { 0 }
                    }''')],
        [group: 'set algebra', name: 'enum: ADMIN in b => ADMIN !in (a - b)', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ Role.ADMIN in b })
                        @Ensures({ Role.ADMIN !in (a - b) })
                        static int f(Set<Role> a, Set<Role> b) { 0 }
                    }''')],

        // Groovy also overloads the bitwise operators for sets: `a | b` = union, `a & b` = intersection
        // (aliases of `+` / `.intersect`). Same combine, recognised in setBinopFor.
        [group: 'set algebra', name: 'Int: x in (a & b) => x in a && x in b (& = intersection)', ok: true,
         src: tc('''class C {
                        @Requires({ x in (a & b) })
                        @Ensures({ x in a && x in b })
                        static int f(Set<Integer> a, Set<Integer> b, int x) { 0 }
                    }''')],
        [group: 'set algebra', name: 'Int: x in a => x in (a | b) (| = union)', ok: true,
         src: tc('''class C {
                        @Requires({ x in a })
                        @Ensures({ x in (a | b) })
                        static int f(Set<Integer> a, Set<Integer> b, int x) { 0 }
                    }''')],
        // Soundness: x in a alone does NOT entail x in (a & b) — it must also be in b.
        [group: 'set algebra', name: 'Int: x in a alone does not give x in (a & b) (refute)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ x in a })
                        @Ensures({ x in (a & b) })
                        static int f(Set<Integer> a, Set<Integer> b, int x) { 0 }
                    }''')],
    ]
}
