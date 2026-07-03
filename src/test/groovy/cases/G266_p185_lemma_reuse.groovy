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

/** 'P185 lemma-reuse' — quantified lemmas reusable under renamed Function formals; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G266_p185_lemma_reuse {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Lemma reuse under renamed Function formals — the Phase-175 aligned-names footgun, closed. A Function-typed formal has no scalar handle to equate across a call boundary: its identity IS the uninterpreted apply$<name> symbol, so a generic lemma frame(g, a, b) with a quantified @Requires over g only lined up with a caller\'s facts when the caller\'s function was ALSO named g. The checker now registers a call-site alias (formal -> named actual) on the per-VC encoder for both the @Requires discharge and the @Ensures assumption, so the lemma\'s g.apply(x) mints the caller\'s apply$csAF symbol — one generic recursive frame lemma serves any caller. Teeth both ways: passing a function the caller holds no facts about fails the callee precondition, and a wrong conclusion refutes; two formals bound to one actual unify.'

    static final List<Map> CASES = [

        // ---------- Phase 185: lemma reuse under renamed Function formals ----------
        // The ticket-lock arc (Phases 174-175) had to name every frame lemma's formals identically to the
        // caller's actuals (csAF/tAF/servingF), because a Function formal's identity is its apply$<name>
        // uninterpreted-function symbol — a scalar formal is equated to its actual's handle, but a Function
        // formal had nothing to connect it. The checker now aliases the formal to a NAMED actual at the call
        // site (both when discharging the callee's @Requires and when assuming its @Ensures), so a generic
        // lemma is reusable: its quantified precondition translates directly onto the caller's facts.
        [group: 'P185 lemma-reuse', name: 'generic frame lemma reused under renamed actuals', ok: true,
         src: tc('''class Reuse {
                        @Requires({ a <= b && (a..<b).every { int i -> g(i + 1) == g(i) } })
                        @Ensures({ g.apply(b) == g.apply(a) })
                        @Decreases({ b - a })
                        static void frame(Function<Integer,Integer> g, int a, int b) {
                            if (a < b) frame(g, a + 1, b)
                        }
                        @Requires({ n <= u && (n..<u).every { int i -> csAF(i + 1) == csAF(i) } })
                        @Ensures({ csAF.apply(u) == csAF.apply(n) })
                        static void use(Function<Integer,Integer> csAF, int n, int u) {
                            frame(csAF, n, u)
                        }
                    }''')],
        // Teeth (soundness of the alias): the caller's facts are about csAF, but it passes a DIFFERENT
        // function — the callee's quantified @Requires must NOT discharge.
        [group: 'P185 lemma-reuse', name: 'passing the wrong function fails the precondition', expect: 'Cannot prove precondition',
         src: tc('''class ReuseWrongFn {
                        @Requires({ a <= b && (a..<b).every { int i -> g(i + 1) == g(i) } })
                        @Ensures({ g.apply(b) == g.apply(a) })
                        @Decreases({ b - a })
                        static void frame(Function<Integer,Integer> g, int a, int b) {
                            if (a < b) frame(g, a + 1, b)
                        }
                        @Requires({ n <= u && (n..<u).every { int i -> csAF(i + 1) == csAF(i) } })
                        @Ensures({ other.apply(u) == other.apply(n) })
                        static void use(Function<Integer,Integer> csAF, Function<Integer,Integer> other, int n, int u) {
                            frame(other, n, u)
                        }
                    }''')],
        // Teeth (the assumed @Ensures is aliased, not parroted): reuse with a WRONG conclusion refutes.
        [group: 'P185 lemma-reuse', name: 'renamed reuse with a wrong conclusion refutes', expect: 'Cannot prove postcondition',
         src: tc('''class ReuseWrongConcl {
                        @Requires({ a <= b && (a..<b).every { int i -> g(i + 1) == g(i) } })
                        @Ensures({ g.apply(b) == g.apply(a) })
                        @Decreases({ b - a })
                        static void frame(Function<Integer,Integer> g, int a, int b) {
                            if (a < b) frame(g, a + 1, b)
                        }
                        @Requires({ n <= u && (n..<u).every { int i -> csAF(i + 1) == csAF(i) } })
                        @Ensures({ csAF.apply(u) == csAF.apply(n) + 1 })
                        static void use(Function<Integer,Integer> csAF, int n, int u) {
                            frame(csAF, n, u)
                        }
                    }''')],
        // Two formals bound to ONE actual unify on the same apply$ symbol — needsEqual(h, h) discharges
        // its p.apply(0) == q.apply(0) precondition trivially.
        [group: 'P185 lemma-reuse', name: 'two formals sharing one actual unify', ok: true,
         src: tc('''class ReuseShared {
                        @Requires({ p.apply(0) == q.apply(0) })
                        @Ensures({ true })
                        static void needsEqual(Function<Integer,Integer> p, Function<Integer,Integer> q) {}
                        static void use(Function<Integer,Integer> h) {
                            needsEqual(h, h)
                        }
                    }''')],
    ]
}
