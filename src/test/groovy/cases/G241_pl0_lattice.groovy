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

/** 'PL0 lattice' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G241_pl0_lattice {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A user-defined security lattice proven well-formed: leq a partial order, join/meet the lub/glb; a non-transitive order refutes.'

    static final List<Map> CASES = [

        // ---------- Phase L0 — security lattice + well-formedness laws (Smith, "A Dafny-based approach to
        //            thread-local information flow analysis", §III) ----------
        // The foundation of the paper's information-flow approach: a user-defined security lattice, with lemmas
        // proving it is *indeed* a lattice (leq a partial order; join/meet the least-upper / greatest-lower bound).
        // It maps onto existing machinery with no new solver theory: the lattice is an enum sort (Phase 27–30),
        // leq/join/meet are pure functions characterised by their @Ensures (Phase 130 `glue` combiner idiom), and
        // each law is a method whose params are the universally-quantified levels — Z3 discharges it by case-split
        // over the finite enum domain (the same shape as the monad-law cases above). This is Slice 0: the algebra
        // and its laws only — the Γ-tracking assignment/branch noninterference VCs are Slice 1 (a future phase).

        // The case study's boolean lattice (Low ⊑ High), transcribed verbatim. All seven lattice laws prove.
        // leq/join/meet are contract-free so the verifier inlines each as a pure function (its body is the
        // defining equation); only the law methods carry @Ensures (a contracted callee would instead be the
        // inter-procedural path). The two-element form leans on L having *exactly* {Low, High} — the join being
        // an upper bound only holds because the domain is finite — which the enum-domain-closure axiom supplies
        // (each enum-sorted param is pinned to `c1 ∨ … ∨ cN`, since enum sorts are otherwise open).
        [group: 'PL0 lattice', name: 'boolean lattice (Low/High): partial-order + join/meet bound laws prove', ok: true,
         src: tc('''class Sec {
                        enum L { Low, High }
                        static boolean leq(L l1, L l2) { l1 == L.Low || l2 == L.High }
                        static L join(L l1, L l2) { leq(l1, l2) ? l2 : l1 }
                        static L meet(L l1, L l2) { leq(l1, l2) ? l1 : l2 }
                        @Ensures({ leq(l1, l1) })
                        static void reflexive(L l1) { }
                        @Ensures({ (leq(l1, l2) && leq(l2, l1)) ==> (l1 == l2) })
                        static void antisymmetric(L l1, L l2) { }
                        @Ensures({ (leq(l1, l2) && leq(l2, l3)) ==> leq(l1, l3) })
                        static void transitive(L l1, L l2, L l3) { }
                        @Ensures({ leq(l1, join(l1, l2)) && leq(l2, join(l1, l2)) })
                        static void joinUpperBound(L l1, L l2) { }
                        @Ensures({ (leq(l1, l3) && leq(l2, l3)) ==> leq(join(l1, l2), l3) })
                        static void joinLeast(L l1, L l2, L l3) { }
                        @Ensures({ leq(meet(l1, l2), l1) && leq(meet(l1, l2), l2) })
                        static void meetLowerBound(L l1, L l2) { }
                        @Ensures({ (leq(l3, l1) && leq(l3, l2)) ==> leq(l3, meet(l1, l2)) })
                        static void meetGreatest(L l1, L l2, L l3) { }
                    }''')],

        // The paper's general "diamond" lattice — A above B and C (incomparable), both above D. This is the
        // datatype L = A | B | C | D / leq / join / meet of §III, and its partialorder / joinLemma / meetLemma
        // lemmas, transcribed. All prove for the genuine lattice.
        [group: 'PL0 lattice', name: 'diamond lattice (A/B/C/D): partialorder + joinLemma + meetLemma prove', ok: true,
         src: tc('''class Diamond {
                        enum L { A, B, C, D }
                        static boolean leq(L l1, L l2) { l1 == L.D || l1 == l2 || l2 == L.A }
                        static L join(L l1, L l2) { leq(l1, l2) ? l2 : (leq(l2, l1) ? l1 : L.A) }
                        static L meet(L l1, L l2) { leq(l1, l2) ? l1 : (leq(l2, l1) ? l2 : L.D) }
                        @Ensures({ leq(l1, l1) })
                        @Ensures({ (leq(l1, l2) && leq(l2, l1)) ==> (l1 == l2) })
                        @Ensures({ (leq(l1, l2) && leq(l2, l3)) ==> leq(l1, l3) })
                        static void partialorder(L l1, L l2, L l3) { }
                        @Ensures({ leq(l1, join(l1, l2)) && leq(l2, join(l1, l2)) })
                        @Ensures({ (leq(l1, l3) && leq(l2, l3)) ==> leq(join(l1, l2), l3) })
                        static void joinLemma(L l1, L l2, L l3) { }
                        @Ensures({ leq(meet(l1, l2), l1) && leq(meet(l1, l2), l2) })
                        @Ensures({ (leq(l3, l1) && leq(l3, l2)) ==> leq(l3, meet(l1, l2)) })
                        static void meetLemma(L l1, L l2, L l3) { }
                    }''')],

        // Soundness — a mis-specified order is caught. This leq makes A ⊑ B and B ⊑ C but NOT A ⊑ C, so it is not
        // transitive and hence not a partial order: the transitivity lemma must refute, with the witnessing triple
        // (l1=A, l2=B, l3=C) as the counterexample. This is exactly the check the paper relies on to know the
        // user's encoding "is indeed a lattice".
        [group: 'PL0 lattice', name: 'non-transitive order: transitivity lemma refuted (A⊑B, B⊑C, ¬A⊑C)',
         expect: 'Cannot prove postcondition',
         src: tc('''class BadOrder {
                        enum L { A, B, C }
                        static boolean leq(L l1, L l2) { l1 == l2 || (l1 == L.A && l2 == L.B) || (l1 == L.B && l2 == L.C) }
                        @Ensures({ (leq(l1, l2) && leq(l2, l3)) ==> leq(l1, l3) })
                        static void transitive(L l1, L l2, L l3) { }
                    }''')],

        // Soundness — a "join" that is not actually an upper bound is caught. This join returns its first argument,
        // so leq(l2, join(l1,l2)) fails (e.g. l1=D, l2=B over the diamond): the upper-bound lemma refutes. Guards
        // against the subtle bug where a programmer's join/meet definitions don't match their leq.
        [group: 'PL0 lattice', name: 'broken join (returns l1, not an upper bound): joinLemma upper-bound refuted',
         expect: 'Cannot prove postcondition',
         src: tc('''class BadJoin {
                        enum L { A, B, C, D }
                        static boolean leq(L l1, L l2) { l1 == L.D || l1 == l2 || l2 == L.A }
                        static L join(L l1, L l2) { l1 }
                        @Ensures({ leq(l1, join(l1, l2)) && leq(l2, join(l1, l2)) })
                        static void joinUpperBound(L l1, L l2) { }
                    }''')],
    ]
}
