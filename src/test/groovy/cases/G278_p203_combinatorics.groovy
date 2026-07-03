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

/** 'P203 combinatorics' — 8 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G278_p203_combinatorics {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The combinatorics pack (math-comp binomial.v inspired): Fact.of(n) with base/step/positivity axioms, and Binom.of(n, k) — the first TWO-argument spec primitive — under Pascal\'s rule. Ground values unfold by e-matching (fact(4)==24, C(4,2)==6); symbolic identities prove by recursive-lemma induction (C(n,1)==n via Pascal + both bases); a factorial loop carries n! as its invariant. Teeth: wrong ground values are DISPROVED (the tractable UNSAT direction — refuting a recurrence-axiomed ground claim needs an MBQI model and times out), and the inconsistency canary pins that a wrong binomial never cleanly proves (it caught an unguarded-base axiom clash during development).'

    static final List<Map> CASES = [

        // ---------- Phase 203: combinatorics — fact$ and the 2-ary binom$ under Pascal's rule ----------
        // Ground unfolding: e-matching walks the step axiom down to the base.
        [group: 'P203 combinatorics', name: 'fact(4) == 24 (ground unfolding)', ok: true,
         src: tc('''class C {
                       @Ensures({ result == 24 })
                       static int f() { Fact.of(4) }
                   }''')],
        [group: 'P203 combinatorics', name: 'C(4,2) == 6 (Pascal, ground)', ok: true,
         src: tc('''class C {
                       @Ensures({ result == 6 })
                       static int f() { Binom.of(4, 2) }
                   }''')],
        // The factorial generation loop: r == Fact.of(i) preserved by r = r * (i+1) via the step axiom —
        // the fib-loop shape with a product.
        [group: 'P203 combinatorics', name: 'factorial loop carries n! as its invariant', ok: true,
         src: tc('''class C {
                       @Requires({ n >= 0 })
                       @Ensures({ result == Fact.of(n) })
                       static int factorial(int n) {
                           int r = 1
                           int i = 0
                           @Invariant({ 0 <= i && i <= n && r == Fact.of(i) })
                           @Decreases({ n - i })
                           while (i < n) {
                               r = r * (i + 1)
                               i = i + 1
                           }
                           return r
                       }
                   }''')],
        // Symbolic identity by recursive-lemma induction: C(n,1) == n (Pascal at k=1 + both bases).
        [group: 'P203 combinatorics', name: 'C(n,1) == n by induction', ok: true,
         src: tc('''class C {
                       @Requires({ n >= 0 })
                       @Ensures({ Binom.of(n, 1) == n })
                       @Decreases({ n })
                       static void chooseOne(int n) {
                           if (n > 0) chooseOne(n - 1)
                       }
                   }''')],
        // Positivity of the factorial, symbolically (the asserted theorem axiom, the gcd$-nonzero move).
        [group: 'P203 combinatorics', name: 'Fact.of(n) >= 1 symbolically', ok: true,
         src: tc('''class C {
                       @Ensures({ Fact.of(n) >= 1 })
                       static void positive(int n) {}
                   }''')],
        // Teeth, disproof form: a WRONG ground value is provably ruled out (`!= 25` VERIFIES — which a
        // vacuous or inconsistent axiom set could not do in this direction only if consistent; see below).
        // The refute direction for fact needs a model of the NIA step universal (MBQI) and times out —
        // the disproof (UNSAT) direction is the tractable spelling of the same fact.
        [group: 'P203 combinatorics', name: 'fact(4) != 25 is disproved (wrong value ruled out)', ok: true,
         src: tc('''class C {
                       @Ensures({ result != 25 })
                       static int f() { Fact.of(4) }
                   }''')],
        // Teeth, the inconsistency canary: a wrong binomial must never PROVE. The solver refutes or
        // times out (recurrence universals defeat MBQI model-building — the expected substring matches
        // both "Cannot prove postcondition of f" and "Could not decide postcondition of f"), but a clean
        // verify fails this case — which is exactly how it caught a real axiom inconsistency during
        // development (an unguarded base clashing with the out-of-range zero at negative n).
        [group: 'P203 combinatorics', name: 'C(4,2) == 7 never proves (inconsistency canary)', expect: 'postcondition of f',
         src: tc('''class C {
                       @Ensures({ result == 7 })
                       static int f() { Binom.of(4, 2) }
                   }''')],
        [group: 'P203 combinatorics', name: 'C(4,2) != 7 is disproved', ok: true,
         src: tc('''class C {
                       @Ensures({ result != 7 })
                       static int f() { Binom.of(4, 2) }
                   }''')],
    ]
}
