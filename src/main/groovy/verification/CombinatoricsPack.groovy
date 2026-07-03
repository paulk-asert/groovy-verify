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
package verification

import groovy.transform.CompileStatic
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.MethodCallExpression

import java.util.concurrent.atomic.AtomicInteger

/**
 * Combinatorics spec helpers as an {@link EncodingPack} (Phase 203) — the third pack, inspired by
 * math-comp's {@code binomial.v}/{@code div.v}: {@code Fact.of(n)} (factorial) and {@code Binom.of(n, k)}
 * (the binomial coefficient via <b>Pascal's rule</b>). {@code binom$} is the first spec primitive minted
 * as a genuinely <b>two-argument</b> UF — the same generic {@code applyUF} the 2-ary trace state rides.
 *
 * <p>Axioms (mint-once per VC, recurrences triggered on the primitive's own application):
 * <ul>
 *   <li>{@code fact$}: base {@code fact(0) == 1}; step {@code ∀n. n >= 1 ⟹ fact(n) == n * fact(n-1)}
 *       (a guarded product, the {@code pow$} NIA precedent); positivity {@code ∀n. fact(n) >= 1}
 *       (a theorem of the recurrence finite e-matching can't reach for symbolic args — asserted so
 *       division by a factorial discharges, the {@code gcd$}-nonzero move).</li>
 *   <li>{@code binom$}: bases {@code ∀n. binom(n,0) == 1} and {@code ∀n,k. k > n ⟹ binom(n,k) == 0};
 *       Pascal {@code ∀n,k. n >= 1 ∧ 1 <= k ⟹ binom(n,k) == binom(n-1,k-1) + binom(n-1,k)}.</li>
 * </ul>
 *
 * <p>Both helpers stay runtime-executable ({@link Fact}, {@link Binom}) so unproven contracts degrade to
 * groovy-contracts checks. Corpus: {@code P203 combinatorics} (verify + refute twins).
 */
@CompileStatic
class CombinatoricsPack implements EncodingPack {

    /** Unique bound-variable suffixes across all VCs (the pack is a JVM-wide singleton). */
    private static final AtomicInteger QUANT = new AtomicInteger()

    @Override
    String name() { 'combinatorics' }

    @Override
    List<String> corpusGroups() { ['P203 combinatorics'] }

    @Override
    Object translateCall(TheoryApi api, MethodCallExpression mce, String m, Expression recv, List<Expression> args) {
        if (m != 'of') return TheoryApi.NO_MATCH
        if (args.size() == 1 && TheoryApi.receiverIsClass(recv, 'Fact')) {
            Object n = api.translate(args.get(0))
            if (n == null) return null
            factAxioms(api)
            return apply1(api.session, 'fact$', n)
        }
        if (args.size() == 2 && TheoryApi.receiverIsClass(recv, 'Binom')) {
            Object n = api.translate(args.get(0))
            Object k = api.translate(args.get(1))
            if (n == null || k == null) return null
            binomAxioms(api)
            return apply2(api.session, 'binom$', n, k)
        }
        TheoryApi.NO_MATCH
    }

    private static Object apply1(SmtSession s, String fn, Object a) { s.applyUF(fn, [a], s.intSort()) }
    private static Object apply2(SmtSession s, String fn, Object a, Object b) { s.applyUF(fn, [a, b], s.intSort()) }

    /** fact: base fact(0)==1; step ∀n≥1. fact(n)==n*fact(n-1); positivity ∀n. fact(n)>=1. */
    private static void factAxioms(TheoryApi api) {
        if (!api.axiomsOnce('combinatorics.fact')) return
        SmtSession s = api.session
        Object zero = s.intLit(0L), one = s.intLit(1L)
        s.assertExpr(s.eq(apply1(s, 'fact$', zero), one))
        Object n = s.boundIntVar('fact$n' + QUANT.getAndIncrement())
        Object term = apply1(s, 'fact$', n)
        Object rhs = s.times(n, apply1(s, 'fact$', s.minus(n, one)))
        s.assertExpr(s.forall([n], s.implies(s.ge(n, one), s.eq(term, rhs)), [term]))
        Object p = s.boundIntVar('fact$n' + QUANT.getAndIncrement())
        Object pterm = apply1(s, 'fact$', p)
        s.assertExpr(s.forall([p], s.ge(pterm, one), [pterm]))
    }

    /** binom: bases ∀n. binom(n,0)==1 and ∀n,k. k>n ⟹ binom(n,k)==0; Pascal ∀n≥1,k≥1. */
    private static void binomAxioms(TheoryApi api) {
        if (!api.axiomsOnce('combinatorics.binom')) return
        SmtSession s = api.session
        Object zero = s.intLit(0L), one = s.intLit(1L)
        // Domain guards matter: an unguarded base (∀n. binom(n,0)==1) clashes with the out-of-range
        // axiom at negative n (binom(-1,0) would be both 1 and 0) — an inconsistency the refute twins
        // caught (everything "verified"). All axioms are guarded to the n >= 0 domain.
        Object bn = s.boundIntVar('binom$n' + QUANT.getAndIncrement())
        Object base = apply2(s, 'binom$', bn, zero)
        s.assertExpr(s.forall([bn], s.implies(s.ge(bn, zero), s.eq(base, one)), [base]))
        Object on = s.boundIntVar('binom$n' + QUANT.getAndIncrement())
        Object ok = s.boundIntVar('binom$k' + QUANT.getAndIncrement())
        Object oterm = apply2(s, 'binom$', on, ok)
        s.assertExpr(s.forall([on, ok],
            s.implies(s.and([s.ge(on, zero), s.gt(ok, on)]), s.eq(oterm, zero)), [oterm]))
        Object pn = s.boundIntVar('binom$n' + QUANT.getAndIncrement())
        Object pk = s.boundIntVar('binom$k' + QUANT.getAndIncrement())
        Object pterm = apply2(s, 'binom$', pn, pk)
        Object prhs = s.plus(apply2(s, 'binom$', s.minus(pn, one), s.minus(pk, one)),
                             apply2(s, 'binom$', s.minus(pn, one), pk))
        s.assertExpr(s.forall([pn, pk],
            s.implies(s.and([s.ge(pn, one), s.ge(pk, one)]), s.eq(pterm, prhs)), [pterm]))
    }
}
