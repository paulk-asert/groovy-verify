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
 * The number-theory spec helpers as an {@link EncodingPack} — the first pack, and the reference for the
 * shape: each of {@code Fib.of(i)} / {@code Trib.of(i)} / {@code Tetra.of(i)} / {@code Gcd.of(a,b)} /
 * {@code Lcm.of(a,b)} pairs a runtime-executable helper class (so the contract still runs as an ordinary
 * groovy-contracts assertion) with a compile-time lowering to an axiomatised uninterpreted primitive
 * ({@code fib$}, {@code trib$}, {@code tetra$}, {@code gcd$}, {@code lcm$} — the same symbols the encoder
 * minted before the extraction, so the emitted SMT is identical).
 *
 * <p>Defining axioms are asserted once per VC via {@link TheoryApi#axiomsOnce}: base cases as ground
 * equalities, recurrences as universals <b>triggered on the primitive's own application</b> (e-matching
 * unfolds exactly one generation per instance — how a `c = a + b` Fibonacci loop preserves
 * {@code c == Fib.of(i+1)}). {@code Gcd} carries Euclid's base/step plus the non-zero theorem (so
 * {@code a.intdiv(Gcd.of(a,b))} discharges its divisor obligation); {@code Lcm} is defined through the
 * fundamental identity {@code lcm(a,b) * gcd(a,b) == a*b}.
 *
 * <p>Everything here is expressed against {@link TheoryApi} + the generic {@link SmtSession} — notably
 * {@code applyUF}, which makes bespoke per-function backend methods unnecessary. The pack's regression
 * mesh is the pre-existing corpus: groups {@code P55 fib}, {@code P63 fibfib}, {@code P46 fib4},
 * {@code HE013 gcd}, {@code P-lcm} (verify + refute each).
 */
@CompileStatic
class NumberTheoryPack implements EncodingPack {

    /** Unique bound-variable suffixes across all VCs (the pack is a JVM-wide singleton). */
    private static final AtomicInteger QUANT = new AtomicInteger()

    @Override
    String name() { 'number-theory' }

    @Override
    List<String> corpusGroups() { ['P55 fib', 'P63 fibfib', 'P46 fib4', 'HE013 gcd', 'P-lcm', 'P204 bezout'] }

    @Override
    Object translateCall(TheoryApi api, MethodCallExpression mce, String m, Expression recv, List<Expression> args) {
        if (m != 'of' && m != 'u' && m != 'v') return TheoryApi.NO_MATCH
        if (args.size() == 1) {
            if (TheoryApi.receiverIsClass(recv, 'Fib'))   return unary(api, args, this.&fibAxioms,   'fib$')
            if (TheoryApi.receiverIsClass(recv, 'Trib'))  return unary(api, args, this.&tribAxioms,  'trib$')
            if (TheoryApi.receiverIsClass(recv, 'Tetra')) return unary(api, args, this.&tetraAxioms, 'tetra$')
        }
        if ((m == 'u' || m == 'v') && args.size() == 2 && TheoryApi.receiverIsClass(recv, 'Bezout')) {
            Object a = api.translate(args.get(0))
            Object b = api.translate(args.get(1))
            if (a == null || b == null) return null
            gcdAxioms(api)
            bezoutAxioms(api)
            return apply2(api.session, m == 'u' ? 'bezU$' : 'bezV$', a, b)
        }
        if (args.size() == 2) {
            if (TheoryApi.receiverIsClass(recv, 'Gcd')) {
                Object a = api.translate(args.get(0))
                Object b = api.translate(args.get(1))
                if (a == null || b == null) return null
                gcdAxioms(api)
                return apply2(api.session, 'gcd$', a, b)
            }
            if (TheoryApi.receiverIsClass(recv, 'Lcm')) {
                Object a = api.translate(args.get(0))
                Object b = api.translate(args.get(1))
                if (a == null || b == null) return null
                gcdAxioms(api)
                lcmAxioms(api)
                return apply2(api.session, 'lcm$', a, b)
            }
        }
        TheoryApi.NO_MATCH
    }

    /** Translate a unary helper's argument, assert the primitive's axioms once, apply the primitive. */
    private static Object unary(TheoryApi api, List<Expression> args, Closure axioms, String fn) {
        Object k = api.translate(args.get(0))
        if (k == null) return null
        axioms.call(api)
        apply1(api.session, fn, k)
    }

    private static Object apply1(SmtSession s, String fn, Object a) { s.applyUF(fn, [a], s.intSort()) }
    private static Object apply2(SmtSession s, String fn, Object a, Object b) { s.applyUF(fn, [a, b], s.intSort()) }

    /** fib: base fib(0)==0, fib(1)==1; step ∀k. k>=2 ⟹ fib(k)==fib(k-1)+fib(k-2), triggered on fib(k). */
    private static void fibAxioms(TheoryApi api) {
        if (!api.axiomsOnce('numtheory.fib')) return
        SmtSession s = api.session
        Object zero = s.intLit(0L), one = s.intLit(1L), two = s.intLit(2L)
        s.assertExpr(s.eq(apply1(s, 'fib$', zero), zero))
        s.assertExpr(s.eq(apply1(s, 'fib$', one), one))
        Object k = s.boundIntVar('fib$k' + QUANT.getAndIncrement())
        Object term = apply1(s, 'fib$', k)
        Object rhs = s.plus(apply1(s, 'fib$', s.minus(k, one)), apply1(s, 'fib$', s.minus(k, two)))
        s.assertExpr(s.forall([k], s.implies(s.ge(k, two), s.eq(term, rhs)), [term]))
    }

    /** trib (fibfib): base 0/0/1; step ∀k. k>=3 ⟹ trib(k)==trib(k-1)+trib(k-2)+trib(k-3). */
    private static void tribAxioms(TheoryApi api) {
        if (!api.axiomsOnce('numtheory.trib')) return
        SmtSession s = api.session
        Object zero = s.intLit(0L), one = s.intLit(1L), two = s.intLit(2L), three = s.intLit(3L)
        s.assertExpr(s.eq(apply1(s, 'trib$', zero), zero))
        s.assertExpr(s.eq(apply1(s, 'trib$', one), zero))
        s.assertExpr(s.eq(apply1(s, 'trib$', two), one))
        Object k = s.boundIntVar('trib$k' + QUANT.getAndIncrement())
        Object term = apply1(s, 'trib$', k)
        Object rhs = s.plus(s.plus(apply1(s, 'trib$', s.minus(k, one)),
                                   apply1(s, 'trib$', s.minus(k, two))),
                            apply1(s, 'trib$', s.minus(k, three)))
        s.assertExpr(s.forall([k], s.implies(s.ge(k, three), s.eq(term, rhs)), [term]))
    }

    /** tetra (fib4): base 0/0/2/0; step ∀k. k>=4 ⟹ tetra(k)==Σ tetra(k-1..k-4). */
    private static void tetraAxioms(TheoryApi api) {
        if (!api.axiomsOnce('numtheory.tetra')) return
        SmtSession s = api.session
        Object zero = s.intLit(0L), one = s.intLit(1L), two = s.intLit(2L)
        Object three = s.intLit(3L), four = s.intLit(4L)
        s.assertExpr(s.eq(apply1(s, 'tetra$', zero), zero))
        s.assertExpr(s.eq(apply1(s, 'tetra$', one), zero))
        s.assertExpr(s.eq(apply1(s, 'tetra$', two), two))
        s.assertExpr(s.eq(apply1(s, 'tetra$', three), zero))
        Object k = s.boundIntVar('tetra$k' + QUANT.getAndIncrement())
        Object term = apply1(s, 'tetra$', k)
        Object rhs = s.plus(s.plus(s.plus(apply1(s, 'tetra$', s.minus(k, one)),
                                          apply1(s, 'tetra$', s.minus(k, two))),
                                   apply1(s, 'tetra$', s.minus(k, three))),
                            apply1(s, 'tetra$', s.minus(k, four)))
        s.assertExpr(s.forall([k], s.implies(s.ge(k, four), s.eq(term, rhs)), [term]))
    }

    /** Euclid: base ∀x. gcd(x,0)==x; step ∀x,y. y!=0 ⟹ gcd(x,y)==gcd(y, x%y); plus the non-zero theorem
     *  ∀x,y. (x!=0 ∨ y!=0) ⟹ gcd(x,y)!=0 (finite e-matching can't reach it for symbolic args; asserted so
     *  `a.intdiv(Gcd.of(a,b))` — the lcm idiom — discharges its divisor-non-zero obligation). */
    private static void gcdAxioms(TheoryApi api) {
        if (!api.axiomsOnce('numtheory.gcd')) return
        SmtSession s = api.session
        Object zero = s.intLit(0L)
        Object x = s.boundIntVar('gcd$x' + QUANT.getAndIncrement())
        Object baseTerm = apply2(s, 'gcd$', x, zero)
        s.assertExpr(s.forall([x], s.eq(baseTerm, x), [baseTerm]))
        Object sx = s.boundIntVar('gcd$x' + QUANT.getAndIncrement())
        Object sy = s.boundIntVar('gcd$y' + QUANT.getAndIncrement())
        Object stepTerm = apply2(s, 'gcd$', sx, sy)
        Object rhs = apply2(s, 'gcd$', sy, s.intRem(sx, sy))
        s.assertExpr(s.forall([sx, sy], s.implies(s.ne(sy, zero), s.eq(stepTerm, rhs)), [stepTerm]))
        Object nx = s.boundIntVar('gcd$x' + QUANT.getAndIncrement())
        Object ny = s.boundIntVar('gcd$y' + QUANT.getAndIncrement())
        Object nzTerm = apply2(s, 'gcd$', nx, ny)
        s.assertExpr(s.forall([nx, ny],
            s.implies(s.or([s.ne(nx, zero), s.ne(ny, zero)]), s.ne(nzTerm, zero)), [nzTerm]))
    }

    /** lcm: base ∀a. lcm(a,0)==0, ∀b. lcm(0,b)==0; the fundamental identity ∀a,b. lcm(a,b)*gcd(a,b)==a*b. */
    private static void lcmAxioms(TheoryApi api) {
        if (!api.axiomsOnce('numtheory.lcm')) return
        SmtSession s = api.session
        Object zero = s.intLit(0L)
        Object la = s.boundIntVar('lcm$a' + QUANT.getAndIncrement())
        Object lz = apply2(s, 'lcm$', la, zero)
        s.assertExpr(s.forall([la], s.eq(lz, zero), [lz]))
        Object lb = s.boundIntVar('lcm$b' + QUANT.getAndIncrement())
        Object zl = apply2(s, 'lcm$', zero, lb)
        s.assertExpr(s.forall([lb], s.eq(zl, zero), [zl]))
        Object pa = s.boundIntVar('lcm$a' + QUANT.getAndIncrement())
        Object pb = s.boundIntVar('lcm$b' + QUANT.getAndIncrement())
        Object lterm = apply2(s, 'lcm$', pa, pb)
        s.assertExpr(s.forall([pa, pb],
            s.eq(s.times(lterm, apply2(s, 'gcd$', pa, pb)), s.times(pa, pb)), [lterm]))
    }

    /** Bézout (Phase 204, math-comp egcdn): ∀m,n. m*bezU(m,n) + n*bezV(m,n) == gcd(m,n), triggered on
     *  the bezU$ term so the (nonlinear) identity is minted only for contracts that mention Bezout. */
    private static void bezoutAxioms(TheoryApi api) {
        if (!api.axiomsOnce('numtheory.bezout')) return
        SmtSession s = api.session
        Object m = s.boundIntVar('bez$m' + QUANT.getAndIncrement())
        Object n = s.boundIntVar('bez$n' + QUANT.getAndIncrement())
        Object u = apply2(s, 'bezU$', m, n)
        Object v = apply2(s, 'bezV$', m, n)
        s.assertExpr(s.forall([m, n],
            s.eq(s.plus(s.times(m, u), s.times(n, v)), apply2(s, 'gcd$', m, n)), [u]))
    }
}
