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

import com.microsoft.z3.ArithExpr
import com.microsoft.z3.ArrayExpr
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import com.microsoft.z3.FuncDecl
import com.microsoft.z3.IntExpr
import com.microsoft.z3.IntNum
import com.microsoft.z3.Model
import com.microsoft.z3.Params
import com.microsoft.z3.Pattern
import com.microsoft.z3.Solver
import com.microsoft.z3.Sort
import com.microsoft.z3.Status
import groovy.transform.CompileStatic

/**
 * Z3 implementation via the z3-turnkey distribution
 * (tools.aqua:z3-turnkey), which bundles native libraries for
 * linux/mac/windows on amd64 and aarch64. No system Z3 install needed.
 *
 * One Context per call to {@link #session()}; the spike doesn't try
 * to amortise solver state across call sites. Per-method timeouts
 * are configured here (2 seconds — generous for QF_LIA, tight enough
 * that NIA blow-ups don't hang the compiler).
 */
@CompileStatic
class Z3Backend implements SmtBackend {

    final int timeoutMs

    Z3Backend(int timeoutMs = 2000) {
        this.timeoutMs = timeoutMs
    }

    @Override
    SmtSession session() {
        Context ctx = new Context()
        Solver solver = ctx.mkSolver()
        Params p = ctx.mkParams()
        p.add("timeout", timeoutMs)
        solver.setParameters(p)
        new Z3Session(ctx, solver)
    }
}

@CompileStatic
class Z3Session implements SmtSession {

    private final Context ctx
    private final Solver solver
    private final Map<String, IntExpr> vars = [:]
    private final Map<String, BoolExpr> boolVars = [:]
    private final Map<String, FuncDecl> funcs = [:]
    private final Map<String, ArrayExpr> arrays = [:]

    Z3Session(Context ctx, Solver solver) {
        this.ctx = ctx
        this.solver = solver
    }

    @Override
    Object intVar(String name) {
        IntExpr cached = vars.get(name)
        if (cached != null) return cached
        IntExpr v = (IntExpr) ctx.mkIntConst(name)
        vars.put(name, v)
        v
    }

    @Override
    Object boolVar(String name) {
        BoolExpr cached = boolVars.get(name)
        if (cached != null) return cached
        BoolExpr v = (BoolExpr) ctx.mkBoolConst(name)
        boolVars.put(name, v)
        v
    }

    @Override
    Object uninterpretedFunc(String name, List<Object> intArgs) {
        String key = name + '/' + intArgs.size()
        FuncDecl fd = funcs.get(key)
        if (fd == null) {
            Sort[] domain = intArgs.collect { ctx.getIntSort() } as Sort[]
            fd = ctx.mkFuncDecl(name, domain, ctx.getIntSort())
            funcs.put(key, fd)
        }
        Expr[] a = intArgs.collect { (Expr) it } as Expr[]
        ctx.mkApp(fd, a)
    }

    @Override
    Object ite(Object cond, Object thenV, Object elseV) {
        ctx.mkITE((BoolExpr) cond, (Expr) thenV, (Expr) elseV)
    }

    @Override
    Object arrayVar(String name) {
        ArrayExpr cached = arrays.get(name)
        if (cached != null) return cached
        ArrayExpr v = (ArrayExpr) ctx.mkConst(name, ctx.mkArraySort(ctx.getIntSort(), ctx.getIntSort()))
        arrays.put(name, v)
        v
    }

    @Override Object select(Object arr, Object idx) { ctx.mkSelect((ArrayExpr) arr, (Expr) idx) }
    @Override Object store(Object arr, Object idx, Object val) { ctx.mkStore((ArrayExpr) arr, (Expr) idx, (Expr) val) }

    @Override Object boundIntVar(String name) { ctx.mkIntConst(name) }

    @Override
    Object forall(List<Object> bound, Object body, List<Object> triggers) {
        Expr[] b = bound.collect { (Expr) it } as Expr[]
        // weight 1, the given patterns, no no-patterns, no quantifier/skolem id.
        ctx.mkForall(b, (Expr) body, 1, patternsFor(triggers, b), (Expr[]) null, (com.microsoft.z3.Symbol) null, (com.microsoft.z3.Symbol) null)
    }

    @Override
    Object exists(List<Object> bound, Object body, List<Object> triggers) {
        Expr[] b = bound.collect { (Expr) it } as Expr[]
        ctx.mkExists(b, (Expr) body, 1, patternsFor(triggers, b), (Expr[]) null, (com.microsoft.z3.Symbol) null, (com.microsoft.z3.Symbol) null)
    }

    /**
     * One pattern per trigger term that actually mentions a bound variable. Seeing *any* such
     * {@code (select arr ·)} ground term lets Z3 instantiate — more robust for matrices with several
     * selects (sortedness uses {@code a[i]} and {@code a[i+1]}) than one conjunctive multi-pattern.
     * A trigger with no bound variable (e.g. the ground {@code a[k]} in {@code any { it == a[k] }})
     * is degenerate — Z3 rejects/ignores it — so it is dropped; null when none remain (auto-pattern).
     */
    private Pattern[] patternsFor(List<Object> triggers, Expr[] bound) {
        if (triggers == null || triggers.isEmpty()) return null
        List<Pattern> pats = new ArrayList<Pattern>()
        for (Object t : triggers) {
            if (mentions((Expr) t, bound)) pats.add(ctx.mkPattern((Expr) t))
        }
        pats.isEmpty() ? null : (pats as Pattern[])
    }

    /** True if {@code term} contains any of the {@code vars} as a subterm. */
    private static boolean mentions(Expr term, Expr[] vars) {
        for (Expr v : vars) {
            if (term.equals(v)) return true
        }
        if (term.isApp()) {
            for (Expr a : term.getArgs()) {
                if (mentions(a, vars)) return true
            }
        }
        false
    }

    @Override Object intLit(long n) { ctx.mkInt(n) }
    @Override Object plus(Object a, Object b)  { ctx.mkAdd((ArithExpr) a, (ArithExpr) b) }
    @Override Object minus(Object a, Object b) { ctx.mkSub((ArithExpr) a, (ArithExpr) b) }
    @Override Object times(Object a, Object b) { ctx.mkMul((ArithExpr) a, (ArithExpr) b) }
    @Override Object neg(Object a)             { ctx.mkUnaryMinus((ArithExpr) a) }

    @Override Object eq(Object a, Object b) { ctx.mkEq((Expr) a, (Expr) b) }
    @Override Object ne(Object a, Object b) { ctx.mkNot(ctx.mkEq((Expr) a, (Expr) b)) }
    @Override Object lt(Object a, Object b) { ctx.mkLt((ArithExpr) a, (ArithExpr) b) }
    @Override Object le(Object a, Object b) { ctx.mkLe((ArithExpr) a, (ArithExpr) b) }
    @Override Object gt(Object a, Object b) { ctx.mkGt((ArithExpr) a, (ArithExpr) b) }
    @Override Object ge(Object a, Object b) { ctx.mkGe((ArithExpr) a, (ArithExpr) b) }

    @Override
    Object and(List<Object> xs) {
        if (xs.isEmpty()) return ctx.mkTrue()
        if (xs.size() == 1) return xs[0]
        BoolExpr[] arr = xs.collect { (BoolExpr) it } as BoolExpr[]
        ctx.mkAnd(arr)
    }

    @Override
    Object or(List<Object> xs) {
        if (xs.isEmpty()) return ctx.mkFalse()
        if (xs.size() == 1) return xs[0]
        BoolExpr[] arr = xs.collect { (BoolExpr) it } as BoolExpr[]
        ctx.mkOr(arr)
    }

    @Override Object not(Object x) { ctx.mkNot((BoolExpr) x) }
    @Override Object implies(Object a, Object b) { ctx.mkImplies((BoolExpr) a, (BoolExpr) b) }
    @Override Object boolLit(boolean b) { b ? ctx.mkTrue() : ctx.mkFalse() }

    @Override
    void assertExpr(Object boolExpr) {
        solver.add((BoolExpr) boolExpr)
    }

    @Override
    CheckResult check() {
        Status status = solver.check()
        if (status == Status.UNSATISFIABLE) {
            return CheckResult.verified()
        }
        if (status == Status.UNKNOWN) {
            return CheckResult.unknown(solver.getReasonUnknown())
        }
        // SATISFIABLE: extract counterexample for variables we declared
        Model m = solver.getModel()
        Map<String, Long> ce = [:]
        vars.each { name, var ->
            Expr v = m.evaluate(var, false)
            if (v instanceof IntNum) {
                ce[name] = ((IntNum) v).getInt64()
            }
        }
        // Boolean vars (e.g. the `recv?null` nullity flags) — recorded as 0/1 when the model
        // pins them, so the failing-call reconstruction (Phase 9) can render a null argument.
        boolVars.each { name, var ->
            Expr v = m.evaluate(var, false)
            if (v.isTrue()) ce[name] = 1L
            else if (v.isFalse()) ce[name] = 0L
        }
        // Array contents the model committed to (Phase 9 slice 2): `recv[k]` for k in [0, size).
        // `model_completion = false` so only *constrained* elements are pinned — unconstrained ones
        // come back as the select term and are skipped, keeping the repro free of irrelevant values.
        arrays.each { String name, ArrayExpr arr ->
            Long szL = ce.get(name + '.size')
            if (szL == null) return
            long sz = szL
            if (sz <= 0L || sz > 16L) return          // cap enumeration; huge/zero sizes stay size-filled
            for (int k = 0; k < sz; k++) {
                Expr ev = m.evaluate((Expr) select(arr, ctx.mkInt(k)), false)
                if (ev instanceof IntNum) ce[name + '[' + k + ']'] = ((IntNum) ev).getInt64()
            }
        }
        CheckResult.refuted(ce)
    }

    @Override
    void close() {
        ctx.close()
    }
}
