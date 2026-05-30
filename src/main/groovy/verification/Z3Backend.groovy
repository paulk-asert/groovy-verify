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
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import com.microsoft.z3.IntExpr
import com.microsoft.z3.IntNum
import com.microsoft.z3.Model
import com.microsoft.z3.Params
import com.microsoft.z3.Solver
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
        CheckResult.refuted(ce)
    }

    @Override
    void close() {
        ctx.close()
    }
}
