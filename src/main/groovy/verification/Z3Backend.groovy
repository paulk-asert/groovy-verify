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
    private final Map<String, ArrayExpr> sets = [:]
    /** Phase 27 — uninterpreted sorts keyed by source-level name (e.g. "String", "Color"). */
    private final Map<String, Sort> sorts = [:]
    /**
     * Phase 27 — variables of an arbitrary sort, keyed by {@code name + ':' + sortName}. A
     * {@code String} parameter {@code s} and a {@code Color} parameter {@code s} would otherwise
     * collide; the sort tag disambiguates while keeping the displayed name clean.
     */
    private final Map<String, Expr> sortedVars = [:]
    /**
     * Phase 27 — interned literals keyed by {@code sortName + ':' + literalKey}. Each new mint
     * within a sort gets pairwise-distinct assertions against every previously-minted constant
     * of that sort (see {@link #sortLiteralsBySort}).
     */
    private final Map<String, Expr> sortedLits = [:]
    /** All literals minted per sort, for the pairwise-distinct cascade in {@link #litOfSort}. */
    private final Map<String, List<Expr>> sortLiteralsBySort = [:]
    /**
     * Reverse lookup: the const-name a non-Int literal was minted under (e.g.
     * {@code "String!val_admin"}) → the source-level literal key ({@code "admin"}).
     * Used in {@link #check} to map a model's non-Int value back to the literal it
     * represents, populating {@link CheckResult#sortedCounterexample} (Phase 27
     * step 9 — counterexample rendering for non-Int parameters).
     */
    private final Map<String, String> literalKeyByConstName = [:]
    /** Phase 27 — arrays of arbitrary key/value sorts, keyed by {@code name + ':' + keySort + '->' + valSort}. */
    private final Map<String, ArrayExpr> sortedArrays = [:]

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

    // ---- Phase 27 — non-Int element sorts ---------------------------------------------------

    @Override
    Object intSort() {
        ctx.getIntSort()
    }

    @Override
    Object declareSort(String name) {
        Sort cached = sorts.get(name)
        if (cached != null) return cached
        Sort s = ctx.mkUninterpretedSort(name)
        sorts.put(name, s)
        s
    }

    @Override
    Object varOfSort(String name, Object sort) {
        // Int parameters keep the existing intVar storage so model extraction (which iterates
        // `vars`) still pins their values for counterexamples.
        if (sort == ctx.getIntSort()) return intVar(name)
        Sort sortHandle = (Sort) sort
        String key = name + ':' + sortHandle.getName()
        Expr cached = sortedVars.get(key)
        if (cached != null) return cached
        Expr v = ctx.mkConst(name, sortHandle)
        sortedVars.put(key, v)
        v
    }

    @Override
    Object litOfSort(Object sort, String literalKey) {
        if (sort == ctx.getIntSort()) {
            // Int literals: parse the key as a long. The backend already exposes intLit for the
            // common case; this branch keeps the interface uniform when the caller doesn't know
            // statically whether the element sort is Int or uninterpreted.
            return ctx.mkInt(Long.parseLong(literalKey))
        }
        Sort sortHandle = (Sort) sort
        String sortName = sortHandle.getName().toString()
        String key = sortName + ':' + literalKey
        Expr cached = sortedLits.get(key)
        if (cached != null) return cached
        // Mint a fresh constant whose displayed name encodes both sort and literal, so a
        // counterexample reading "String!val_admin" is traceable back to the source "admin".
        String constName = sortName + '!val_' + literalKey
        Expr v = ctx.mkConst(constName, sortHandle)
        sortedLits.put(key, v)
        literalKeyByConstName.put(constName, literalKey)   // reverse lookup for model rendering
        // Lazy pairwise-distinct: assert the new constant is distinct from every previously-minted
        // literal of this sort. Cumulative cost is O(n^2) per sort; fine for the dozens-of-literals
        // scale typical for set/map element domains in a single compilation unit.
        List<Expr> bucket = sortLiteralsBySort.get(sortName)
        if (bucket == null) {
            bucket = new ArrayList<Expr>()
            sortLiteralsBySort.put(sortName, bucket)
        }
        for (Expr prior : bucket) {
            solver.add((BoolExpr) ctx.mkNot(ctx.mkEq(v, prior)))
        }
        bucket.add(v)
        v
    }

    @Override
    Object arrayVarOfSort(String name, Object keySort, Object valSort) {
        // Int->Int arrays continue to use the existing storage so the counterexample model walk
        // (which iterates `arrays`) still pins their contents. Anything else lives in sortedArrays.
        if (keySort == ctx.getIntSort() && valSort == ctx.getIntSort()) return arrayVar(name)
        Sort k = (Sort) keySort
        Sort v = (Sort) valSort
        String key = name + ':' + k.getName() + '->' + v.getName()
        ArrayExpr cached = sortedArrays.get(key)
        if (cached != null) return cached
        ArrayExpr arr = (ArrayExpr) ctx.mkConst(name, ctx.mkArraySort(k, v))
        sortedArrays.put(key, arr)
        arr
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

    private FuncDecl countFn
    @Override
    Object count(Object arr, Object v) {
        if (countFn == null) {
            Sort arrSort = ctx.mkArraySort(ctx.getIntSort(), ctx.getIntSort())
            countFn = ctx.mkFuncDecl('count$', [arrSort, ctx.getIntSort()] as Sort[], ctx.getIntSort())
        }
        ctx.mkApp(countFn, (Expr) arr, (Expr) v)
    }

    @Override
    Object setVar(String name) {
        ArrayExpr cached = sets.get(name)
        if (cached != null) return cached
        // A set is a characteristic array Int -> Int (1 = member, 0 = absent), sharing the
        // array sort so membership/add/remove reuse select/store and Z3's array theory.
        ArrayExpr v = (ArrayExpr) ctx.mkConst(name, ctx.mkArraySort(ctx.getIntSort(), ctx.getIntSort()))
        sets.put(name, v)
        v
    }

    /**
     * Per-element-sort cardinality functions (Phase 27). A {@code Set<Int>}'s {@code card$Int} and a
     * {@code Set<String>}'s {@code card$String!Sort} are distinct uninterpreted functions, since each
     * takes a differently-sorted array. Keyed by the element sort's string name.
     */
    private final Map<String, FuncDecl> cardFnsByElemSort = [:]
    @Override
    Object setCard(Object set) {
        ArrayExpr arr = (ArrayExpr) set
        Sort elemSort = arr.getSort().getDomain()
        String key = elemSort.getName().toString()
        FuncDecl fd = cardFnsByElemSort.get(key)
        if (fd == null) {
            Sort arrSort = ctx.mkArraySort(elemSort, ctx.getIntSort())
            fd = ctx.mkFuncDecl('card$' + key, [arrSort] as Sort[], ctx.getIntSort())
            cardFnsByElemSort.put(key, fd)
        }
        ctx.mkApp(fd, (Expr) set)
    }

    /** Per-element-sort bounded-count functions (Phase 27, parallel structure to {@link #cardFnsByElemSort}). */
    private final Map<String, FuncDecl> bcountFnsByElemSort = [:]
    @Override
    Object setCount(Object set, Object k) {
        ArrayExpr arr = (ArrayExpr) set
        Sort elemSort = arr.getSort().getDomain()
        String key = elemSort.getName().toString()
        FuncDecl fd = bcountFnsByElemSort.get(key)
        if (fd == null) {
            Sort arrSort = ctx.mkArraySort(elemSort, ctx.getIntSort())
            fd = ctx.mkFuncDecl('bcount$' + key, [arrSort, ctx.getIntSort()] as Sort[], ctx.getIntSort())
            bcountFnsByElemSort.put(key, fd)
        }
        ctx.mkApp(fd, (Expr) set, (Expr) k)
    }

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
        // Phase 27 step 9 — non-Int parameter / variable values from the model. A String parameter
        // pinned to "admin" appears in the model as our minted constant `String!val_admin`; the
        // const-name reverse lookup recovers the literal key "admin". A model value that doesn't
        // match any of our minted constants (Z3 invented a fresh interpretation) is dropped — the
        // renderer falls back to the default {@code ""} / {@code null}.
        // Phase 27 step 9 — for each non-Int variable, check equality-under-model against every
        // interned literal of the same sort. Z3 may assign the variable a synthetic constant
        // (`String!val!1`) instead of one of our minted constants (`String!val_admin`); the
        // model still satisfies the constraint that they're equal, which equality-evaluation
        // recovers. Const-name string-matching alone misses these synthetic-name cases.
        Map<String, String> sce = [:]
        sortedVars.each { String key, Expr var ->
            com.microsoft.z3.Sort varSort = var.getSort()
            Expr mv = m.evaluate(var, false)
            int vColon = key.indexOf(':')
            String name = vColon >= 0 ? key.substring(0, vColon) : key
            for (Map.Entry<String, Expr> entry : sortedLits.entrySet()) {
                Expr litExpr = entry.value
                if (litExpr.getSort() != varSort) continue
                Expr eqResult = m.evaluate(ctx.mkEq(mv, litExpr), true)
                if (eqResult.isTrue()) {
                    String litKey = entry.key
                    int colon = litKey.indexOf(':')
                    String literalKey = colon >= 0 ? litKey.substring(colon + 1) : litKey
                    sce[name] = literalKey
                    break
                }
            }
        }
        CheckResult r = CheckResult.refuted(ce)
        r.sortedCounterexample = sce
        r
    }

    @Override
    void close() {
        ctx.close()
    }
}
