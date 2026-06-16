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
import com.microsoft.z3.BitVecExpr
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import com.microsoft.z3.FPExpr
import com.microsoft.z3.FPRMExpr
import com.microsoft.z3.FPSort
import com.microsoft.z3.FuncDecl
import com.microsoft.z3.DatatypeSort
import com.microsoft.z3.Constructor
import com.microsoft.z3.IntExpr
import com.microsoft.z3.IntNum
import java.math.BigInteger
import com.microsoft.z3.Model
import com.microsoft.z3.SeqExpr
import com.microsoft.z3.Params
import com.microsoft.z3.Pattern
import com.microsoft.z3.Solver
import com.microsoft.z3.Sort
import com.microsoft.z3.Status
import groovy.transform.CompileStatic

import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicLong

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
        new Z3Session(ctx, solver, timeoutMs)
    }

    /**
     * Phase 34 — process-wide VC cache. Two checks built from the same set of asserted Z3
     * expressions (compared structurally via {@link com.microsoft.z3.Expr#toString}) and the
     * same timeout produce the same {@link CheckResult}, so we look up before calling the
     * solver. Within {@code ./gradlew verify} (one JVM, ~250 tests, many shared trivial VCs
     * for arithmetic/bounds/null obligations), the suite gains a high hit rate without any
     * loss of soundness — counterexamples are pure {@code Map<String, Long>} / {@code String}
     * data, so cached refutations re-render correctly in any session whose declared variables
     * carry the cached names.
     */
    static final Map<String, CheckResult> vcCache = new ConcurrentHashMap<>()
    private static final AtomicLong vcHits = new AtomicLong()
    private static final AtomicLong vcMisses = new AtomicLong()
    static long vcCacheHits() { vcHits.get() }
    static long vcCacheMisses() { vcMisses.get() }
    static int  vcCacheSize()  { vcCache.size() }
    static void resetVCCacheStats() { vcHits.set(0); vcMisses.set(0) }
    static void recordVCCacheHit()   { vcHits.incrementAndGet() }
    static void recordVCCacheMiss()  { vcMisses.incrementAndGet() }
}

@CompileStatic
class Z3Session implements SmtSession {

    private final Context ctx
    private final Solver solver
    private Model lastModel    // Phase 126 — retained after a SAT check so callers can eval extra terms (array elements)
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

    /**
     * Phase 34 — assertion fingerprint, lazily hashed in {@link #check}. We keep the
     * {@link BoolExpr} handles (cheap — they're shared with the solver) rather than
     * computing {@code toString} eagerly on every {@code assertExpr}, since the encoder
     * may build dozens of intermediate constraints before any check fires.
     */
    private final List<BoolExpr> assertedExprs = new ArrayList<BoolExpr>()
    private final int timeoutMs

    Z3Session(Context ctx, Solver solver, int timeoutMs) {
        this.ctx = ctx
        this.solver = solver
        this.timeoutMs = timeoutMs
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
    Object boolSort() {
        ctx.getBoolSort()
    }

    /**
     * Phase 47 — Z3's native String sort, cached on first request. Replaces the Phase-27
     * uninterpreted {@code String!Sort} so {@code str.prefixof}/{@code str.len}/{@code str.at}/
     * etc. fire through the seq theory directly. Sort identity (reference equality) is the
     * discriminator used elsewhere in this file to route String-handling separately from
     * uninterpreted sorts (Enums still use the uninterpreted path).
     */
    private Sort cachedStringSort
    private Sort stringSort() {
        if (cachedStringSort == null) {
            cachedStringSort = ctx.mkStringSort()
        }
        cachedStringSort
    }

    @Override
    Object declareSort(String name) {
        if (name == 'String') return stringSort()
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
        // Phase 47 — Z3 native String sort goes through sortedVars too, but with a stable
        // 'String' tag rather than {@code sortHandle.getName()} (which may render as a long
        // {@code "Seq Char"}-shape symbol depending on Z3 version).
        String tag = (sort == stringSort()) ? 'String' : sortHandle.getName().toString()
        String key = name + ':' + tag
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
        if (sort == stringSort()) {
            // Phase 47 — Z3 native string literal. {@code mkString} returns the canonical
            // interned form, so distinctness ({@code "a" != "b"}) is a theory consequence — no
            // pairwise-distinct cascade required. Length and per-position content
            // ({@code len("hello") == 5}, {@code at("hello", 0) == "h"}) are theory consequences
            // too — no mint-time pinning required. This replaces the Phase-27 (cascade) +
            // Phase-46b (length pin) + Phase-46e (char pin, capped at 64) machinery in one move.
            Expr lit = ctx.mkString(literalKey)
            // Phase 47g/47i — track minted literals for case-folding and reverse pinning (only when
            // the relevant functions are in play). {@link #pinCaseLiteral} / {@link #pinReverseLiteral}
            // compute and assert the upper/lower/reversed form at mint time so
            // {@code "Hello".toUpperCase() == "HELLO"} and {@code "abc".reverse() == "cba"} fold.
            if (stringLiteralKeys.add(literalKey)) {
                if (toUpperFn != null || toLowerFn != null) pinCaseLiteral(literalKey, lit)
                if (reverseFn != null) pinReverseLiteral(literalKey, lit)
            }
            return lit
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
    Object arraySort(Object keySort, Object valSort) {
        ctx.mkArraySort((Sort) keySort, (Sort) valSort)
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

    // Phase B (carrier model) — a single-field immutable wrapper carrier modelled as a one-constructor Z3
    // datatype. The selector/constructor round-trips (`content(mk(x)) == x`, `mk(content(c)) == c`) are
    // datatype theorems Z3 derives for free — no manual axioms, no quantifier triggers.
    private final Map<String, DatatypeSort> wrapperSorts = [:]
    private final Map<String, FuncDecl> wrapperCtor = [:]
    private final Map<String, FuncDecl> wrapperSel = [:]

    @Override
    Object wrapperSort(String typeName, Object contentSort) {
        DatatypeSort cached = wrapperSorts.get(typeName)
        if (cached != null) return cached
        Constructor ctor = ctx.mkConstructor('mk$' + typeName, 'is$' + typeName,
            ['content$' + typeName] as String[], [(Sort) contentSort] as Sort[], [0] as int[])
        DatatypeSort dt = ctx.mkDatatypeSort(typeName, [ctor] as Constructor[])
        wrapperSorts.put(typeName, dt)
        wrapperCtor.put(typeName, dt.getConstructors()[0])
        wrapperSel.put(typeName, dt.getAccessors()[0][0])
        dt
    }

    @Override
    Object wrapperUnit(String typeName, Object contentSort, Object value) {
        wrapperSort(typeName, contentSort)
        ctx.mkApp(wrapperCtor.get(typeName), (Expr) value)
    }

    @Override
    Object wrapperContent(String typeName, Object contentSort, Object carrier) {
        wrapperSort(typeName, contentSort)
        ctx.mkApp(wrapperSel.get(typeName), (Expr) carrier)
    }

    // Phase M-A — general N-constructor algebraic datatypes (Some(v) | None, …). Decls are read back from the
    // DatatypeSort by index after creation (constructors[i], recognizers[i], accessors[i][j]).
    private final Map<String, DatatypeSort> dtSorts = [:]
    private final Map<String, Integer> dtCtorIdx = [:]    // 'type/ctor'        -> constructor index
    private final Map<String, Integer> dtFieldIdx = [:]   // 'type/ctor/field'  -> field index

    @Override
    Object datatypeSort(String typeName, List<Object[]> constructors) {
        DatatypeSort cached = dtSorts.get(typeName)
        if (cached != null) return cached
        Constructor[] ctors = new Constructor[constructors.size()]
        for (int i = 0; i < constructors.size(); i++) {
            Object[] c = constructors.get(i)
            String ctorName = (String) c[0]
            List<Object[]> fields = (List<Object[]>) c[1]
            int n = fields.size()
            String[] fieldNames = new String[n]
            Sort[] fieldSorts = new Sort[n]
            int[] sortRefs = new int[n]
            for (int j = 0; j < n; j++) {
                fieldNames[j] = (String) fields.get(j)[0]
                fieldSorts[j] = (Sort) fields.get(j)[1]
                sortRefs[j] = 0
                dtFieldIdx.put(typeName + '/' + ctorName + '/' + fieldNames[j], j)
            }
            ctors[i] = ctx.mkConstructor(ctorName, 'is$' + ctorName, fieldNames, fieldSorts, sortRefs)
            dtCtorIdx.put(typeName + '/' + ctorName, i)
        }
        DatatypeSort dt = ctx.mkDatatypeSort(typeName, ctors)
        dtSorts.put(typeName, dt)
        dt
    }

    @Override
    Object datatypeConstruct(String typeName, String ctorName, List<Object> args) {
        FuncDecl ctor = dtSorts.get(typeName).getConstructors()[dtCtorIdx.get(typeName + '/' + ctorName)]
        ctx.mkApp(ctor, args.collect { (Expr) it } as Expr[])
    }

    @Override
    Object datatypeSelect(String typeName, String ctorName, String fieldName, Object carrier) {
        int ci = dtCtorIdx.get(typeName + '/' + ctorName)
        int fi = dtFieldIdx.get(typeName + '/' + ctorName + '/' + fieldName)
        ctx.mkApp(dtSorts.get(typeName).getAccessors()[ci][fi], (Expr) carrier)
    }

    @Override
    Object datatypeRecognize(String typeName, String ctorName, Object carrier) {
        FuncDecl rec = dtSorts.get(typeName).getRecognizers()[dtCtorIdx.get(typeName + '/' + ctorName)]
        ctx.mkApp(rec, (Expr) carrier)
    }

    // Phase M-B — the distinguished `null` element per value sort (mint-once).
    private final Map<String, Expr> nullVals = [:]
    @Override
    Object nullValue(Object valueSort) {
        Sort sort = (Sort) valueSort
        String tag = (sort == stringSort()) ? 'String' : sort.getName().toString()
        Expr cached = nullVals.get(tag)
        if (cached != null) return cached
        Expr v = ctx.mkConst('null$' + tag, sort)
        nullVals.put(tag, v)
        v
    }

    @Override
    Object applyUF(String name, List<Object> args, Object rangeSort) {
        Expr[] a = args.collect { (Expr) it } as Expr[]
        Sort[] domain = a.collect { it.getSort() } as Sort[]
        Sort range = (Sort) rangeSort
        // Key by the full signature so a re-declaration always matches the cached decl's sorts.
        String key = name + '/' + domain.collect { it.toString() }.join(',') + '->' + range.toString()
        FuncDecl fd = funcs.get(key)
        if (fd == null) {
            fd = ctx.mkFuncDecl(name, domain, range)
            funcs.put(key, fd)
        }
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

    @Override
    Object constIntArray(Object value) {
        ctx.mkConstArray(ctx.getIntSort(), (Expr) value)
    }

    // --- Bitwise / shift via 32-bit two's-complement bit-vectors (Java `int` width) ---
    private BitVecExpr toBV32(Object e) { ctx.mkInt2BV(32, (IntExpr) e) }          // int → 32-bit BV (mod 2^32)
    private Object fromBV(BitVecExpr b) { ctx.mkBV2Int(b, true) }                  // BV → signed Int
    private BitVecExpr maskShift(BitVecExpr s) {                                   // Java masks the shift count to 5 bits
        ctx.mkBVAND(s, (BitVecExpr) ctx.mkNumeral(31, ctx.mkBitVecSort(32)))
    }
    @Override Object bvAnd(Object a, Object b) { fromBV(ctx.mkBVAND(toBV32(a), toBV32(b))) }
    @Override Object bvOr(Object a, Object b)  { fromBV(ctx.mkBVOR(toBV32(a), toBV32(b))) }
    @Override Object bvXor(Object a, Object b) { fromBV(ctx.mkBVXOR(toBV32(a), toBV32(b))) }
    @Override Object bvShl(Object a, Object b) { fromBV(ctx.mkBVSHL(toBV32(a), maskShift(toBV32(b)))) }
    @Override Object bvShr(Object a, Object b) { fromBV(ctx.mkBVASHR(toBV32(a), maskShift(toBV32(b)))) }  // arithmetic >>

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

    private FuncDecl bcountFn
    @Override
    Object bcount(Object arr, Object v, Object lo, Object hi) {
        if (bcountFn == null) {
            Sort arrSort = ctx.mkArraySort(ctx.getIntSort(), ctx.getIntSort())
            bcountFn = ctx.mkFuncDecl('bcountArr$',
                [arrSort, ctx.getIntSort(), ctx.getIntSort(), ctx.getIntSort()] as Sort[],
                ctx.getIntSort())
        }
        ctx.mkApp(bcountFn, (Expr) arr, (Expr) v, (Expr) lo, (Expr) hi)
    }

    private FuncDecl sumFn
    @Override
    Object sum(Object arr, Object lo, Object hi) {
        if (sumFn == null) {
            Sort arrSort = ctx.mkArraySort(ctx.getIntSort(), ctx.getIntSort())
            sumFn = ctx.mkFuncDecl('sumArr$',
                [arrSort, ctx.getIntSort(), ctx.getIntSort()] as Sort[],
                ctx.getIntSort())
        }
        ctx.mkApp(sumFn, (Expr) arr, (Expr) lo, (Expr) hi)
    }

    // Phase 70 — Real-element aggregation (List<BigDecimal>): a Real-codomain sum over Array Int Real.
    @Override Object realSort() { ctx.getRealSort() }
    @Override boolean isReal(Object handle) { ((Expr) handle).getSort().equals(ctx.getRealSort()) }
    @Override boolean isInt(Object handle) { ((Expr) handle).getSort().equals(ctx.getIntSort()) }
    @Override boolean isSeq(Object handle) { ((Expr) handle).getSort().equals(stringSort()) }
    @Override boolean isBool(Object handle) { ((Expr) handle).getSort().equals(ctx.getBoolSort()) }
    @Override String evalDisplay(Object handle) {
        if (lastModel == null || handle == null) return null
        try {
            Expr v = lastModel.evaluate((Expr) handle, true)
            if (v == null) return null
            if (v.isString()) return '"' + cleanZ3String(v.getString()) + '"'
            if (v instanceof IntNum) return Long.toString(clampInt64((IntNum) v))
            return null
        } catch (Throwable ignored) {
            return null
        }
    }

    /** Z3's {@code getString()} renders non-ASCII as literal {@code \\u{HHHH}} escapes, and {@code mkString}
     *  round-trips a supplementary character as a {@code [code-point, low-surrogate]} pair — so decode the
     *  escapes and drop the artifact lone surrogates, recovering the real text (e.g. the actual emoji). */
    private static String cleanZ3String(String s) {
        if (s == null || s.indexOf('\\') < 0) return s
        StringBuilder out = new StringBuilder()
        int i = 0
        while (i < s.length()) {
            if (s.charAt(i) == '\\' && i + 2 < s.length() && s.charAt(i + 1) == 'u' && s.charAt(i + 2) == '{') {
                int close = s.indexOf('}', i + 3)
                if (close > i + 3) {
                    try {
                        int cp = Integer.parseInt(s.substring(i + 3, close), 16)
                        if (cp < 0xD800 || cp > 0xDFFF) out.appendCodePoint(cp)   // skip lone surrogate artifacts
                        i = close + 1
                        continue
                    } catch (NumberFormatException ignored) {
                    }
                }
            }
            out.append(s.charAt(i))
            i++
        }
        out.toString()
    }
    private FuncDecl sumRealFn
    @Override
    Object sumReal(Object arr, Object lo, Object hi) {
        if (sumRealFn == null) {
            Sort arrSort = ctx.mkArraySort(ctx.getIntSort(), ctx.getRealSort())
            sumRealFn = ctx.mkFuncDecl('sumRealArr$',
                [arrSort, ctx.getIntSort(), ctx.getIntSort()] as Sort[],
                ctx.getRealSort())
        }
        ctx.mkApp(sumRealFn, (Expr) arr, (Expr) lo, (Expr) hi)
    }

    // Phase 73 — IEEE-754 floating point. Arithmetic rounds round-nearest-ties-to-even (the JVM default).
    private FPRMExpr rneMode
    private FPRMExpr rne() { if (rneMode == null) rneMode = ctx.mkFPRoundNearestTiesToEven(); rneMode }
    private FPSort fp(boolean isDouble) { isDouble ? ctx.mkFPSortDouble() : ctx.mkFPSortSingle() }
    @Override Object fpSort(boolean isDouble) { fp(isDouble) }
    @Override Object fpLit(double v, boolean isDouble) { ctx.mkFP(v, fp(isDouble)) }
    @Override Object fpVar(String name, boolean isDouble) { ctx.mkConst(name, fp(isDouble)) }
    @Override Object fpAdd(Object a, Object b) { ctx.mkFPAdd(rne(), (FPExpr) a, (FPExpr) b) }
    @Override Object fpSub(Object a, Object b) { ctx.mkFPSub(rne(), (FPExpr) a, (FPExpr) b) }
    @Override Object fpMul(Object a, Object b) { ctx.mkFPMul(rne(), (FPExpr) a, (FPExpr) b) }
    @Override Object fpDiv(Object a, Object b) { ctx.mkFPDiv(rne(), (FPExpr) a, (FPExpr) b) }
    @Override Object fpNeg(Object a) { ctx.mkFPNeg((FPExpr) a) }
    @Override Object fpSqrt(Object a) { ctx.mkFPSqrt(rne(), (FPExpr) a) }
    @Override Object fpAbs(Object a) { ctx.mkFPAbs((FPExpr) a) }
    @Override Object fpEq(Object a, Object b) { ctx.mkFPEq((FPExpr) a, (FPExpr) b) }
    @Override Object fpLt(Object a, Object b) { ctx.mkFPLt((FPExpr) a, (FPExpr) b) }
    @Override Object fpLeq(Object a, Object b) { ctx.mkFPLEq((FPExpr) a, (FPExpr) b) }
    @Override Object fpGt(Object a, Object b) { ctx.mkFPGt((FPExpr) a, (FPExpr) b) }
    @Override Object fpGeq(Object a, Object b) { ctx.mkFPGEq((FPExpr) a, (FPExpr) b) }
    @Override Object fpIsNaN(Object a) { ctx.mkFPIsNaN((FPExpr) a) }
    @Override Object fpIsInfinite(Object a) { ctx.mkFPIsInfinite((FPExpr) a) }
    @Override boolean isFp(Object handle) { ((Expr) handle).getSort() instanceof FPSort }

    private FuncDecl prodFn
    @Override
    Object prod(Object arr, Object lo, Object hi) {
        if (prodFn == null) {
            Sort arrSort = ctx.mkArraySort(ctx.getIntSort(), ctx.getIntSort())
            prodFn = ctx.mkFuncDecl('prodArr$',
                [arrSort, ctx.getIntSort(), ctx.getIntSort()] as Sort[],
                ctx.getIntSort())
        }
        ctx.mkApp(prodFn, (Expr) arr, (Expr) lo, (Expr) hi)
    }

    private FuncDecl fibFn
    @Override
    Object fib(Object k) {
        if (fibFn == null) {
            fibFn = ctx.mkFuncDecl('fib$', [ctx.getIntSort()] as Sort[], ctx.getIntSort())
        }
        ctx.mkApp(fibFn, (Expr) k)
    }

    private FuncDecl tribFn
    @Override
    Object trib(Object k) {
        if (tribFn == null) {
            tribFn = ctx.mkFuncDecl('trib$', [ctx.getIntSort()] as Sort[], ctx.getIntSort())
        }
        ctx.mkApp(tribFn, (Expr) k)
    }

    private FuncDecl gcdFn
    @Override
    Object gcd(Object a, Object b) {
        if (gcdFn == null) {
            gcdFn = ctx.mkFuncDecl('gcd$', [ctx.getIntSort(), ctx.getIntSort()] as Sort[], ctx.getIntSort())
        }
        ctx.mkApp(gcdFn, (Expr) a, (Expr) b)
    }

    private FuncDecl lcmFn
    @Override
    Object lcm(Object a, Object b) {
        if (lcmFn == null) {
            lcmFn = ctx.mkFuncDecl('lcm$', [ctx.getIntSort(), ctx.getIntSort()] as Sort[], ctx.getIntSort())
        }
        ctx.mkApp(lcmFn, (Expr) a, (Expr) b)
    }

    private FuncDecl powFn
    @Override
    Object pow(Object base, Object exp) {
        if (powFn == null) {
            powFn = ctx.mkFuncDecl('pow$', [ctx.getIntSort(), ctx.getIntSort()] as Sort[], ctx.getIntSort())
        }
        ctx.mkApp(powFn, (Expr) base, (Expr) exp)
    }

    private FuncDecl strConcatFn
    @Override
    Object strConcatRange(Object arr, Object lo, Object hi) {
        if (strConcatFn == null) {
            // Domain array is (Int -> String), matching arrayFor(List<String>); range is String.
            Sort arrSort = ctx.mkArraySort(ctx.getIntSort(), stringSort())
            strConcatFn = ctx.mkFuncDecl('strConcatArr$',
                [arrSort, ctx.getIntSort(), ctx.getIntSort()] as Sort[],
                stringSort())
        }
        ctx.mkApp(strConcatFn, (Expr) arr, (Expr) lo, (Expr) hi)
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

    // Phase 47 — string operations are now Z3 native primitives via the seq theory, not
    // uninterpreted functions. The previous Phase-46a/b/e {@code startsWithFn} / {@code strLengthFn}
    // / {@code strCharAtFn} declarations are retired along with the Phase-46c session-level
    // axioms (non-negativity + prefix/suffix length bound); all three are theory consequences.

    @Override
    Object stringStartsWith(Object s, Object prefix) {
        // {@code (str.prefixof prefix s)} — is prefix a prefix of s? Argument order matters.
        ctx.mkPrefixOf((Expr) prefix, (Expr) s)
    }

    @Override
    Object stringEndsWith(Object s, Object suffix) {
        ctx.mkSuffixOf((Expr) suffix, (Expr) s)
    }

    @Override
    Object stringContainsSub(Object s, Object sub) {
        ctx.mkContains((Expr) s, (Expr) sub)
    }

    @Override
    Object stringLength(Object s) {
        ctx.mkLength((Expr) s)
    }

    @Override
    Object stringCharAt(Object s, Object i) {
        // Z3 native: {@code (char.to_int (seq.nth s i))} — extract the char at position {@code i}
        // (a single-character sequence is the seq theory's "char" view) and convert to its int
        // codepoint. The Phase-46e wrapper {@code charAt$} is retired; both literal-position
        // identities and cross-string facts now come from the seq theory directly.
        ctx.charToInt(ctx.mkNth((Expr) s, (Expr) i))
    }

    @Override
    Object stringConcat(Object a, Object b) {
        // {@code mkConcat} is overloaded: a 2-arg BitVec form and a varargs Seq form. Groovy's
        // static dispatch with two {@code Expr} args picks the BitVec one, which Z3 then
        // rejects at runtime with "operator applied to wrong sort". Passing an explicit
        // {@code SeqExpr[]} array forces the Seq varargs overload.
        SeqExpr[] args = [(SeqExpr) a, (SeqExpr) b] as SeqExpr[]
        ctx.mkConcat(args)
    }

    @Override
    Object stringSubstring(Object s, Object offset, Object length) {
        ctx.mkExtract((Expr) s, (Expr) offset, (Expr) length)
    }

    @Override
    Object stringReplace(Object s, Object oldSub, Object newSub) {
        ctx.mkReplace((Expr) s, (Expr) oldSub, (Expr) newSub)
    }

    @Override
    Object stringIndexOf(Object s, Object sub, Object fromIndex) {
        ctx.mkIndexOf((Expr) s, (Expr) sub, (Expr) fromIndex)
    }

    @Override
    Object stringInRegex(Object s, Object regex) {
        ctx.mkInRe((Expr) s, (com.microsoft.z3.ReExpr) regex)
    }

    @Override
    Object reToRe(Object stringExpr) {
        ctx.mkToRe((Expr) stringExpr)
    }

    @Override
    Object reUnion(Object a, Object b) {
        com.microsoft.z3.ReExpr[] args = [(com.microsoft.z3.ReExpr) a, (com.microsoft.z3.ReExpr) b] as com.microsoft.z3.ReExpr[]
        ctx.mkUnion(args)
    }

    @Override
    Object reConcat(Object a, Object b) {
        com.microsoft.z3.ReExpr[] args = [(com.microsoft.z3.ReExpr) a, (com.microsoft.z3.ReExpr) b] as com.microsoft.z3.ReExpr[]
        ctx.mkConcat(args)
    }

    @Override
    Object reStar(Object re) {
        ctx.mkStar((Expr) re)
    }

    @Override
    Object rePlus(Object re) {
        ctx.mkPlus((Expr) re)
    }

    @Override
    Object reOption(Object re) {
        ctx.mkOption((Expr) re)
    }

    @Override
    Object reRange(Object loChar, Object hiChar) {
        ctx.mkRange((Expr) loChar, (Expr) hiChar)
    }

    /** Phase 47c — the {@code re.allchar} regex ("any single character"). */
    private com.microsoft.z3.ReExpr cachedAllChar
    @Override
    Object reAllChar() {
        if (cachedAllChar == null) {
            com.microsoft.z3.ReSort reSort = ctx.mkReSort(stringSort())
            cachedAllChar = ctx.mkAllcharRe(reSort)
        }
        cachedAllChar
    }

    @Override
    Object reComplement(Object re) {
        ctx.mkComplement((Expr) re)
    }

    @Override
    Object reIntersect(Object a, Object b) {
        com.microsoft.z3.ReExpr[] args = [(com.microsoft.z3.ReExpr) a, (com.microsoft.z3.ReExpr) b] as com.microsoft.z3.ReExpr[]
        ctx.mkIntersect(args)
    }

    @Override
    Object reLoop(Object re, int lo, int hi) {
        ctx.mkLoop((Expr) re, lo, hi)
    }

    @Override
    Object reLoopAtLeast(Object re, int lo) {
        ctx.mkLoop((Expr) re, lo)
    }

    @Override
    Object stringFromInt(Object n) {
        // Java/Groovy-faithful: Integer.toString(-7) == "-7" == "-" ++ Integer.toString(7). Z3's
        // intToString is correct for non-negative inputs only (it returns "" for n < 0), so thread
        // the sign explicitly rather than reasoning over Z3's SMT-LIB semantics.
        ArithExpr nn = (ArithExpr) n
        BoolExpr nonneg = ctx.mkGe(nn, ctx.mkInt(0))
        Expr pos = ctx.intToString((Expr) nn)
        SeqExpr[] negParts = [(SeqExpr) ctx.mkString('-'),
                              (SeqExpr) ctx.intToString((Expr) ctx.mkUnaryMinus(nn))] as SeqExpr[]
        ctx.mkITE(nonneg, pos, ctx.mkConcat(negParts))
    }

    @Override
    Object parseIntFromString(Object s) {
        // Java/Groovy-faithful sign handling: parseInt("-7") == -7. Z3's stringToInt returns -1 for a
        // signed string, so strip a leading "-" and negate the magnitude. (Malformed-input
        // well-formedness is a separate, loud obligation — see parseIntValid.)
        Expr ss = (Expr) s
        BoolExpr neg = ctx.mkPrefixOf((Expr) ctx.mkString('-'), ss)
        Expr mag = ctx.mkExtract((Expr) ss, (Expr) ctx.mkInt(1),
            (Expr) ctx.mkSub((ArithExpr) ctx.mkLength(ss), ctx.mkInt(1)))   // substring(s, 1, len-1)
        Expr negVal = ctx.mkUnaryMinus((ArithExpr) ctx.stringToInt((Expr) mag))
        ctx.mkITE(neg, negVal, ctx.stringToInt((Expr) ss))
    }

    @Override
    Object parseIntValid(Object s) {
        // Well-formedness: Integer.parseInt(s) doesn't throw iff the sign-stripped magnitude is a
        // valid sequence of digits — equivalently Z3's stringToInt(magnitude) >= 0 (it returns -1 for
        // empty / non-digit / bare-"-" inputs). The loud obligation discharged at each parseInt site.
        Expr ss = (Expr) s
        BoolExpr neg = ctx.mkPrefixOf((Expr) ctx.mkString('-'), ss)
        Expr rest = ctx.mkExtract((Expr) ss, (Expr) ctx.mkInt(1),
            (Expr) ctx.mkSub((ArithExpr) ctx.mkLength(ss), ctx.mkInt(1)))
        Expr mag = ctx.mkITE(neg, rest, ss)
        ctx.mkGe((ArithExpr) ctx.stringToInt((Expr) mag), ctx.mkInt(0))
    }

    /**
     * Phase 47f — uninterpreted {@code replaceAll$} and {@code lastIndexOf$}, lazily declared
     * with weak universally-quantified axioms on first use. Z3 has no native primitive for
     * either; the uninterpreted form lets calls thread through proofs as opaque, with the
     * axioms providing the minimal facts that aren't a semantic gamble.
     */
    private FuncDecl replaceAllFn
    private FuncDecl lastIndexOfFn
    private boolean replaceAllAxiomsAsserted = false
    private boolean lastIndexOfAxiomsAsserted = false

    private FuncDecl ensureReplaceAllFn() {
        if (replaceAllFn != null) return replaceAllFn
        Sort strSort = stringSort()
        replaceAllFn = ctx.mkFuncDecl('replaceAll$',
            [strSort, strSort, strSort] as Sort[], strSort)
        replaceAllFn
    }

    private FuncDecl ensureLastIndexOfFn() {
        if (lastIndexOfFn != null) return lastIndexOfFn
        Sort strSort = stringSort()
        lastIndexOfFn = ctx.mkFuncDecl('lastIndexOf$',
            [strSort, strSort, ctx.getIntSort()] as Sort[], ctx.getIntSort())
        lastIndexOfFn
    }

    private void ensureReplaceAllAxioms() {
        if (replaceAllAxiomsAsserted) return
        replaceAllAxiomsAsserted = true
        FuncDecl fn = ensureReplaceAllFn()
        Sort strSort = stringSort()
        Expr s  = ctx.mkConst('q$raS', strSort)
        Expr od = ctx.mkConst('q$raO', strSort)
        Expr nw = ctx.mkConst('q$raN', strSort)
        Expr appl = ctx.mkApp(fn, s, od, nw)
        // Axiom: ¬contains(s, old) ⟹ replaceAll(s, old, new) == s. (When the target isn't
        // present, the result is the input — the only fact we're sure about without primitives.)
        BoolExpr noOccur = (BoolExpr) ctx.mkNot(ctx.mkContains((Expr) s, (Expr) od))
        BoolExpr noOp = ctx.mkImplies(noOccur, ctx.mkEq(appl, s))
        addAxiom(ctx.mkForall([s, od, nw] as Expr[], noOp, 1,
            [ctx.mkPattern(appl)] as Pattern[], (Expr[]) null,
            (com.microsoft.z3.Symbol) null, (com.microsoft.z3.Symbol) null))
        // Axiom: length(old) == length(new) ⟹ length(replaceAll(s, old, new)) == length(s).
        // (Single-character replace, the most common case.)
        Expr lenOld = ctx.mkLength((Expr) od)
        Expr lenNew = ctx.mkLength((Expr) nw)
        Expr lenS   = ctx.mkLength((Expr) s)
        Expr lenAppl = ctx.mkLength((Expr) appl)
        BoolExpr sameLen = ctx.mkImplies(
            ctx.mkEq(lenOld, lenNew),
            ctx.mkEq(lenAppl, lenS))
        addAxiom(ctx.mkForall([s, od, nw] as Expr[], sameLen, 1,
            [ctx.mkPattern(appl)] as Pattern[], (Expr[]) null,
            (com.microsoft.z3.Symbol) null, (com.microsoft.z3.Symbol) null))
    }

    private void ensureLastIndexOfAxioms() {
        if (lastIndexOfAxiomsAsserted) return
        lastIndexOfAxiomsAsserted = true
        FuncDecl fn = ensureLastIndexOfFn()
        Sort strSort = stringSort()
        Expr s    = ctx.mkConst('q$liS', strSort)
        Expr sub  = ctx.mkConst('q$liT', strSort)
        Expr from = ctx.mkIntConst('q$liF')
        Expr appl = ctx.mkApp(fn, s, sub, from)
        // Axiom: lastIndexOf(s, sub, from) >= -1.
        BoolExpr geMinus1 = ctx.mkGe((ArithExpr) appl, (ArithExpr) ctx.mkInt(-1))
        addAxiom(ctx.mkForall([s, sub, from] as Expr[], geMinus1, 1,
            [ctx.mkPattern(appl)] as Pattern[], (Expr[]) null,
            (com.microsoft.z3.Symbol) null, (com.microsoft.z3.Symbol) null))
        // Axiom: ¬contains(s, sub) ⟹ lastIndexOf(s, sub, from) == -1.
        BoolExpr noOccur = (BoolExpr) ctx.mkNot(ctx.mkContains((Expr) s, (Expr) sub))
        BoolExpr negOne = ctx.mkImplies(noOccur, ctx.mkEq(appl, ctx.mkInt(-1)))
        addAxiom(ctx.mkForall([s, sub, from] as Expr[], negOne, 1,
            [ctx.mkPattern(appl)] as Pattern[], (Expr[]) null,
            (com.microsoft.z3.Symbol) null, (com.microsoft.z3.Symbol) null))
    }

    /** Phase 47f — helper used by the axiom-emission paths above. Mirrors the pattern Phase
     *  46c used before native theory retired its axioms — kept local since other paths no
     *  longer need it. */
    private void addAxiom(Object ax) {
        BoolExpr be = (BoolExpr) ax
        solver.add(be)
        assertedExprs.add(be)
    }

    @Override
    Object stringReplaceAll(Object s, Object oldSub, Object newSub) {
        ensureReplaceAllAxioms()
        ctx.mkApp(replaceAllFn, (Expr) s, (Expr) oldSub, (Expr) newSub)
    }

    @Override
    Object stringLastIndexOf(Object s, Object sub, Object fromIndex) {
        ensureLastIndexOfAxioms()
        ctx.mkApp(lastIndexOfFn, (Expr) s, (Expr) sub, (Expr) fromIndex)
    }

    /**
     * Phase 47g — case-folding state. {@code toUpperFn}/{@code toLowerFn} are uninterpreted
     * declarations brought up on first use; {@code stringLiteralKeys} tracks every minted
     * String literal so we can pin its case forms on the spot, and re-pin retroactively when
     * the case ops are first referenced (rare for typical workloads). The pinning uses
     * {@link Locale#ROOT} — ASCII-faithful, no Turkish-locale {@code i}/{@code İ} surprise.
     */
    private FuncDecl toUpperFn
    private FuncDecl toLowerFn
    private boolean caseAxiomsAsserted = false
    private final Set<String> stringLiteralKeys = new LinkedHashSet<String>()

    private FuncDecl ensureToUpperFn() {
        if (toUpperFn != null) return toUpperFn
        toUpperFn = ctx.mkFuncDecl('toUpper$', [stringSort()] as Sort[], stringSort())
        // Newly declared — pin every literal that was minted before this point.
        pinExistingLiterals()
        toUpperFn
    }

    private FuncDecl ensureToLowerFn() {
        if (toLowerFn != null) return toLowerFn
        toLowerFn = ctx.mkFuncDecl('toLower$', [stringSort()] as Sort[], stringSort())
        pinExistingLiterals()
        toLowerFn
    }

    /** Phase 47g — pin case forms for every literal currently in the universe. */
    private void pinExistingLiterals() {
        // Snapshot to avoid concurrent-modification while pinCaseLiteral expands the set.
        List<String> snapshot = new ArrayList<String>(stringLiteralKeys)
        for (String key : snapshot) {
            pinCaseLiteral(key, ctx.mkString(key))
        }
    }

    /**
     * Phase 47g — assert {@code toUpper(lit) == mkString(upper(key))} and the toLower mirror.
     * Recursively pins the derived literals (the upper/lower forms themselves) so the case
     * universe is closed. {@link Locale#ROOT} is the case-folding contract — ASCII-faithful.
     */
    private void pinCaseLiteral(String key, Expr lit) {
        if (toUpperFn != null) {
            String upperKey = key.toUpperCase(java.util.Locale.ROOT)
            Expr upperLit = ctx.mkString(upperKey)
            BoolExpr pin = ctx.mkEq(ctx.mkApp(toUpperFn, lit), upperLit)
            solver.add(pin)
            assertedExprs.add(pin)
            if (stringLiteralKeys.add(upperKey)) {
                pinCaseLiteral(upperKey, upperLit)
            }
        }
        if (toLowerFn != null) {
            String lowerKey = key.toLowerCase(java.util.Locale.ROOT)
            Expr lowerLit = ctx.mkString(lowerKey)
            BoolExpr pin = ctx.mkEq(ctx.mkApp(toLowerFn, lit), lowerLit)
            solver.add(pin)
            assertedExprs.add(pin)
            if (stringLiteralKeys.add(lowerKey)) {
                pinCaseLiteral(lowerKey, lowerLit)
            }
        }
    }

    /**
     * Phase 47g — case-folding axioms. The natural set is length-preservation +
     * idempotence + cascade as universals, but each universal over a {@code (Seq Char) -> Seq Char}
     * uninterpreted function defeats Z3's model construction whenever the conjecture *negates*
     * a literal equation involving {@code toUpper}/{@code toLower}. Confirmed by a standalone
     * probe: {@code "Hello".toUpperCase() != "hello"} solves in 9ms with literal-pin only,
     * hangs for 60s+ (any timeout — not a slow-laptop issue) once even the length-preservation
     * universal is asserted. The unsat-direction (positive verification) is fast either way;
     * the sat-direction (refute) is where Z3 stalls trying to build a model that satisfies
     * the universal for the uninterpreted seq-to-seq function.
     *
     * <p>Resolution: no universals; rely on per-literal pinning at the mint site. Literal-only
     * cases work; symbolic length / idempotence / cascade claims aren't reachable. The
     * structural facts remain true mathematically. Future Z3 releases (or a different solver
     * tactic) may handle this better.
     */
    private void ensureCaseAxioms() {
        if (caseAxiomsAsserted) return
        caseAxiomsAsserted = true
        ensureToUpperFn()
        ensureToLowerFn()
    }

    @Override
    Object stringToUpper(Object s) {
        ensureCaseAxioms()
        ctx.mkApp(toUpperFn, (Expr) s)
    }

    @Override
    Object stringToLower(Object s) {
        ensureCaseAxioms()
        ctx.mkApp(toLowerFn, (Expr) s)
    }

    /**
     * Phase 47i — reverse state. {@code reverse$} is an uninterpreted {@code (String) -> String}
     * brought up on first use; like case-folding, it relies on per-literal pinning (no universals —
     * Phase 47g showed those defeat Z3's seq model construction). Pinning is bidirectional, so
     * literal involution and literal length follow for free.
     */
    private FuncDecl reverseFn

    private FuncDecl ensureReverseFn() {
        if (reverseFn != null) return reverseFn
        reverseFn = ctx.mkFuncDecl('reverse$', [stringSort()] as Sort[], stringSort())
        // No universals — confirmed by probe (matching Phase 47g): a triggered length-preservation +
        // involution universal over reverse$ *does* prove symbolic `s.reverse().reverse() == s` and
        // `s.reverse().length() == s.length()`, but poisons the refute direction — `"abc".reverse() ==
        // "abc"` (false) goes from a clean "cannot prove" to a solver timeout. Z3's seq model
        // construction stalls building a model that satisfies the universal over a Seq→Seq function.
        // Literal pinning only; symbolic algebraic identities stay out (sound under-approximation).
        List<String> snapshot = new ArrayList<String>(stringLiteralKeys)
        for (String key : snapshot) pinReverseLiteral(key, ctx.mkString(key))
        reverseFn
    }

    /**
     * Phase 47i — assert {@code reverse(lit) == mkString(rev(key))}. Recursively pins the reversed
     * literal too (so {@code reverse(reverse(lit)) == lit} is present); a palindrome key reverses to
     * itself and the recursion stops. Java {@code StringBuilder.reverse} is the contract.
     */
    private void pinReverseLiteral(String key, Expr lit) {
        if (reverseFn == null) return
        String revKey = new StringBuilder(key).reverse().toString()
        Expr revLit = ctx.mkString(revKey)
        BoolExpr pin = ctx.mkEq(ctx.mkApp(reverseFn, lit), revLit)
        solver.add(pin)
        assertedExprs.add(pin)
        if (stringLiteralKeys.add(revKey)) {
            pinReverseLiteral(revKey, revLit)
        }
    }

    @Override
    Object stringReverse(Object s) {
        ensureReverseFn()
        ctx.mkApp(reverseFn, (Expr) s)
    }

    @Override Object boundIntVar(String name) { ctx.mkIntConst(name) }

    @Override
    Object forall(List<Object> bound, Object body, List<Object> triggers) {
        Expr[] b = bound.collect { (Expr) it } as Expr[]
        // weight 1, the given patterns, no no-patterns, no quantifier/skolem id.
        ctx.mkForall(b, (Expr) body, 1, patternsFor(triggers, b), (Expr[]) null, (com.microsoft.z3.Symbol) null, (com.microsoft.z3.Symbol) null)
    }

    @Override
    Object forallMultiPattern(List<Object> bound, Object body, List<Object> patternTerms) {
        Expr[] b = bound.collect { (Expr) it } as Expr[]
        Pattern[] pats = null
        if (patternTerms != null && !patternTerms.isEmpty()) {
            List<Expr> terms = new ArrayList<Expr>()
            for (Object t : patternTerms) {
                Expr e = (Expr) t
                if (containsForbiddenPattern(e)) { terms = null; break }   // can't form a valid pattern → auto
                terms.add(e)
            }
            // One multi-pattern covering all bound vars at once (the whole point — see SmtBackend doc).
            if (terms != null && !terms.isEmpty()) pats = [ctx.mkPattern(terms as Expr[])] as Pattern[]
        }
        ctx.mkForall(b, (Expr) body, 1, pats, (Expr[]) null, (com.microsoft.z3.Symbol) null, (com.microsoft.z3.Symbol) null)
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
            Expr e = (Expr) t
            if (mentions(e, bound) && !containsForbiddenPattern(e)) {
                pats.add(ctx.mkPattern(e))
            }
        }
        pats.isEmpty() ? null : (pats as Pattern[])
    }

    /**
     * SMT-LIB rejects patterns that contain Boolean operators ({@code and}, {@code or},
     * {@code not}, {@code implies}), arithmetic, or {@code ite} at any position. After a
     * conditional list mutation (Phase 45c ITE-combine), the array binding is an
     * {@code ite}-expression — selecting from that array would produce a
     * {@code select(ite, …)} term that Z3 won't accept as a quantifier trigger. Walking the
     * term and skipping any such candidate keeps the rest of the trigger set valid; if
     * everything is filtered out, the caller falls back to auto-patterns.
     */
    private static boolean containsForbiddenPattern(Expr e) {
        if (e == null) return false
        if (e.isITE() || e.isAnd() || e.isOr() || e.isNot() || e.isImplies() ||
            e.isAdd() || e.isSub() || e.isMul() || e.isDiv() || e.isModulus()) {
            return true
        }
        if (e.isApp()) {
            for (Expr a : e.getArgs()) {
                if (containsForbiddenPattern(a)) return true
            }
        }
        false
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
    @Override Object intDiv(Object a, Object b) { ctx.mkDiv((Expr) a, (Expr) b) }
    @Override Object intMod(Object a, Object b) { ctx.mkMod((Expr) a, (Expr) b) }
    @Override Object intRem(Object a, Object b) {
        // Groovy's % / .remainder: truncated, sign-of-dividend (-5 % 2 == -1). Z3's mkRem does NOT
        // follow the dividend's sign, so build it from the Euclidean mod (mkMod ∈ [0, |b|)):
        //   rem = (a >= 0 || mod == 0) ? mod : mod - |b|
        Expr mod = (Expr) ctx.mkMod((Expr) a, (Expr) b)
        Expr absb = ctx.mkITE(ctx.mkGe((ArithExpr) b, ctx.mkInt(0)), (Expr) b, ctx.mkUnaryMinus((ArithExpr) b))
        BoolExpr nonneg = ctx.mkOr(ctx.mkGe((ArithExpr) a, ctx.mkInt(0)), ctx.mkEq(mod, ctx.mkInt(0)))
        ctx.mkITE(nonneg, mod, ctx.mkSub((ArithExpr) mod, (ArithExpr) absb))
    }

    // Phase 61 — Real (exact rational) primitives for Groovy BigDecimal arithmetic.
    @Override Object realLit(String rational) { ctx.mkReal(rational) }
    @Override Object realVar(String name)     { ctx.mkRealConst(name) }
    @Override Object realDiv(Object a, Object b) { ctx.mkDiv((ArithExpr) a, (ArithExpr) b) }
    @Override Object intToReal(Object a)      { ctx.mkInt2Real((IntExpr) a) }

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
        BoolExpr be = (BoolExpr) boolExpr
        solver.add(be)
        assertedExprs.add(be)
    }

    // SMT {@code Int} is the unbounded mathematical integer, so a model can pin a counterexample
    // variable to a value outside {@code long} range — e.g. a 64-bit-overflow witness where Z3 picks
    // an operand past {@code Long.MAX_VALUE}. {@code IntNum.getInt64()} throws "Numeral is not an
    // int64" on those, which (uncaught) would silently drop the whole refute back to a clean compile.
    // The counterexample map is display-only, so saturate to the {@code long} boundary: the rendered
    // witness sits at the edge of the representable range, and the refute itself is preserved.
    private static long clampInt64(IntNum n) {
        BigInteger b = n.getBigInteger()
        if (b.compareTo(BigInteger.valueOf(Long.MAX_VALUE)) > 0) return Long.MAX_VALUE
        if (b.compareTo(BigInteger.valueOf(Long.MIN_VALUE)) < 0) return Long.MIN_VALUE
        return b.longValue()
    }

    /**
     * Phase 34 — canonical fingerprint of the asserted set. Sorted S-expression strings make the
     * key insensitive to assertion order (the solver result already is), and the timeout prefix
     * guards against a hard-VC UNKNOWN being reused under a different bound.
     */
    private String vcKey() {
        if (assertedExprs.isEmpty()) return "t:${timeoutMs}\n<empty>"
        List<String> reprs = new ArrayList<String>(assertedExprs.size())
        for (BoolExpr e : assertedExprs) reprs.add(e.toString())
        Collections.sort(reprs)
        StringBuilder sb = new StringBuilder()
        sb.append('t:').append(timeoutMs).append('\n')
        for (String s : reprs) sb.append(s).append('\n')
        sb.toString()
    }

    @Override
    CheckResult check() {
        String key = vcKey()
        CheckResult cached = Z3Backend.vcCache.get(key)
        if (cached != null) {
            Z3Backend.recordVCCacheHit()
            return cached
        }
        Z3Backend.recordVCCacheMiss()
        CheckResult result = computeCheck()
        Z3Backend.vcCache.put(key, result)
        return result
    }

    private CheckResult computeCheck() {
        // {@code Z3_TIMING=1} env var reports any check slower than 500ms — a forensic hook
        // for spotting solver hot spots without paying overhead in normal runs.
        long t0 = System.nanoTime()
        Status status = solver.check()
        long elapsedMs = (long)((System.nanoTime() - t0) / 1_000_000L)
        if (System.getenv('Z3_TIMING') == '1' && elapsedMs > 500) {
            System.err.println("[Z3] check ${status} in ${elapsedMs}ms")
        }
        if (status == Status.UNSATISFIABLE) {
            return CheckResult.verified()
        }
        if (status == Status.UNKNOWN) {
            return CheckResult.unknown(solver.getReasonUnknown())
        }
        // SATISFIABLE: extract counterexample for variables we declared
        Model m = solver.getModel()
        lastModel = m    // Phase 126 — retain for post-check element evaluation (evalDisplay)
        Map<String, Long> ce = [:]
        vars.each { name, var ->
            Expr v = m.evaluate(var, false)
            if (v instanceof IntNum) {
                ce[name] = clampInt64((IntNum) v)
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
                if (ev instanceof IntNum) ce[name + '[' + k + ']'] = clampInt64((IntNum) ev)
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
            int vColon = key.indexOf(':')
            String name = vColon >= 0 ? key.substring(0, vColon) : key
            // Phase 47 — Z3 native strings expose the model value directly via
            // {@code getString()}; no reverse-lookup through {@code sortedLits} needed.
            if (var.getSort() == cachedStringSort) {
                Expr mv = m.evaluate(var, false)
                if (mv != null && mv.isString()) {
                    sce[name] = mv.getString()
                }
                return  // continue
            }
            // Uninterpreted sorts (Enum): equality-evaluate against every interned literal,
            // since Z3 may pin the var to a synthetic constant (e.g. {@code Color!val!1})
            // distinct from our minted ones but equal-by-model — getName-matching alone misses
            // that case.
            com.microsoft.z3.Sort varSort = var.getSort()
            Expr mv = m.evaluate(var, false)
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
