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
import org.codehaus.groovy.ast.expr.ArgumentListExpression
import org.codehaus.groovy.ast.expr.BinaryExpression
import org.codehaus.groovy.ast.expr.DeclarationExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.PostfixExpression
import org.codehaus.groovy.ast.expr.PrefixExpression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.EmptyStatement
import org.codehaus.groovy.ast.stmt.AssertStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.IfStatement
import org.codehaus.groovy.ast.stmt.LoopingStatement
import org.codehaus.groovy.ast.stmt.ReturnStatement
import org.codehaus.groovy.ast.stmt.Statement
import org.codehaus.groovy.syntax.Types

/**
 * Everything captured at producer-compile-time for one annotated loop:
 * the conjuncts of its {@code @Invariant}, the optional {@code @Decreases}
 * measure, the loop guard, and a clean snapshot of the loop body. The body
 * is copied at CONVERSION because groovy-contracts injects its own invariant
 * asserts into the live loop body at SEMANTIC_ANALYSIS.
 */
@CompileStatic
class LoopSpec {
    List<Expression> invariants = []
    Expression variant            // null when no @Decreases
    Expression guard
    List<Statement> body = []
    // Phase 59 — a classic {@code for (init; cond; update)} desugars to
    // {@code init; while (cond) { body; update }}: {@code init} is threaded into the
    // loop prefix and {@code update} is appended to {@code body} at capture time, so
    // every downstream path (loop VCs and value-flow) sees a plain while-shaped loop.
    List<Statement> init = null   // null for while/do-while
    // Phase 63/65 — for a {@code for (x in xs)} loop, the loop variable's name and the synthetic
    // {@code x = xs[idx]} binding. groovy-contracts checks the invariant at *body-entry* (x bound),
    // so an invariant clause referencing {@code x} is a per-element check (Phase 65), not a loop-head
    // invariant — verified with x = xs[idx] under 0 <= idx < size (vacuous on an empty collection).
    String forInVar = null
    Statement forInBind = null
    // Phase 88 — a {@code do B while (G)} loop ({@code do-while}). Semantically {@code B; while (G) B}:
    // the body runs once unconditionally before the first guard/invariant check, so establishment must
    // hold AFTER that first iteration, not at loop entry. Preservation/progress/use (the residual while)
    // are identical to a plain while. (Treating do-while as while was silently unsound — see Phase 88.)
    boolean isDoWhile = false
    // A for-in / `.each` that carries ONLY the auto bounds invariant (no user or inferred @Invariant): its
    // `0 <= idx <= size` proves SAFETY (per-element properties, bounded reads) and `size - idx` proves
    // termination, but it can't frame a variable the body *accumulates* — so the postcondition use check
    // loud-skips when the body writes anything beyond the loop variable / synthetic index (an accumulating
    // `.each` would need an @Invariant, which is a Groovy parse error on a method-call statement).
    boolean autoInvariantOnly = false
}

/**
 * Straight-line symbolic execution helpers for loop verification, built on the
 * {@link Encoder}'s mutable name→handle store: an assignment is just a re-bind,
 * so SSA renaming falls out for free, and a fresh {@code Encoder} per
 * verification condition gives havoc-by-default (any name never assigned is an
 * unconstrained fresh variable). The supported region is the same fragment as
 * the rest of the spike: plain assignments, single-variable declarations, and a
 * trailing/explicit return — anything else raises
 * {@link UnsupportedConstructException}.
 */
@CompileStatic
class LoopEncoder {

    /** Frames a contracted call (e.g. an {@code @UnderRely} rely-step) inside a loop body — havoc its declared
     *  frame and assume its {@code @Ensures}. Returns true if it handled the call. {@link VerifyChecker} installs
     *  one (delegating to {@code assumeCalleeEnsures}) around a method's loop verification; null elsewhere. */
    interface LoopCallHandler {
        boolean handle(MethodCallExpression call, Encoder enc, SmtSession s)
    }

    /** Installed by {@link VerifyChecker} around the loop verification of a method; read by {@link #applyAssign}.
     *  Thread-local + set/restore, so concurrent compilations (parallel builds) don't collide. */
    static final ThreadLocal<LoopCallHandler> callHandler = new ThreadLocal<LoopCallHandler>()

    /** The {@code .count(v)} value expressions the enclosing loop's invariant / contract tracks (the {@code v}
     *  in {@code a.count(v)}). Set/restored by {@link VerifyChecker#verifyLoop}, read by {@link #applyAssign} so an
     *  inline array store in the loop body emits the same per-store count law the method-body executor does — without
     *  it, {@code count(a)} is unconstrained across the body and a permutation invariant can't be preserved. Held as
     *  AST (not Z3 terms) because each loop VC translates against its own fresh session. Empty ⇒ ordinary loops pay
     *  nothing. Thread-local for the same parallel-build reason as {@link #callHandler}. */
    static final ThreadLocal<List<Expression>> countVals = new ThreadLocal<List<Expression>>()

    /** Translate the enclosing loop's tracked {@code .count(v)} value expressions against the live encoder/session. */
    private static List<Object> translatedCountVals(Encoder enc) {
        List<Expression> exprs = countVals.get()
        if (exprs == null || exprs.isEmpty()) return Collections.<Object> emptyList()
        List<Object> out = new ArrayList<Object>()
        for (Expression ve : exprs) { Object h = enc.translate(ve); if (h != null) out.add(h) }
        out
    }

    /** Translate, raising a "skipped" rather than returning null. */
    static Object tr(Encoder enc, Expression e, String what) {
        Object h = enc.translate(e)
        if (h == null) {
            throw new UnsupportedConstructException(
                "${what} ('${e?.text}') is outside the supported fragment")
        }
        return h
    }

    /** Conjunction of the invariant's conjuncts under the current store. */
    static Object conj(Encoder enc, SmtSession s, List<Expression> invs) {
        if (invs == null || invs.isEmpty()) {
            throw new UnsupportedConstructException("loop has no invariant conjuncts")
        }
        List<Object> hs = new ArrayList<Object>()
        for (Expression e : invs) hs.add(tr(enc, e, "invariant"))
        return hs.size() == 1 ? hs.get(0) : s.and(hs)
    }

    /** Execute a straight-line region (prefix or loop body), updating the store. */
    static void symExec(List<Statement> stmts, Encoder enc, SmtSession s) {
        // Expression-position `++`/`--` (`x = i++`, `a[i++] = v`) → an explicit two-statement sequence.
        stmts = Encoder.expandIncDecStatements(stmts)
        for (Statement st : stmts) {
            LoopSpec innerSpec = (st instanceof LoopingStatement) ?
                (LoopSpec) ((Statement) st).getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY) : null
            if (st instanceof BlockStatement) {
                symExec(((BlockStatement) st).statements, enc, s)
            } else if (st instanceof ExpressionStatement) {
                applyAssign((ExpressionStatement) st, enc, s)
            } else if (st instanceof IfStatement) {
                applyIf((IfStatement) st, enc, s)
            } else if (st instanceof AssertStatement) {
                // Assume the asserted condition — it is proven separately by the in-loop assert discharge
                // (verifyLoopObligations), so threading it as a fact for the rest of the body is sound
                // (assume/enforce). An unmodelable condition just isn't assumed (fewer facts, still sound).
                Object c = enc.translate(((AssertStatement) st).booleanExpression)
                if (c != null) s.assertExpr(c)
            } else if (innerSpec != null) {
                summarizeInner(innerSpec, enc, s)
            } else {
                throw new UnsupportedConstructException(
                    "unsupported statement ${st.class.simpleName} in loop region (line ${st.lineNumber})")
            }
        }
    }

    /**
     * Phase 91 — replace a nested annotated loop with its inductive summary: havoc the variables it
     * writes — scalars (`havoc`) and array contents (`havocArray`) — then assume `inner_inv ∧
     * ¬inner_guard` (its post-state). Used by *both* the VC body walk and the obligation pass's
     * `preceding` replay, so the two stay consistent. {@link #innerFrame} returns false (→ loud skip) if
     * the inner body writes anything it can't soundly account for (a field, a collection mutator, or an
     * unrecognised construct) — under-havocking would leave the outer state with a value the inner loop
     * actually changed. Array *size* is deliberately not havoc'd: `a[k] = v` changes contents, not length;
     * a length-changing inner loop (a collection mutator) is rejected by {@code innerFrame}.
     */
    static void summarizeInner(LoopSpec inner, Encoder enc, SmtSession s) {
        Set<String> scalars = new HashSet<String>()
        Set<String> arrays = new HashSet<String>()
        if (!innerFrame(inner.body, scalars, arrays)) {
            throw new UnsupportedConstructException(
                "nested loop writes a field/collection or unbounded construct — not yet supported")
        }
        for (String nm : scalars) enc.havoc(nm)
        // Phase 186 — a written subscript target may be a MAP, whose havoc must refresh both the value
        // array and the key-set (an Int-sorted havocArray on a non-Int-keyed map sort-crashes).
        for (String nm : arrays) { if (enc.isMapName(nm)) enc.havocMap(nm) else enc.havocArray(nm) }
        s.assertExpr(conj(enc, s, inner.invariants))
        s.assertExpr(s.not(tr(enc, inner.guard, "inner-loop guard")))
    }

    /** Partition a nested loop body's writes into scalar names and array names, or false if it writes
     *  anything that isn't a plain scalar local or an `a[idx] = v` array element (so havocking the two
     *  sets is a complete account of the inner loop's effect). */
    static boolean innerFrame(List<Statement> stmts, Set<String> scalars, Set<String> arrays) {
        if (stmts == null) return true
        for (Statement st : stmts) if (!innerFrameStmt(st, scalars, arrays)) return false
        true
    }
    private static boolean innerFrameStmt(Statement st, Set<String> scalars, Set<String> arrays) {
        if (st == null || st instanceof EmptyStatement) return true
        if (st instanceof BlockStatement) return innerFrame(((BlockStatement) st).statements, scalars, arrays)
        if (st instanceof IfStatement) {
            IfStatement ifs = (IfStatement) st
            return innerFrameStmt(ifs.ifBlock, scalars, arrays) &&
                   (ifs.elseBlock == null || innerFrameStmt(ifs.elseBlock, scalars, arrays))
        }
        if (st instanceof ExpressionStatement) return innerFrameExpr(((ExpressionStatement) st).expression, scalars, arrays)
        // Phase 109 — a `return` inside the inner loop writes nothing to the *outer* state (it transfers
        // control out of the method). On the fall-through path — the only one where the outer loop continues
        // past the inner loop — the inner loop completed without returning, so the summary (inner_inv ∧
        // ¬inner_guard) is unaffected. The return's own @Ensures is discharged separately (verifyNestedLoops).
        if (st instanceof ReturnStatement) return true
        return false   // nested loop / unknown statement → bail
    }
    private static boolean innerFrameExpr(Expression e, Set<String> scalars, Set<String> arrays) {
        if (e == null) return true
        if (e instanceof DeclarationExpression) {
            DeclarationExpression de = (DeclarationExpression) e
            if (!(de.leftExpression instanceof VariableExpression)) return false
            scalars.add(((VariableExpression) de.leftExpression).name)
            return true
        }
        if (e instanceof PostfixExpression) return innerFrameTarget(((PostfixExpression) e).expression, scalars, arrays)
        if (e instanceof PrefixExpression)  return innerFrameTarget(((PrefixExpression) e).expression, scalars, arrays)
        if (e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e
            if (Types.ofType(be.operation.type, Types.ASSIGNMENT_OPERATOR)) return innerFrameTarget(be.leftExpression, scalars, arrays)
            return true
        }
        return false   // method calls (mutators / unknown) → bail
    }
    private static boolean innerFrameTarget(Expression t, Set<String> scalars, Set<String> arrays) {
        if (t instanceof VariableExpression) { scalars.add(((VariableExpression) t).name); return true }
        if (t instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) t
            if (be.operation.type == Types.LEFT_SQUARE_BRACKET && be.leftExpression instanceof VariableExpression) {
                arrays.add(((VariableExpression) be.leftExpression).name); return true
            }
        }
        return false   // field / property / nested subscript target → bail
    }

    /**
     * Phase 45c — model an {@code if (cond) { then } else { else }} in a loop body via
     * snapshot-restore + SMT ITE: apply each branch in turn against a snapshot of the entry
     * bindings, then for any binding that differs between the two branches, rebind to
     * {@code ite(cond, thenValue, elseValue)}. A binding modified only in one branch uses the
     * entry value for the other side. Bindings unchanged in both branches are left alone.
     *
     * <p>Factory records (Phase 38b) that differ between branches are conservatively dropped
     * — the SMT ITE machinery only models the size/array oracles, not the literal-arg list,
     * so a conditional mutation must invalidate the factory fold regardless.
     */
    private static void applyIf(IfStatement ifs, Encoder enc, SmtSession s) {
        Object cond = enc.translate(ifs.booleanExpression)
        if (cond == null) {
            throw new UnsupportedConstructException(
                "if-condition '${ifs.booleanExpression.text}' is outside fragment in loop body")
        }
        Encoder.EncoderSnapshot entry = enc.snapshotState()
        // Then branch.
        Statement thenBlk = ifs.ifBlock
        if (thenBlk != null && !(thenBlk instanceof EmptyStatement)) {
            symExec(asList(thenBlk), enc, s)
        }
        Encoder.EncoderSnapshot afterThen = enc.snapshotState()
        // Restore + else branch.
        enc.restoreState(entry)
        Statement elseBlk = ifs.elseBlock
        if (elseBlk != null && !(elseBlk instanceof EmptyStatement)) {
            symExec(asList(elseBlk), enc, s)
        }
        Encoder.EncoderSnapshot afterElse = enc.snapshotState()
        // ITE-combine: for each map, walk the union of keys touched in either branch.
        iteCombineMap(afterThen.env, afterElse.env, entry.env, cond, enc, s,
            { String n, Object h -> enc.bind(n, h) })
        iteCombineMap(afterThen.arrEnv, afterElse.arrEnv, entry.arrEnv, cond, enc, s,
            { String n, Object h -> enc.bindArray(n, h) })
        iteCombineMap(afterThen.sizeEnv, afterElse.sizeEnv, entry.sizeEnv, cond, enc, s,
            { String n, Object h -> enc.bindSizeRaw(n, h) })
        iteCombineMap(afterThen.setEnv, afterElse.setEnv, entry.setEnv, cond, enc, s,
            { String n, Object h -> enc.bindSet(n, h) })
        // Conservative: drop any factory record that wasn't preserved by *both* branches.
        Set<String> factoryNames = new LinkedHashSet<String>()
        factoryNames.addAll(afterThen.localFactories.keySet())
        factoryNames.addAll(afterElse.localFactories.keySet())
        for (String n : factoryNames) {
            if (afterThen.localFactories.get(n) != afterElse.localFactories.get(n)) {
                enc.clearFactoryRecord(n)
            }
        }
    }

    /**
     * Combine two post-branch maps via SMT ITE, calling {@code apply} once per name whose
     * binding differs between branches. Names absent in one snapshot fall back to the entry
     * value; names absent in both fall back to the encoder's natural mint, which is rare here
     * because at least one branch must have changed the binding for the name to be in scope.
     */
    private static void iteCombineMap(Map<String, Object> thenMap, Map<String, Object> elseMap,
                                      Map<String, Object> entryMap, Object cond, Encoder enc,
                                      SmtSession s, Closure<Void> apply) {
        Set<String> names = new LinkedHashSet<String>()
        names.addAll(thenMap.keySet())
        names.addAll(elseMap.keySet())
        for (String n : names) {
            Object thenV = thenMap.get(n)
            Object elseV = elseMap.get(n)
            Object entryV = entryMap.get(n)
            if (thenV == null) thenV = entryV
            if (elseV == null) elseV = entryV
            if (thenV == null || elseV == null) continue   // truly fresh on both sides — leave alone
            if (thenV != elseV) {
                apply.call(n, s.ite(cond, thenV, elseV))
            }
        }
    }

    /** Helper to coerce a single-statement branch into a List for the recursive {@link #symExec}. */
    private static List<Statement> asList(Statement st) {
        if (st instanceof BlockStatement) return ((BlockStatement) st).statements
        Collections.singletonList(st)
    }

    /**
     * Execute the post-loop region and return the expression whose value the
     * method yields (explicit {@code return} or trailing expression).
     */
    static Expression resultExpr(List<Statement> stmts, Encoder enc, SmtSession s) {
        Expression result = null
        for (int i = 0; i < stmts.size(); i++) {
            Statement st = stmts.get(i)
            boolean last = (i == stmts.size() - 1)
            if (st instanceof ReturnStatement) {
                result = ((ReturnStatement) st).expression
                break
            } else if (st instanceof ExpressionStatement) {
                ExpressionStatement es = (ExpressionStatement) st
                if (isAssign(es.expression)) {
                    applyAssign(es, enc, s)
                } else if (last) {
                    result = es.expression   // Groovy implicit return
                } else {
                    throw new UnsupportedConstructException(
                        "statement with no modelled effect after loop (line ${st.lineNumber})")
                }
            } else {
                throw new UnsupportedConstructException(
                    "unsupported statement ${st.class.simpleName} after loop (line ${st.lineNumber})")
            }
        }
        if (result == null) {
            throw new UnsupportedConstructException("no return value after loop")
        }
        return result
    }

    private static boolean isAssign(Expression e) {
        (e instanceof DeclarationExpression) ||
        (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.ASSIGN) ||
        Encoder.isCompoundAssign(e) || Encoder.isIncDec(e)
    }

    private static void applyAssign(ExpressionStatement st, Encoder enc, SmtSession s) {
        Expression e = st.expression
        // Phase 85/86 — `s += xs[i]` and `i++` / `--i` desugar to `s = s + xs[i]` / `i = i ± 1` so the
        // assignment paths apply.
        if (Encoder.isIncDec(e)) e = Encoder.desugarIncDec(e)
        else if (Encoder.isCompoundAssign(e)) e = Encoder.desugarCompoundAssign((BinaryExpression) e)
        if (e instanceof DeclarationExpression) {
            DeclarationExpression de = (DeclarationExpression) e
            if (!(de.leftExpression instanceof VariableExpression)) {
                throw new UnsupportedConstructException(
                    "multi-variable declaration unsupported (line ${st.lineNumber})")
            }
            String name = ((VariableExpression) de.leftExpression).name
            rebind(enc, name, de.rightExpression)
            return
        }
        if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.ASSIGN) {
            BinaryExpression be = (BinaryExpression) e
            if (be.leftExpression instanceof VariableExpression) {
                rebind(enc, ((VariableExpression) be.leftExpression).name, be.rightExpression)
                return
            }
            // a[i] = v  ->  a := (store a i v): the array's contents are threaded
            // through the loop, so an invariant over them is preserved across the
            // body (Phase 6 store, now inside loops).
            if (be.leftExpression instanceof BinaryExpression &&
                ((BinaryExpression) be.leftExpression).operation.type == Types.LEFT_SQUARE_BRACKET &&
                ((BinaryExpression) be.leftExpression).leftExpression instanceof VariableExpression) {
                BinaryExpression sub = (BinaryExpression) be.leftExpression
                String arr = ((VariableExpression) sub.leftExpression).name
                // Phase 186 — m[k] = v on a MAP inside a loop body: a map put (value store + key-set add +
                // cardinality law), routed through the map's declared key/value sorts — mirroring the
                // straight-line replay. Without this the map fell into the Int-indexed array path below
                // and sort-crashed to a loud skip on any non-Int-keyed map.
                if (enc.isMapName(arr)) {
                    Object k = enc.translateInSort(sub.rightExpression, enc.mapKeySort(arr))
                    Object mv = enc.translateInSort(be.rightExpression, enc.mapValueSort(arr))
                    if (k == null || mv == null) enc.havocMap(arr)   // unmodelable put → map unknown (sound)
                    else enc.mapPut(arr, k, mv)
                    return
                }
                Object idx = enc.translate(sub.rightExpression)
                Object val = enc.translate(be.rightExpression)
                if (idx == null || val == null) enc.havocArray(arr)   // unmodelable update → contents unknown (sound)
                else {
                    Object oldA = enc.arrayFor(arr)
                    Object newA = s.store(oldA, idx, val)
                    enc.bindArray(arr, newA)
                    // Maintain count(a, v) for the loop's tracked values, so a swap's two stores conserve every
                    // count and a permutation invariant is preserved across the body (shared with the method-body
                    // executor; the loop pass previously omitted this).
                    enc.emitStoreCountLaw(arr, oldA, newA, idx, val, enc.listElementSort(arr), translatedCountVals(enc))
                }
                return
            }
            throw new UnsupportedConstructException(
                "assignment to a non-variable target (line ${st.lineNumber})")
        }
        // Phase 45c — a standalone list mutation as an ExpressionStatement, e.g.
        // {@code positive.add(x)} inside the loop body. Thread the same SMT effects
        // {@code VerifyChecker.applyListMutation} does, sans count-law tracking (the loop
        // pass doesn't carry countVals).
        if (e instanceof MethodCallExpression) {
            if (applyListMutationInLoop((MethodCallExpression) e, enc, s)) return
            // A rely-step call (havoc the shared frame + assume its @Ensures): handed off to VerifyChecker's
            // caller-side framing via the installed handler, so a loop body under @UnderRely is modelled with the
            // environment running per iteration. Returns false for any other (uncontracted) call → loud skip below.
            LoopCallHandler h = callHandler.get()
            if (h != null && h.handle((MethodCallExpression) e, enc, s)) return
        }
        throw new UnsupportedConstructException(
            "unsupported statement in loop region (line ${st.lineNumber})")
    }

    /**
     * Phase 45c — minimal list-mutation handling for loop bodies. Mirrors
     * {@code VerifyChecker.applyListMutation}'s effect on the size/array oracles + factory
     * record, sans count-law assertions (the loop pass doesn't track {@code countVals}).
     * Returns true if the call was recognised as a list mutation; false otherwise so the
     * caller can throw an honest skip.
     */
    private static boolean applyListMutationInLoop(MethodCallExpression mce, Encoder enc, SmtSession s) {
        Expression recv = mce.objectExpression
        if (!(recv instanceof VariableExpression)) return false
        String name = ((VariableExpression) recv).name
        String m = mce.methodAsString
        List<Expression> args = mce.arguments instanceof ArgumentListExpression ?
            ((ArgumentListExpression) mce.arguments).expressions :
            Collections.<Expression>emptyList()
        Object one = s.intLit(1L), zero = s.intLit(0L)
        if (m == 'add' && args.size() == 1) {
            Object x = enc.translate(args.get(0))
            if (x == null) return false
            Object oldSize = enc.sizeOf(name)
            Object oldArr = enc.arrayFor(name)
            enc.bindArray(name, s.store(oldArr, oldSize, x))
            enc.bindSize(name, s.plus(oldSize, one))
            enc.clearFactoryRecord(name)
            return true
        }
        if (m == 'clear' && args.isEmpty()) {
            enc.bindSize(name, zero)
            enc.clearFactoryRecord(name)
            return true
        }
        if ((m == 'removeLast' || m == 'pop') && args.isEmpty()) {
            Object oldSize = enc.sizeOf(name)
            enc.bindSize(name, s.minus(oldSize, one))
            enc.clearFactoryRecord(name)
            return true
        }
        false
    }

    /**
     * Translate {@code rhs} under the current store and re-bind {@code name} —
     * the SSA step, so subsequent reads see the new handle. If the RHS is
     * outside the fragment (e.g. it reads an array element), havoc {@code name}
     * instead of aborting: its value becomes unknown but the loop's other
     * variables — and thus its invariant and any bounds obligation that depends
     * only on them — can still be reasoned about.
     */
    private static void rebind(Encoder enc, String name, Expression rhs) {
        // Phase 38b/35 — try the materialised-set and factory-record paths first, so a loop
        // prefix like {@code List<Integer> positive = []} pins the size/nullity oracles the
        // invariant check sees. Without this, the assign would havoc {@code positive} and the
        // invariant {@code positive.size() <= i} would refute at iteration 0.
        if (enc.tryMaterialiseSetBinopAssign(name, rhs)) return
        if (enc.tryRecordFactoryAssign(name, rhs)) return
        Object h = enc.translate(rhs)
        if (h == null) enc.havoc(name)
        else enc.bind(name, h)
    }
}
