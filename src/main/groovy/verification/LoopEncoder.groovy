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
import org.codehaus.groovy.ast.expr.TupleExpression
import org.codehaus.groovy.ast.expr.BinaryExpression
import org.codehaus.groovy.ast.expr.DeclarationExpression
import org.codehaus.groovy.ast.expr.TernaryExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.PostfixExpression
import org.codehaus.groovy.ast.expr.PropertyExpression
import org.codehaus.groovy.ast.expr.StaticMethodCallExpression
import org.codehaus.groovy.ast.expr.PrefixExpression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.EmptyStatement
import org.codehaus.groovy.ast.stmt.AssertStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.IfStatement
import org.codehaus.groovy.ast.stmt.LoopingStatement
import org.codehaus.groovy.ast.stmt.ReturnStatement
import org.codehaus.groovy.ast.stmt.ThrowStatement
import org.codehaus.groovy.ast.stmt.BreakStatement
import org.codehaus.groovy.ast.stmt.ContinueStatement
import org.codehaus.groovy.ast.stmt.WhileStatement
import org.codehaus.groovy.ast.stmt.ForStatement
import org.codehaus.groovy.ast.stmt.DoWhileStatement
import org.codehaus.groovy.ast.stmt.SwitchStatement
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.CodeVisitorSupport
import org.codehaus.groovy.ast.stmt.Statement
import org.codehaus.groovy.syntax.Token
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
    // Phase 326 — the appended update itself (null for while/do-while), so a tail if/else chain just ahead of it is
    // still found as the body's tail (Phase 49c's exit lifting).
    Statement update = null
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
    // Phase 310 — the loop came from `xs.each { … }` / `.eachWithIndex { … }`: its body is a CLOSURE's code, where
    // `return` ends only the current element's call (like `continue`), never the method. The loop-site builder
    // uses this to keep such a `return` from being read as a method early-exit.
    boolean fromEach = false
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
     * Phase 311 — replay a region to reach a LATER point on the same path (an obligation's {@code preceding}, a
     * call site's in-loop prefix). Unlike {@link #symExec} — the strict walk the loop VCs use, which rejects an exit
     * so an unrecognised one loud-skips — an {@code if} whose branch always leaves (return / throw / break /
     * continue) is fine here: the point we're heading for lies on the CONTINUING path, so that branch's condition
     * was false (or the else-branch's true) and the other branch is replayed as straight-line code. Both branches
     * leaving makes the rest of the region unreachable. Anything else defers to {@link #symExec}; an exception
     * propagates so the caller can havoc what it couldn't replay.
     */
    static void replay(List<Statement> stmts, Encoder enc, SmtSession s) {
        stmts = Encoder.expandIncDecStatements(stmts)
        for (Statement st : stmts) {
            if (st instanceof BlockStatement) { replay(((BlockStatement) st).statements, enc, s); continue }
            if (st instanceof IfStatement) {
                IfStatement ifs = (IfStatement) st
                Statement elseBlk = ifs.elseBlock
                boolean hasElse = elseBlk != null && !(elseBlk instanceof EmptyStatement)
                boolean thenLeaves = leaves(ifs.ifBlock), elseLeaves = hasElse && leaves(elseBlk)
                if (thenLeaves || elseLeaves) {
                    Object cond = tr(enc, ifs.booleanExpression, "if-condition")
                    if (thenLeaves && elseLeaves) { s.assertExpr(s.boolLit(false)); return }
                    if (thenLeaves) {
                        s.assertExpr(s.not(cond))
                        if (hasElse) replay(asList(elseBlk), enc, s)
                    } else {
                        s.assertExpr(cond)
                        replay(asList(ifs.ifBlock), enc, s)
                    }
                    continue
                }
            }
            symExec([st] as List<Statement>, enc, s)
        }
    }

    /** True iff {@code body} has a {@code break} that leaves THIS loop: not inside a nested loop, switch or closure. */
    static boolean containsLoopBreak(List<Statement> body) {
        boolean[] found = [false]
        CodeVisitorSupport v = new CodeVisitorSupport() {
            @Override void visitBreakStatement(BreakStatement b) { found[0] = true }
            @Override void visitWhileLoop(WhileStatement w) { }
            @Override void visitForLoop(ForStatement f) { }
            @Override void visitDoWhileLoop(DoWhileStatement d) { }
            @Override void visitSwitch(SwitchStatement sw) { }
            @Override void visitClosureExpression(ClosureExpression ce) { }
        }
        for (Statement st : body) st.visit(v)
        found[0]
    }

    /** True iff control never falls out of {@code st}: it ends in return / throw / break / continue, or is an
     *  if/else whose branches both leave. */
    static boolean leaves(Statement st) {
        if (st instanceof ReturnStatement || st instanceof ThrowStatement ||
            st instanceof BreakStatement || st instanceof ContinueStatement) return true
        if (st instanceof BlockStatement) {
            List<Statement> ss = ((BlockStatement) st).statements
            return !ss.isEmpty() && leaves(ss.get(ss.size() - 1))
        }
        if (st instanceof IfStatement) {
            IfStatement ifs = (IfStatement) st
            return ifs.elseBlock != null && !(ifs.elseBlock instanceof EmptyStatement) &&
                leaves(ifs.ifBlock) && leaves(ifs.elseBlock)
        }
        false
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
        // Phase 312 — inv ∧ ¬guard is the post-state of a loop that only leaves through its guard. Phase 324 — a
        // loop that also leaves by a top-level `if (c) break` / `if (c) { lead; break }` has one more exit state per
        // break; anything else that breaks still skips loudly.
        List<Integer> breaks = new ArrayList<Integer>()
        if (containsLoopBreak(inner.body)) {
            for (int k = 0; k < inner.body.size(); k++) {
                Statement st = inner.body.get(k)
                if (breakLead(st) != null) breaks.add(k)
                else if (containsLoopBreak([st])) {
                    throw new UnsupportedConstructException(
                        "a `break` in a nested loop is modelled only as a top-level `if (c) break` or `if (c) { …; break }`")
                }
            }
        }
        Set<String> scalars = new HashSet<String>()
        Set<String> arrays = new HashSet<String>()
        Set<String> lists = new HashSet<String>()
        if (!innerFrame(inner.body, scalars, arrays, lists)) {
            throw new UnsupportedConstructException(
                "nested loop writes a field/collection or unbounded construct — not yet supported")
        }
        for (String nm : scalars) enc.havoc(nm)
        // Phase 186 — a written subscript target may be a MAP, whose havoc must refresh both the value
        // array and the key-set (an Int-sorted havocArray on a non-Int-keyed map sort-crashes).
        for (String nm : arrays) { if (enc.isMapName(nm)) enc.havocMap(nm) else enc.havocArray(nm) }
        // Phase 252 — a LIST-BUILDING loop (`q.add(x)` / `clear` / `removeLast` / `pop`) changes both the
        // contents and the length: havoc both oracles, then its invariant ∧ ¬guard characterises the list
        // (a producer loop's `q.size() == i - a` and its element relation survive into the loop after it).
        for (String nm : lists) { enc.havocArray(nm); enc.havocSize(nm); if (enc.isSetName(nm)) enc.havocSet(nm) }   // Phase 342 — a set's own model too
        if (breaks.isEmpty()) {
            s.assertExpr(conj(enc, s, inner.invariants))
            s.assertExpr(s.not(tr(enc, inner.guard, "inner-loop guard")))
            return
        }
        summarizeWithBreaks(inner, breaks, enc, s)
    }

    private static int breakSelCounter = 0

    /**
     * Phase 324 — the post-state of a nested loop that can also leave by {@code break}. Its writes are havocked
     * (state H, above); then one alternative per way out, chosen by a fresh selector {@code sel}:
     * <ul>
     *   <li>{@code sel == 0}, the natural exit: {@code inv ∧ ¬guard} in H;</li>
     *   <li>{@code sel == k}, break k: H is the state at the start of the breaking iteration, so
     *       {@code inv ∧ guard}, the body up to the break replayed with earlier exits not taken, the break's
     *       condition, then its lead.</li>
     * </ul>
     * Each alternative runs under {@link SmtSession#pushAssertGuard} ({@code sel == k}), so what its replay
     * asserts holds only there, and the bindings are merged as an ite over {@code sel}. A break's state isn't
     * required to satisfy the invariant, as in Dafny. Sound because H ranges over every state the loop can be in
     * at an iteration start (inv holds there: the inner loop's establishment and preservation are checked).
     */
    private static void summarizeWithBreaks(LoopSpec inner, List<Integer> breaks, Encoder enc, SmtSession s) {
        Object sel = s.intVar('brk#sel' + (breakSelCounter++))
        s.assertExpr(s.and([s.le(s.intLit(0L), sel), s.le(sel, s.intLit((long) breaks.size()))]))
        Encoder.EncoderSnapshot h = enc.snapshotState()
        List<Encoder.EncoderSnapshot> states = new ArrayList<Encoder.EncoderSnapshot>()
        List<Object> sels = new ArrayList<Object>()
        Object natural = s.eq(sel, s.intLit(0L))
        s.pushAssertGuard(natural)
        try {
            s.assertExpr(conj(enc, s, inner.invariants))
            s.assertExpr(s.not(tr(enc, inner.guard, "inner-loop guard")))
        } finally { s.popAssertGuard() }
        states.add(h); sels.add(natural)
        for (int b = 0; b < breaks.size(); b++) {
            int k = breaks.get(b)
            enc.restoreState(h)
            Object here = s.eq(sel, s.intLit((long) (b + 1)))
            s.pushAssertGuard(here)
            try {
                s.assertExpr(conj(enc, s, inner.invariants))
                s.assertExpr(tr(enc, inner.guard, "inner-loop guard"))
                replay(new ArrayList<Statement>(inner.body.subList(0, k)), enc, s)
                IfStatement bk = (IfStatement) inner.body.get(k)
                s.assertExpr(tr(enc, bk.booleanExpression, "break condition"))
                symExec(breakLead(bk), enc, s)
            } finally { s.popAssertGuard() }
            states.add(enc.snapshotState()); sels.add(here)
        }
        // Fold the alternatives into one state, last first: acc = sel == k ? state_k : acc.
        Encoder.EncoderSnapshot acc = states.get(states.size() - 1)
        enc.restoreState(acc)
        for (int k = states.size() - 2; k >= 0; k--) {
            mergeStates(states.get(k), acc, h, sels.get(k), enc, s)
            acc = enc.snapshotState()
        }
    }

    /** The lead of a top-level break exit — {@code if (c) break} (empty) or {@code if (c) { lead; break }} with no
     *  else — or null. The lead may not itself exit or loop. */
    static List<Statement> breakLead(Statement st) {
        if (!(st instanceof IfStatement)) return null
        IfStatement ifs = (IfStatement) st
        if (ifs.elseBlock != null && !(ifs.elseBlock instanceof EmptyStatement)) return null
        Statement t = ifs.ifBlock
        if (t instanceof BreakStatement) return ((BreakStatement) t).label == null ? Collections.<Statement> emptyList() : null
        if (!(t instanceof BlockStatement)) return null
        List<Statement> ss = ((BlockStatement) t).statements
        if (ss.isEmpty() || !(ss.get(ss.size() - 1) instanceof BreakStatement) ||
            ((BreakStatement) ss.get(ss.size() - 1)).label != null) return null
        List<Statement> lead = new ArrayList<Statement>(ss.subList(0, ss.size() - 1))
        for (Statement l : lead) if (leaves(l) || containsLoopBreak([l]) || l instanceof LoopingStatement) return null
        lead
    }

    /** Partition a nested loop body's writes into scalar names and array names, or false if it writes
     *  anything that isn't a plain scalar local or an `a[idx] = v` array element (so havocking the two
     *  sets is a complete account of the inner loop's effect). */
    static boolean innerFrame(List<Statement> stmts, Set<String> scalars, Set<String> arrays) {
        innerFrame(stmts, scalars, arrays, new HashSet<String>())
    }
    /** As above, with list mutators accepted into {@code lists} (Phase 252 — size-changing writes). */
    static boolean innerFrame(List<Statement> stmts, Set<String> scalars, Set<String> arrays, Set<String> lists) {
        if (stmts == null) return true
        for (Statement st : stmts) if (!innerFrameStmt(st, scalars, arrays, lists)) return false
        true
    }
    /**
     * Phase 340 — writes the loop body models as the assignments they are: {@code this.f = v} is {@code f = v} (the
     * name a bare {@code f} reads), a map's {@code m.put(k, v)} is {@code m[k] = v}, and a list's {@code xs.set(i, v)}
     * is {@code xs[i] = v}, an in-bounds store, since {@code set} throws otherwise (its result unused as a statement).
     * Anything else is returned as it is.
     */
    static Expression asStore(Expression e, Encoder enc) {
        if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.ASSIGN) {
            BinaryExpression be = (BinaryExpression) e
            Expression t = be.leftExpression
            if (t instanceof PropertyExpression && ((PropertyExpression) t).objectExpression instanceof VariableExpression &&
                ((VariableExpression) ((PropertyExpression) t).objectExpression).name == 'this') {
                VariableExpression f = new VariableExpression(((PropertyExpression) t).propertyAsString)
                f.setSourcePosition(t)
                BinaryExpression r = new BinaryExpression(f, be.operation, be.rightExpression)
                r.setSourcePosition(be)
                return r
            }
            return e
        }
        if (!(e instanceof MethodCallExpression)) return e
        MethodCallExpression m = (MethodCallExpression) e
        if (!(m.objectExpression instanceof VariableExpression) || !(m.arguments instanceof TupleExpression)) return e
        String recv = ((VariableExpression) m.objectExpression).name
        List<Expression> args = ((TupleExpression) m.arguments).expressions
        if (args.size() != 2) return e
        boolean store = (m.methodAsString == 'put' && enc.isMapName(recv)) || (m.methodAsString == 'set' && enc.isListName(recv))
        if (!store) return e
        BinaryExpression at = new BinaryExpression(m.objectExpression, Token.newSymbol(Types.LEFT_SQUARE_BRACKET, -1, -1), args.get(0))
        at.setSourcePosition(m)
        BinaryExpression r = new BinaryExpression(at, Token.newSymbol(Types.ASSIGN, -1, -1), args.get(1))
        r.setSourcePosition(m)
        r
    }

    private static final List<String> LIST_MUTATORS = ['add', 'clear', 'removeLast', 'pop'].asImmutable()
    private static final List<String> CONTENT_WRITERS = ['put', 'set'].asImmutable()
    private static boolean innerFrameStmt(Statement st, Set<String> scalars, Set<String> arrays, Set<String> lists) {
        if (st == null || st instanceof EmptyStatement) return true
        if (st instanceof BlockStatement) return innerFrame(((BlockStatement) st).statements, scalars, arrays, lists)
        if (st instanceof IfStatement) {
            IfStatement ifs = (IfStatement) st
            return innerFrameStmt(ifs.ifBlock, scalars, arrays, lists) &&
                   (ifs.elseBlock == null || innerFrameStmt(ifs.elseBlock, scalars, arrays, lists))
        }
        if (st instanceof AssertStatement) return true      // Phase 252 — an in-loop assert writes nothing
        if (st instanceof ExpressionStatement) {
            Expression e = ((ExpressionStatement) st).expression
            List<MethodCallExpression> adds = Encoder.leftShiftAdds(e)   // Phase 341 — xs << v appends
            if (adds != null) { lists.add(((VariableExpression) adds.get(0).objectExpression).name); return true }
            if (e instanceof MethodCallExpression) {          // Phase 252 — a list mutator statement
                MethodCallExpression m = (MethodCallExpression) e
                if (m.objectExpression instanceof VariableExpression && m.methodAsString in LIST_MUTATORS) {
                    lists.add(((VariableExpression) m.objectExpression).name); return true
                }
                // Phase 340 — a content write that keeps the size: a map's put/remove (havocMap via `arrays`, Phase
                // 186) or a list's set. Its arguments must write nothing themselves.
                if (m.objectExpression instanceof VariableExpression && m.methodAsString in CONTENT_WRITERS &&
                    guardWritesNothing(m.arguments)) {
                    arrays.add(((VariableExpression) m.objectExpression).name); return true
                }
            }
            return innerFrameExpr(e, scalars, arrays)
        }
        // Phase 109 — a `return` inside the inner loop writes nothing to the *outer* state (it transfers
        // control out of the method). On the fall-through path — the only one where the outer loop continues
        // past the inner loop — the inner loop completed without returning, so the summary (inner_inv ∧
        // ¬inner_guard) is unaffected. The return's own @Ensures is discharged separately (verifyNestedLoops).
        if (st instanceof ReturnStatement) return true
        if (st instanceof BreakStatement) return true       // Phase 324 — a break writes nothing
        // Phase 338 — an annotated loop inside the summarised one (an earlier outer loop that holds a nested loop,
        // summarised for a later sequential loop) writes what its init, guard and body write. It is verified at its
        // own site; here only its writes matter, havocked with the rest.
        LoopSpec nested = (LoopSpec) st.getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY)
        if (nested != null) {
            if (nested.init != null && !innerFrame(nested.init, scalars, arrays, lists)) return false
            return guardWritesNothing(nested.guard) && innerFrame(nested.body, scalars, arrays, lists)
        }
        return false   // an unannotated loop / unknown statement → bail
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
    private static final Set<String> READ_ONLY_CALLS = ['size', 'length', 'isEmpty', 'get', 'getAt', 'contains'] as Set

    /** Phase 338 — a loop guard that writes nothing: no assignment, no {@code ++}/{@code --}, only read-only calls. */
    private static boolean guardWritesNothing(Expression g) {
        if (g == null) return true
        boolean[] ok = [true] as boolean[]
        g.visit(new CodeVisitorSupport() {
            @Override void visitBinaryExpression(BinaryExpression be) {
                if (Types.ofType(be.operation.type, Types.ASSIGNMENT_OPERATOR)) ok[0] = false
                super.visitBinaryExpression(be)
            }
            @Override void visitPostfixExpression(PostfixExpression pe) { ok[0] = false }
            @Override void visitPrefixExpression(PrefixExpression pe) { ok[0] = false }
            @Override void visitMethodCallExpression(MethodCallExpression m) {
                if (!(m.methodAsString in READ_ONLY_CALLS)) ok[0] = false
                super.visitMethodCallExpression(m)
            }
            @Override void visitStaticMethodCallExpression(StaticMethodCallExpression m) { ok[0] = false }
            @Override void visitClosureExpression(ClosureExpression c) { ok[0] = false }
        })
        ok[0]
    }

    private static boolean innerFrameTarget(Expression t, Set<String> scalars, Set<String> arrays) {
        if (t instanceof VariableExpression) { scalars.add(((VariableExpression) t).name); return true }
        // Phase 340 — `this.f = v` writes the field f, the name a bare `f` reads
        if (t instanceof PropertyExpression && ((PropertyExpression) t).objectExpression instanceof VariableExpression &&
            ((VariableExpression) ((PropertyExpression) t).objectExpression).name == 'this') {
            scalars.add(((PropertyExpression) t).propertyAsString); return true
        }
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
        // Phase 344 — what a branch assumes (a nested loop's inv ∧ ¬guard, an assert) holds only on its path: unguarded,
        // a loop in one branch whose invariant the other path breaks made that path vacuous
        // Then branch.
        Statement thenBlk = ifs.ifBlock
        if (thenBlk != null && !(thenBlk instanceof EmptyStatement)) {
            s.pushAssertGuard(cond)
            try { symExec(asList(thenBlk), enc, s) } finally { s.popAssertGuard() }
        }
        Encoder.EncoderSnapshot afterThen = enc.snapshotState()
        // Restore + else branch.
        enc.restoreState(entry)
        Statement elseBlk = ifs.elseBlock
        if (elseBlk != null && !(elseBlk instanceof EmptyStatement)) {
            s.pushAssertGuard(s.not(cond))
            try { symExec(asList(elseBlk), enc, s) } finally { s.popAssertGuard() }
        }
        mergeStates(afterThen, enc.snapshotState(), entry, cond, enc, s)
    }

    /** ITE-combine two states into the encoder, which must currently hold {@code afterElse}: each binding that
     *  differs becomes {@code cond ? then : else} (absent ones fall back to {@code entry}). */
    private static void mergeStates(Encoder.EncoderSnapshot afterThen, Encoder.EncoderSnapshot afterElse,
                                    Encoder.EncoderSnapshot entry, Object cond, Encoder enc, SmtSession s) {
        // ITE-combine: for each map, walk the union of keys touched in either branch.
        iteCombineMap(afterThen.env, afterElse.env, entry.env, cond, enc, s,
            { String n, Object h -> enc.bind(n, h) }, true)
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
                                      SmtSession s, Closure<Void> apply, boolean scalars = false) {
        Set<String> names = new LinkedHashSet<String>()
        names.addAll(thenMap.keySet())
        names.addAll(elseMap.keySet())
        for (String n : names) {
            Object thenV = thenMap.get(n)
            Object elseV = elseMap.get(n)
            Object entryV = entryMap.get(n)
            // Phase 339 — a scalar first written in one branch, unread before the if, has no entry binding: its
            // entry value is the free value any later read gets (varFor), so `if (c) r = i` is `r = c ? i : r`. It
            // used to be skipped, dropping the write (r read as its free value after the if: sound, but it lost r = i).
            if (entryV == null && scalars && !n.contains('\$')) {
                Object other = thenV != null ? thenV : elseV
                Object free = enc.varFor(n)
                if (other != null && free != null && s.isBool(other) == s.isBool(free) && s.isReal(other) == s.isReal(free)) entryV = free
            }
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
    static Expression resultExpr(List<Statement> stmts, Encoder enc, SmtSession s, boolean voidMethod = false) {
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
            } else if (st instanceof AssertStatement && !last && st.getNodeMetaData(ChannelDesugar.ASSUME_ONLY_KEY) != null) {
                // Phase 334 — an assume-only assert after the loop (a branch condition) is a fact from here on
                Object c = enc.translate(((AssertStatement) st).booleanExpression)
                if (c != null) s.assertExpr(c)
            } else if (last && st instanceof IfStatement && returnedBy(st) != null) {
                result = returnedBy(st)   // Phase 319 — `if (c) return a else return b` is `return c ? a : b`
                break
            } else {
                throw new UnsupportedConstructException(
                    "unsupported statement ${st.class.simpleName} after loop (line ${st.lineNumber})")
            }
        }
        if (result == null && voidMethod) return null   // Phase 340 — a void method's @Ensures reads state, not result
        if (result == null) {
            throw new UnsupportedConstructException("no return value after loop")
        }
        return result
    }

    /** Phase 319 — the value a statement that only returns returns: a `return e`, a block holding just one, or an
     *  `if`/`else` (`else if` chains too) both of whose branches only return — as the matching ternary. Null for
     *  anything else, including an `if` without an `else` (it falls through). */
    static Expression returnedBy(Statement st) {
        if (st instanceof ReturnStatement) return ((ReturnStatement) st).expression
        if (st instanceof BlockStatement && ((BlockStatement) st).statements.size() == 1) return returnedBy(((BlockStatement) st).statements.get(0))
        if (st instanceof IfStatement) {
            IfStatement i = (IfStatement) st
            if (i.elseBlock == null || i.elseBlock instanceof EmptyStatement) return null
            Expression a = returnedBy(i.ifBlock), b = returnedBy(i.elseBlock)
            if (a == null || b == null) return null
            TernaryExpression t = new TernaryExpression(i.booleanExpression, a, b)
            t.setSourcePosition(st)
            return t
        }
        null
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
        e = asStore(e, enc)   // Phase 340 — this.f = v, m.put(k, v), xs.set(i, v)
        // Phase 341 — xs << a << b on a list: xs.add(a), then xs.add(b)
        List<MethodCallExpression> adds = Encoder.leftShiftAdds(e)
        String shiftRecv = adds != null ? ((VariableExpression) adds.get(0).objectExpression).name : null
        if (adds != null && (enc.isListTyped(shiftRecv) || enc.isSetName(shiftRecv))) {   // Phase 342 — a set's << inserts
            for (MethodCallExpression add : adds) {
                if (!applyListMutationInLoop(add, enc, s)) {
                    throw new UnsupportedConstructException("unsupported statement in loop region (line ${st.lineNumber})")
                }
            }
            return
        }
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
                    enc.emitStoreSumLaw(oldA, newA, idx, val, enc.listElementSort(arr))   // Phase 321
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
        // Phase 342 — a set is not a list: its add/remove went down the append path below, which wrote only the list
        // oracles, so the set model saw no change (an add left st.isEmpty() provable). Its own store and
        // cardinality law, as the straight-line replay does; any other set mutation (clear, addAll) is refused.
        if (enc.isSetName(name)) {
            if ((m != 'add' && m != 'remove') || args.size() != 1) return false
            Object elem = enc.translateInSort(args.get(0), enc.setElementSort(name))
            if (elem == null) return false
            boolean adding = m == 'add'
            Object oldS = enc.setFor(name)
            Object newS = s.store(oldS, elem, adding ? one : zero)
            Object memOld = enc.member(oldS, elem)
            Object delta = adding ? s.ite(memOld, zero, one) : s.ite(memOld, one, zero)
            s.assertExpr(s.eq(enc.cardOf(newS), adding ? s.plus(enc.cardOf(oldS), delta) : s.minus(enc.cardOf(oldS), delta)))
            enc.bindSet(name, newS)
            return true
        }
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
