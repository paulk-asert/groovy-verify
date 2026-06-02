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

import groovy.contracts.Ensures
import groovy.contracts.Requires
import groovy.transform.CompileStatic
import org.codehaus.groovy.ast.AnnotationNode
import org.codehaus.groovy.ast.ASTNode
import org.codehaus.groovy.ast.ClassCodeVisitorSupport
import org.codehaus.groovy.ast.ClassHelper
import org.codehaus.groovy.ast.ClassNode
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.Parameter
import org.codehaus.groovy.ast.Variable
import org.codehaus.groovy.ast.builder.AstBuilder
import org.codehaus.groovy.ast.expr.BinaryExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.MethodCall
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.StaticMethodCallExpression
import org.codehaus.groovy.ast.expr.DeclarationExpression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.EmptyStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.IfStatement
import org.codehaus.groovy.ast.stmt.ReturnStatement
import org.codehaus.groovy.ast.stmt.Statement
import org.codehaus.groovy.control.CompilePhase
import org.codehaus.groovy.control.SourceUnit
import org.codehaus.groovy.syntax.Types
import org.codehaus.groovy.transform.stc.StaticTypeCheckingVisitor
import org.codehaus.groovy.transform.stc.TypeCheckingExtension

/**
 * SMT-backed precondition verifier — the spike entry point.
 *
 * Usage from consumer code:
 *   {@code @TypeChecked(extensions = 'verification.VerifyChecker')}
 *
 * Contracts are authored as stock {@code groovy.contracts.@Requires}/
 * {@code @Ensures}; {@link ContractExpansionTransform} captures each closure's
 * verbatim source into a {@code @ContractSource} that this checker reads back
 * (it survives into bytecode, so a callee compiled in another module still
 * carries its contract).
 *
 * What this does on every method call inside the annotated scope:
 *   1. Look up the called method's {@code @Requires} precondition and read
 *      its captured text from {@code @ContractSource}.
 *   2. Bind the contract's formal parameters to the actual-argument
 *      expressions at this call site.
 *   3. Harvest the path condition from enclosing {@code if}
 *      statements (precomputed by {@link PathFacts}).
 *   4. Ask Z3 whether {@code path ∧ ¬precond} is satisfiable.
 *        - UNSAT  → verified, no diagnostic.
 *        - SAT    → refuted, emit error with counterexample.
 *        - UNKNOWN → emit warning ("could not decide").
 *
 * Beyond explicit contracts, every method body in scope is also checked for the
 * implicit preconditions every program carries — array index in bounds, divisor
 * non-zero, dereferenced receiver non-null ({@link #verifyImplicitObligations}) —
 * discharged with the same assume-facts / refute-negation machinery.
 *
 * Anything outside the supported fragment becomes a "skipped"
 * warning rather than a silent pass — borrowed from OpenJML's ESC
 * mode discipline.
 */
@CompileStatic
class VerifyChecker extends TypeCheckingExtension {

    private static final ClassNode REQUIRES_TYPE = ClassHelper.make(Requires)
    private static final ClassNode ENSURES_TYPE = ClassHelper.make(Ensures)
    private static final ClassNode CONTRACT_SOURCE_TYPE = ClassHelper.make(ContractSource)

    private SmtBackend backend
    private PathFacts currentFacts
    /** The method currently being type-checked; its own @Requires is a given at any call site in its body. */
    private MethodNode currentMethod

    VerifyChecker(StaticTypeCheckingVisitor visitor) {
        super(visitor)
    }

    @Override
    void setup() {
        backend = new Z3Backend(2000)
    }

    @Override
    boolean beforeVisitMethod(MethodNode node) {
        currentFacts = new PathFacts()
        currentMethod = node
        if (node.code != null) {
            try {
                node.code.visit(currentFacts)
            } catch (Throwable t) {
                // Defensive: if precomputation fails, fall back to
                // "no facts known". The spike prefers continuing
                // verification over hard-failing the build.
                currentFacts = new PathFacts()
            }
        }
        false  // false = also run the default type-check visit
    }

    @Override
    void afterVisitMethod(MethodNode node) {
        try {
            Statement body = (Statement) node.getNodeMetaData(
                ContractExpansionTransform.ORIGINAL_BODY_KEY)
            if (body == null) body = node.code

            LoopSite site
            try {
                site = findLoopSite(body)
            } catch (UnsupportedConstructException e) {
                addStaticTypeError(Reporter.formatLoopSkipped(node.name, e.message), node)
                return
            }

            // Implicit safety obligations (array bounds, division by zero, null
            // dereference) fire on every method, contract or not. For an
            // annotated loop they are discharged *with the invariant in scope*
            // (Phase 5b); otherwise via the per-method value-flow/havoc pass
            // (Phase 5a). Best-effort: never fail the build over them.
            try {
                if (site != null) verifyLoopObligations(node, site)
                else verifyImplicitObligations(node)
            } catch (Throwable ignored) {
            }

            if (site != null) verifyLoop(node, site)
            else verifyPostcondition(node)
        } finally {
            currentFacts = null
            currentMethod = null
        }
    }

    // ---- Phase 1: implicit safety obligations ----

    /**
     * Discharge the implicit preconditions that every program carries: an array
     * index is in bounds, a divisor is non-zero, a dereferenced receiver is
     * non-null. No annotation surface — these fire automatically on the relevant
     * AST shapes inside the method body. Each obligation is checked exactly like a
     * call-site precondition: assume the method's own {@code @Requires} and the
     * enclosing path facts, assert the negation of the obligation, and ask Z3
     * whether that is satisfiable (a model is a counterexample).
     *
     * The analysis is path-sensitive (it honours enclosing {@code if}s) but not
     * value-flow-sensitive: like the call-site checker, it does not track local
     * assignments, so the canonical demos are guard-based. Bodies are read from
     * the clean CONVERSION snapshot so groovy-contracts' injected asserts are not
     * mistaken for user dereferences.
     */
    private void verifyImplicitObligations(MethodNode node) {
        Statement body = (Statement) node.getNodeMetaData(
            ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (body == null) body = node.code
        if (body == null) return

        Expression reqAst = findRequires(node) != null ? contractAstFor(node, 'requires') : null

        // Phase 5a — value-flow. When the whole body is in the value-flow
        // fragment (straight-line + if/else + single-assignment locals, no
        // loops), discharge each obligation under the symbolic store that
        // *reaches* it, so safety implied by a preceding assignment — not only
        // by a guard — is provable. Anything outside that fragment (a loop, a
        // re-assignment, an unsupported statement) throws, and we fall back to
        // the path-fact-only havoc pass: sound, but value-flow-blind.
        try {
            List<VfObligation> sites = new ArrayList<VfObligation>()
            collectVfObligations(topStatements(body),
                new ArrayList<Guard>(), new ArrayList<Assign>(),
                new HashSet<String>(), sites)
            for (VfObligation v : sites) dischargeVfObligation(node, v, reqAst)
        } catch (UnsupportedConstructException ignored) {
            dischargeObligationsHavoc(node, body, reqAst)
        }
    }

    /** The value-flow-blind fallback: assume @Requires + enclosing ifs only (pre-Phase-5 behaviour). */
    private void dischargeObligationsHavoc(MethodNode node, Statement body, Expression reqAst) {
        PathFacts pf = new PathFacts()
        try {
            body.visit(pf)
        } catch (Throwable t) {
            pf = new PathFacts()
        }
        ObligationCollector col = new ObligationCollector()
        try {
            body.visit(col)
        } catch (Throwable t) {
            return
        }
        for (IndexSite s : col.indexSites)  dischargeIndex(s, pf, reqAst)
        for (DivideSite s : col.divideSites) dischargeDivide(s, pf, reqAst)
        for (DerefSite s : col.derefSites)  dischargeDeref(s, pf, reqAst)
    }

    /** An implicit obligation paired with the guards and single-assignment bindings that reach it. */
    @CompileStatic
    private static class VfObligation {
        Object site                 // IndexSite | DivideSite | DerefSite
        List<Guard> guards
        List<Assign> assigns
    }

    /**
     * Walk the value-flow fragment, snapshotting for each implicit obligation
     * the guards and single-assignment bindings in effect at the point it is
     * evaluated. Forks at each {@code if} (the condition's own obligations are
     * evaluated before the branch); statements after an {@code if} continue with
     * the pre-{@code if} store, so a variable assigned only inside a branch is
     * havoc afterwards (sound — we never claim a merged value). Throws
     * {@link UnsupportedConstructException} on loops, re-assignment, or any
     * unsupported statement so the caller can fall back to the havoc pass.
     */
    private void collectVfObligations(List<Statement> stmts,
                                      List<Guard> guards, List<Assign> assigns,
                                      Set<String> assigned, List<VfObligation> out) {
        for (Statement st : stmts) {
            if (st instanceof BlockStatement) {
                collectVfObligations(((BlockStatement) st).statements, guards, assigns, assigned, out)
                continue
            }
            if (st instanceof IfStatement) {
                IfStatement ifs = (IfStatement) st
                Expression cond = ifs.booleanExpression
                scanObligations(cond, guards, assigns, out)
                collectVfObligations(topStatements(ifs.ifBlock),
                    append(guards, new Guard(cond, true)),
                    new ArrayList<Assign>(assigns), new HashSet<String>(assigned), out)
                Statement elseBlk = ifs.elseBlock
                if (elseBlk != null && !(elseBlk instanceof EmptyStatement)) {
                    collectVfObligations(topStatements(elseBlk),
                        append(guards, new Guard(cond, false)),
                        new ArrayList<Assign>(assigns), new HashSet<String>(assigned), out)
                }
                continue
            }
            if (st instanceof ReturnStatement) {
                scanObligations(((ReturnStatement) st).expression, guards, assigns, out)
                return   // rest of this list is dead on this path
            }
            if (st instanceof ExpressionStatement) {
                Expression e = ((ExpressionStatement) st).expression
                if (e instanceof DeclarationExpression) {
                    DeclarationExpression de = (DeclarationExpression) e
                    if (!(de.leftExpression instanceof VariableExpression)) {
                        throw new UnsupportedConstructException("multi-variable declaration")
                    }
                    String name = ((VariableExpression) de.leftExpression).name
                    scanObligations(de.rightExpression, guards, assigns, out)
                    if (!assigned.add(name)) throw new UnsupportedConstructException("re-assignment of '${name}'")
                    if (de.rightExpression != null) assigns.add(new Assign(name, de.rightExpression))
                    continue
                }
                if (e instanceof BinaryExpression &&
                    ((BinaryExpression) e).operation.type == Types.ASSIGN) {
                    BinaryExpression be = (BinaryExpression) e
                    if (!(be.leftExpression instanceof VariableExpression)) {
                        throw new UnsupportedConstructException("assignment to a non-variable target")
                    }
                    String name = ((VariableExpression) be.leftExpression).name
                    scanObligations(be.rightExpression, guards, assigns, out)
                    if (!assigned.add(name)) throw new UnsupportedConstructException("re-assignment of '${name}'")
                    assigns.add(new Assign(name, be.rightExpression))
                    continue
                }
                scanObligations(e, guards, assigns, out)
                continue
            }
            // Loops, switch, try/catch, etc. — outside the value-flow fragment.
            throw new UnsupportedConstructException(
                "statement ${st.class.simpleName} outside value-flow fragment")
        }
    }

    /** Collect the implicit obligations syntactically present in {@code e}, each tagged with a snapshot of context. */
    private void scanObligations(Expression e, List<Guard> guards, List<Assign> assigns, List<VfObligation> out) {
        if (e == null) return
        ObligationCollector col = new ObligationCollector()
        try { e.visit(col) } catch (Throwable ignored) { return }
        if (col.indexSites.isEmpty() && col.divideSites.isEmpty() && col.derefSites.isEmpty()) return
        List<Guard> gSnap = new ArrayList<Guard>(guards)
        List<Assign> aSnap = new ArrayList<Assign>(assigns)
        for (IndexSite s : col.indexSites)  out.add(mkVf(s, gSnap, aSnap))
        for (DivideSite s : col.divideSites) out.add(mkVf(s, gSnap, aSnap))
        for (DerefSite s : col.derefSites)  out.add(mkVf(s, gSnap, aSnap))
    }

    private static List<Guard> append(List<Guard> base, Guard g) {
        List<Guard> r = new ArrayList<Guard>(base); r.add(g); return r
    }

    private static VfObligation mkVf(Object site, List<Guard> guards, List<Assign> assigns) {
        VfObligation v = new VfObligation()
        v.site = site; v.guards = guards; v.assigns = assigns
        return v
    }

    /** Discharge a value-flow obligation: assume @Requires, replay the reaching assignments and guards, then check. */
    private void dischargeVfObligation(MethodNode node, VfObligation v, Expression reqAst) {
        SmtSession s = backend.session()
        try {
            Encoder enc = new Encoder(s)
            if (reqAst != null) {
                Object pre = enc.translate(reqAst)
                if (pre != null) s.assertExpr(pre)
            }
            // Single-assignment locals: each name is bound once, before use, so
            // asserting the equalities in any order recovers the reaching store.
            for (Assign a : v.assigns) {
                Object rhs = enc.translate(a.rhs)
                if (rhs != null) s.assertExpr(s.eq(enc.varFor(a.name), rhs))
            }
            for (Guard g : v.guards) {
                Object c = enc.translate(g.cond)
                if (c != null) s.assertExpr(g.positive ? c : s.not(c))
            }
            dischargeObligationUnder(s, enc, v.site)
        } finally {
            try { s.close() } catch (Throwable ignored) {}
        }
    }

    /** Assume the method's own @Requires (if encodable) plus the path facts at a site. */
    private void assumeContext(SmtSession s, Encoder enc, Expression reqAst, ASTNode site, PathFacts pf) {
        if (reqAst != null) {
            Object pre = enc.translate(reqAst)
            if (pre != null) s.assertExpr(pre)
        }
        for (IfFact f : pf.factsAt(site)) {
            Object c = enc.translate(f.condition)
            if (c == null) continue   // an unencodable fact just weakens the assumption set — safe
            s.assertExpr(f.inThenBranch ? c : s.not(c))
        }
    }

    private void dischargeIndex(IndexSite site, PathFacts pf, Expression reqAst) {
        SmtSession s = backend.session()
        try {
            Encoder enc = new Encoder(s)
            assumeContext(s, enc, reqAst, site.node, pf)
            dischargeObligationUnder(s, enc, site)
        } finally {
            try { s.close() } catch (Throwable ignored) {}
        }
    }

    private void dischargeDivide(DivideSite site, PathFacts pf, Expression reqAst) {
        SmtSession s = backend.session()
        try {
            Encoder enc = new Encoder(s)
            assumeContext(s, enc, reqAst, site.node, pf)
            dischargeObligationUnder(s, enc, site)
        } finally {
            try { s.close() } catch (Throwable ignored) {}
        }
    }

    private void dischargeDeref(DerefSite site, PathFacts pf, Expression reqAst) {
        SmtSession s = backend.session()
        try {
            Encoder enc = new Encoder(s)
            assumeContext(s, enc, reqAst, site.node, pf)
            dischargeObligationUnder(s, enc, site)
        } finally {
            try { s.close() } catch (Throwable ignored) {}
        }
    }

    /**
     * Assert the negation of one implicit obligation against an already-seeded
     * session (context assumptions added by the caller) and report if it is not
     * discharged. Shared by the havoc pass and the Phase 5 value-flow pass.
     */
    private void dischargeObligationUnder(SmtSession s, Encoder enc, Object site) {
        if (site instanceof IndexSite) {
            IndexSite ix = (IndexSite) site
            Object idx = enc.translate(ix.index)
            if (idx == null) {
                addStaticTypeError(Reporter.formatImplicitSkipped("array index",
                    "index '${ix.index.text}' is outside fragment"), ix.node)
                return
            }
            Object size = enc.sizeOf(ix.receiver)
            Object inBounds = s.and([s.le(s.intLit(0L), idx), s.lt(idx, size)])
            s.assertExpr(s.not(inBounds))
            CheckResult r = s.check()
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(Reporter.formatIndexBounds(ix.index.text, ix.receiver, r), ix.node)
            }
            return
        }
        if (site instanceof DivideSite) {
            DivideSite dv = (DivideSite) site
            Object divisor = enc.translate(dv.divisor)
            if (divisor == null) {
                addStaticTypeError(Reporter.formatImplicitSkipped("division",
                    "divisor '${dv.divisor.text}' is outside fragment"), dv.node)
                return
            }
            s.assertExpr(s.not(s.ne(divisor, s.intLit(0L))))   // negation of (divisor != 0)
            CheckResult r = s.check()
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(Reporter.formatDivisionByZero(dv.divisor.text, r), dv.node)
            }
            return
        }
        if (site instanceof DerefSite) {
            DerefSite df = (DerefSite) site
            // Obligation: ¬isNull(recv). Assert its negation, isNull(recv), and
            // check: SAT means the receiver can be null on this path.
            s.assertExpr(enc.nullityOf(df.receiver))
            CheckResult r = s.check()
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(Reporter.formatNullDereference(df.receiver, r), df.node)
            }
        }
    }

    /**
     * Phase 5b — discharge a loop method's implicit obligations with the loop's
     * {@code @Invariant} in scope. Prefix sites see {@code @Requires} and the
     * straight-line prefix store; the guard and body sites additionally assume
     * the invariant (and, in the body, the guard); suffix sites assume the
     * invariant and the negated guard. Loop-modified variables are otherwise
     * havoc, so this proves exactly what the user's invariant is strong enough
     * to support — and honestly reports "could not decide" when it is not.
     */
    private void verifyLoopObligations(MethodNode node, LoopSite site) {
        Expression reqAst = findRequires(node) != null ? contractAstFor(node, 'requires') : null
        LoopSpec spec = site.spec
        // 1. Prefix: @Requires + the straight-line prefix store; no invariant yet.
        dischargeRegion(site.prefix, reqAst, Collections.<Expression>emptyList(), null)
        // 2. Guard expression: evaluated whenever the invariant holds.
        for (Object s : sitesInExpression(spec.guard)) {
            dischargeSeeded(s, reqAst, spec.invariants, null, Collections.<Statement>emptyList())
        }
        // 3. Body: invariant ∧ guard, threaded through the (straight-line) body.
        List<Expression> bodyAssumed = new ArrayList<Expression>(spec.invariants)
        bodyAssumed.add(spec.guard)
        dischargeRegion(spec.body, reqAst, bodyAssumed, null)
        // 4. Suffix: invariant ∧ ¬guard (the loop has exited).
        dischargeRegion(site.suffix, reqAst, spec.invariants, spec.guard)
    }

    /** Discharge every obligation in a straight-line region, each under the seed plus the region's preceding statements. */
    private void dischargeRegion(List<Statement> stmts, Expression reqAst,
                                 List<Expression> assumePos, Expression assumeNeg) {
        if (stmts == null) return
        for (int i = 0; i < stmts.size(); i++) {
            List<Object> sites = sitesInStatement(stmts.get(i))
            if (sites.isEmpty()) continue
            List<Statement> preceding = stmts.subList(0, i)
            for (Object site : sites) {
                dischargeSeeded(site, reqAst, assumePos, assumeNeg, preceding)
            }
        }
    }

    /**
     * Fresh session: assume {@code @Requires}, the positive facts and the
     * optional negated fact, then bind-thread the preceding straight-line
     * statements (SSA semantics — correct even when the loop counter is
     * re-assigned), and discharge the obligation.
     */
    private void dischargeSeeded(Object site, Expression reqAst,
                                 List<Expression> assumePos, Expression assumeNeg,
                                 List<Statement> preceding) {
        SmtSession s = backend.session()
        try {
            Encoder enc = new Encoder(s)
            if (reqAst != null) {
                Object p = enc.translate(reqAst)
                if (p != null) s.assertExpr(p)
            }
            if (assumePos != null) {
                for (Expression e : assumePos) {
                    Object h = enc.translate(e)
                    if (h != null) s.assertExpr(h)
                }
            }
            if (assumeNeg != null) {
                Object h = enc.translate(assumeNeg)
                if (h != null) s.assertExpr(s.not(h))
            }
            try {
                LoopEncoder.symExec(preceding, enc, s)
            } catch (UnsupportedConstructException ignored) {
                // Can't model the preceding statements → leave those vars havoc (sound).
            }
            dischargeObligationUnder(s, enc, site)
        } finally {
            try { s.close() } catch (Throwable ignored) {}
        }
    }

    private static List<Object> sitesInStatement(Statement st) {
        ObligationCollector col = new ObligationCollector()
        try { if (st != null) st.visit(col) } catch (Throwable ignored) {}
        return combineSites(col)
    }

    private static List<Object> sitesInExpression(Expression e) {
        ObligationCollector col = new ObligationCollector()
        try { if (e != null) e.visit(col) } catch (Throwable ignored) {}
        return combineSites(col)
    }

    private static List<Object> combineSites(ObligationCollector col) {
        List<Object> r = new ArrayList<Object>()
        r.addAll(col.indexSites); r.addAll(col.divideSites); r.addAll(col.derefSites)
        return r
    }

    @CompileStatic private static class IndexSite  { ASTNode node; String receiver; Expression index }
    @CompileStatic private static class DivideSite { ASTNode node; Expression divisor }
    @CompileStatic private static class DerefSite  { ASTNode node; String receiver }

    /**
     * Walks a method body once, collecting the implicit-precondition sites:
     * array/list subscripts, integer division/modulo, and instance-method
     * dereferences on a named local/parameter receiver. Static calls, {@code this}
     * receivers, and calls on non-variable receivers are skipped — they are either
     * provably non-null or out of the spike's reach.
     */
    @CompileStatic
    private static class ObligationCollector extends ClassCodeVisitorSupport {
        final List<IndexSite> indexSites = []
        final List<DivideSite> divideSites = []
        final List<DerefSite> derefSites = []

        @Override
        protected SourceUnit getSourceUnit() { null }

        @Override
        void visitBinaryExpression(BinaryExpression be) {
            // Match by operator text rather than token id: the parser assigns `%`
            // a token outside the Types.MOD constant, so text is the robust key.
            String sym = be.operation.text
            if (be.operation.type == Types.LEFT_SQUARE_BRACKET &&
                be.leftExpression instanceof VariableExpression) {
                indexSites.add(new IndexSite(node: be,
                    receiver: ((VariableExpression) be.leftExpression).name,
                    index: be.rightExpression))
            } else if (sym == '/' || sym == '%') {
                divideSites.add(new DivideSite(node: be, divisor: be.rightExpression))
            }
            super.visitBinaryExpression(be)
        }

        @Override
        void visitMethodCallExpression(MethodCallExpression mce) {
            Expression recv = mce.objectExpression
            if (!mce.implicitThis && recv instanceof VariableExpression) {
                VariableExpression v = (VariableExpression) recv
                Variable accessed = v.accessedVariable
                // Only real value variables (parameters / locals) — never a class
                // name (static call) or an unresolved dynamic reference.
                boolean realVar = accessed instanceof Parameter || accessed instanceof VariableExpression
                if (realVar && v.name != 'this' && v.name != 'super') {
                    derefSites.add(new DerefSite(node: mce, receiver: v.name))
                }
            }
            super.visitMethodCallExpression(mce)
        }
    }

    /**
     * Discharge a method's own {@code @Ensures} postcondition
     * against its body. Enumerate the body's execution paths and, for
     * each, ask Z3 whether {@code pathFacts ∧ ¬postcondition} is
     * satisfiable — a model is a return on which the postcondition fails.
     */
    private void verifyPostcondition(MethodNode node) {
        AnnotationNode ens = findEnsures(node)
        if (ens == null || node.code == null) return

        Expression postAst = contractAstFor(node, 'ensures')
        if (postAst == null) {
            addStaticTypeError(
                Reporter.formatPostconditionSkipped(node.name,
                    "contract source was not captured by ContractExpansionTransform"),
                node)
            return
        }

        // A method may use its own @Requires as an entry assumption.
        AnnotationNode reqOwn = findRequires(node)
        Expression reqAst = reqOwn != null ? contractAstFor(node, 'requires') : null

        try {
            // Prefer the clean body snapshot taken at CONVERSION; by now
            // groovy-contracts has rewritten node.code in place.
            Statement body = (Statement) node.getNodeMetaData(
                ContractExpansionTransform.ORIGINAL_BODY_KEY)
            if (body == null) body = node.code
            List<Path> paths = BodyEncoder.enumeratePaths(body)
            for (Path p : paths) {
                checkPath(node, p, postAst, reqAst)
            }
        } catch (UnsupportedConstructException e) {
            addStaticTypeError(
                Reporter.formatPostconditionSkipped(node.name, e.message), node)
        }
    }

    private void checkPath(MethodNode node, Path p, Expression postAst, Expression reqAst) {
        SmtSession session = backend.session()
        try {
            Encoder enc = new Encoder(session)

            if (reqAst != null) {
                Object pre = enc.translate(reqAst)
                if (pre == null) {
                    throw new UnsupportedConstructException(
                        "precondition '${reqAst.text}' is outside fragment")
                }
                session.assertExpr(pre)
            }

            for (Object step : p.steps) {
                if (step instanceof Guard) {
                    Guard g = (Guard) step
                    Object c = enc.translate(g.cond)
                    if (c == null) {
                        throw new UnsupportedConstructException(
                            "guard '${g.cond.text}' is outside fragment")
                    }
                    session.assertExpr(g.positive ? c : session.not(c))
                } else if (step instanceof Assign) {
                    Assign a = (Assign) step
                    Object rhs = enc.translate(a.rhs)
                    if (rhs != null) {
                        session.assertExpr(session.eq(enc.varFor(a.name), rhs))
                    } else if (isCallExpr(a.rhs) &&
                               assumeCalleeEnsures(session, enc, a.rhs, node, enc.varFor(a.name))) {
                        // s = f(args): s is constrained by f's @Ensures (result ↦ s,
                        // formals ↦ actuals) — Phase 7 inter-procedural reasoning. The
                        // callee's @Requires is discharged separately at the call site.
                    } else {
                        throw new UnsupportedConstructException(
                            "assignment '${a.name} = ${a.rhs.text}' is outside fragment")
                    }
                } else if (step instanceof ArrayStore) {
                    ArrayStore st = (ArrayStore) step
                    Object idx = enc.translate(st.index)
                    Object val = enc.translate(st.value)
                    if (idx == null || val == null) {
                        throw new UnsupportedConstructException(
                            "array store '${st.arr}[${st.index.text}] = ${st.value.text}' is outside fragment")
                    }
                    // a := (store a idx val): subsequent reads of a see the update.
                    enc.bindArray(st.arr, session.store(enc.arrayFor(st.arr), idx, val))
                }
            }

            Object resHandle = enc.translate(p.result)
            if (resHandle == null) {
                throw new UnsupportedConstructException(
                    "return expression '${p.result?.text}' is outside fragment")
            }
            enc.bind('result', resHandle)

            Object post = enc.translate(postAst)
            if (post == null) {
                throw new UnsupportedConstructException(
                    "postcondition '${postAst.text}' is outside fragment")
            }
            session.assertExpr(session.not(post))

            CheckResult r = session.check()
            if (r.status == CheckResult.Status.VERIFIED) return

            ASTNode anchor = (p.result != null && p.result.lineNumber > 0) ?
                (ASTNode) p.result : (ASTNode) node
            addStaticTypeError(
                Reporter.formatPostconditionFailure(node.name, postAst.text, r), anchor)
        } finally {
            try { session.close() } catch (Throwable ignored) {}
        }
    }

    private static AnnotationNode findEnsures(MethodNode m) {
        List<AnnotationNode> direct = m.getAnnotations(ENSURES_TYPE)
        return (direct != null && !direct.isEmpty()) ? direct[0] : null
    }

    // ---- Loops (@Invariant / @Decreases) ----

    /** A body shaped as: straight-line prefix; one annotated loop; straight-line suffix. */
    @CompileStatic
    private static class LoopSite {
        Statement loopStmt
        LoopSpec spec
        List<Statement> prefix
        List<Statement> suffix
    }

    /**
     * Locate the single top-level annotated loop, returning its {@link LoopSpec}
     * plus the straight-line prefix/suffix around it, or null if there is none.
     * Raises {@link UnsupportedConstructException} (→ "skipped") if the body has
     * more than one — the spike models a single loop.
     */
    private static LoopSite findLoopSite(Statement body) {
        List<Statement> top = topStatements(body)
        int idx = -1
        for (int i = 0; i < top.size(); i++) {
            if (top.get(i).getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY) != null) {
                if (idx != -1) {
                    throw new UnsupportedConstructException(
                        "more than one annotated loop in the method body")
                }
                idx = i
            }
        }
        if (idx == -1) return null
        LoopSite site = new LoopSite()
        site.loopStmt = top.get(idx)
        site.spec = (LoopSpec) site.loopStmt.getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY)
        site.prefix = new ArrayList<Statement>(top.subList(0, idx))
        site.suffix = new ArrayList<Statement>(top.subList(idx + 1, top.size()))
        return site
    }

    private static List<Statement> topStatements(Statement body) {
        if (body instanceof BlockStatement) {
            return new ArrayList<Statement>(((BlockStatement) body).statements)
        }
        return body != null ? ([body] as List<Statement>) : Collections.<Statement> emptyList()
    }

    /**
     * Discharge the inductive proof for an annotated loop: establishment,
     * preservation, optional progress (@Decreases), and — when the method has an
     * {@code @Ensures} — the use obligation that the post-loop state proves the
     * postcondition. Each is an independent solver context with a fresh
     * {@link Encoder}, so any variable a context does not bind is a fresh
     * unconstrained value: that is exactly "havoc the loop-modified variables".
     */
    private void verifyLoop(MethodNode node, LoopSite site) {
        Expression reqAst = findRequires(node) != null ? contractAstFor(node, 'requires') : null
        Expression postAst = findEnsures(node) != null ? contractAstFor(node, 'ensures') : null
        try {
            checkEstablishment(node, site, reqAst)
            checkPreservation(node, site)
            if (site.spec.variant != null) checkProgress(node, site)
            if (postAst != null) checkUse(node, site, reqAst, postAst)
        } catch (UnsupportedConstructException e) {
            addStaticTypeError(Reporter.formatLoopSkipped(node.name, e.message), site.loopStmt)
        }
    }

    /** Establishment: precondition ∧ prefix ⇒ invariant. */
    private void checkEstablishment(MethodNode node, LoopSite site, Expression reqAst) {
        SmtSession s = backend.session()
        try {
            Encoder enc = new Encoder(s)
            if (reqAst != null) s.assertExpr(LoopEncoder.tr(enc, reqAst, "precondition"))
            LoopEncoder.symExec(site.prefix, enc, s)
            s.assertExpr(s.not(LoopEncoder.conj(enc, s, site.spec.invariants)))
            CheckResult r = s.check()
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(
                    Reporter.formatLoopEstablishment(node.name, invText(site), r), site.loopStmt)
            }
        } finally { try { s.close() } catch (Throwable ignored) {} }
    }

    /** Preservation: invariant ∧ guard ∧ one body iteration ⇒ invariant still holds. */
    private void checkPreservation(MethodNode node, LoopSite site) {
        SmtSession s = backend.session()
        try {
            Encoder enc = new Encoder(s)
            s.assertExpr(LoopEncoder.conj(enc, s, site.spec.invariants))
            s.assertExpr(LoopEncoder.tr(enc, site.spec.guard, "guard"))
            LoopEncoder.symExec(site.spec.body, enc, s)
            // Re-translating the invariant reads the post-body bindings → inv'.
            s.assertExpr(s.not(LoopEncoder.conj(enc, s, site.spec.invariants)))
            CheckResult r = s.check()
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(
                    Reporter.formatLoopPreservation(node.name, invText(site), r), site.loopStmt)
            }
        } finally { try { s.close() } catch (Throwable ignored) {} }
    }

    /** Progress: invariant ∧ guard ⇒ the variant strictly decreases and stays ≥ 0. */
    private void checkProgress(MethodNode node, LoopSite site) {
        SmtSession s = backend.session()
        try {
            Encoder enc = new Encoder(s)
            s.assertExpr(LoopEncoder.conj(enc, s, site.spec.invariants))
            s.assertExpr(LoopEncoder.tr(enc, site.spec.guard, "guard"))
            Object oldV = LoopEncoder.tr(enc, site.spec.variant, "variant")
            LoopEncoder.symExec(site.spec.body, enc, s)
            Object newV = LoopEncoder.tr(enc, site.spec.variant, "variant")
            s.assertExpr(s.not(s.and([s.lt(newV, oldV), s.ge(newV, s.intLit(0L))])))
            CheckResult r = s.check()
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(
                    Reporter.formatLoopProgress(node.name, site.spec.variant.text, r), site.loopStmt)
            }
        } finally { try { s.close() } catch (Throwable ignored) {} }
    }

    /** Use: precondition ∧ invariant ∧ ¬guard ∧ suffix ⇒ postcondition. */
    private void checkUse(MethodNode node, LoopSite site, Expression reqAst, Expression postAst) {
        SmtSession s = backend.session()
        try {
            Encoder enc = new Encoder(s)
            if (reqAst != null) s.assertExpr(LoopEncoder.tr(enc, reqAst, "precondition"))
            s.assertExpr(LoopEncoder.conj(enc, s, site.spec.invariants))
            s.assertExpr(s.not(LoopEncoder.tr(enc, site.spec.guard, "guard")))
            Expression resultExpr = LoopEncoder.resultExpr(site.suffix, enc, s)
            enc.bind('result', LoopEncoder.tr(enc, resultExpr, "return expression"))
            s.assertExpr(s.not(LoopEncoder.tr(enc, postAst, "postcondition")))
            CheckResult r = s.check()
            if (r.status != CheckResult.Status.VERIFIED) {
                ASTNode anchor = (resultExpr != null && resultExpr.lineNumber > 0) ?
                    (ASTNode) resultExpr : (ASTNode) site.loopStmt
                addStaticTypeError(
                    Reporter.formatPostconditionFailure(node.name, postAst.text, r), anchor)
            }
        } finally { try { s.close() } catch (Throwable ignored) {} }
    }

    private static String invText(LoopSite site) {
        site.spec.invariants.collect { it.text }.join(' && ')
    }

    @Override
    void onMethodSelection(Expression expression, MethodNode target) {
        // We only care about resolvable, method-call-shaped expressions.
        if (!(expression instanceof MethodCall)) return
        if (target == null) return

        // Find @Requires on the callee. Walk superclasses too — a child
        // can inherit a contract via overriding.
        AnnotationNode req = findRequires(target)
        if (req == null) return

        Expression contractAst = contractAstFor(target, 'requires')
        if (contractAst == null) {
            addStaticTypeError(
                Reporter.formatSkipped(target.name,
                    "contract source was not captured by ContractExpansionTransform " +
                    "(producer may not have been recompiled with :verification on its classpath)"),
                expression as ASTNode)
            return
        }

        List<Expression> argExprs = collectArgumentExpressions((MethodCall) expression)
        if (argExprs == null) {
            addStaticTypeError(
                Reporter.formatSkipped(target.name,
                    "could not extract argument expressions at call site"),
                expression as ASTNode)
            return
        }

        Parameter[] formals = target.parameters
        if (formals.length != argExprs.size()) {
            // Varargs and default params: out of scope for the spike.
            addStaticTypeError(
                Reporter.formatSkipped(target.name,
                    "formal/actual arity mismatch (varargs not supported yet)"),
                expression as ASTNode)
            return
        }

        verifyCallSite(target, formals, argExprs, contractAst, expression)
    }

    private void verifyCallSite(MethodNode target,
                                Parameter[] formals,
                                List<Expression> argExprs,
                                Expression contractAst,
                                Expression callExpr) {

        SmtSession session = backend.session()
        try {
            Encoder enc = new Encoder(session)

            // 1. Translate each actual-argument expression into an SMT
            //    handle, sharing the encoder's env so a free variable
            //    referenced by the argument is the same SMT var as one
            //    referenced by the path condition.
            Map<String, Object> formalBindings = [:]
            // Reference-typed formals bound to a named actual: candidates for
            // tying the size/nullity oracles across the boundary (see below).
            Map<String, String> oracleActuals = [:]
            for (int i = 0; i < formals.length; i++) {
                Object argHandle = enc.translate(argExprs[i])
                if (argHandle == null) {
                    addStaticTypeError(
                        Reporter.formatSkipped(target.name,
                            "actual argument '${argExprs[i].text}' is outside fragment"),
                        callExpr as ASTNode)
                    return
                }
                // Bind the formal to a named SMT variable pinned to the
                // actual argument, rather than to the argument handle
                // directly. This guarantees the parameter shows up in
                // any counterexample model (Dafny-style "x = -1"), even
                // when the actual argument is a bare literal.
                Object formalVar = session.intVar(formals[i].name)
                session.assertExpr(session.eq(formalVar, argHandle))
                formalBindings[formals[i].name] = formalVar

                // Record reference-typed formals bound to a named actual. The
                // size/nullity oracles are tied *after* the contract is
                // translated (below), so we tie only the oracles the contract
                // actually uses — minting an unused `n.size` would pollute the
                // counterexample. Primitives have no size/nullity to tie.
                if (argExprs[i] instanceof VariableExpression &&
                    !ClassHelper.isPrimitiveType(formals[i].type)) {
                    oracleActuals[formals[i].name] = ((VariableExpression) argExprs[i]).name
                }
            }

            // 1b. Assume the *enclosing* method's own @Requires, if any. A
            //     precondition is a given throughout the method body, so it may
            //     be used to discharge a call the body makes — exactly as the
            //     implicit-obligation checks already do (see assumeContext).
            //     The enclosing parameter names coincide with the actual-
            //     argument names in scope here, so the same SMT symbols (and
            //     their size/nullity oracles) are shared automatically.
            if (currentMethod != null && findRequires(currentMethod) != null) {
                Expression enclosingReq = contractAstFor(currentMethod, 'requires')
                if (enclosingReq != null) {
                    Object pre = enc.translate(enclosingReq)
                    if (pre != null) session.assertExpr(pre)
                }
            }

            // 2. Harvest path facts and assert them. Each fact is one
            //    enclosing if's condition (negated if we're in the
            //    else branch).
            List<IfFact> facts = currentFacts != null ?
                currentFacts.factsAt(callExpr as ASTNode) :
                Collections.<IfFact>emptyList()
            for (IfFact f : facts) {
                Object condExpr = enc.translate(f.condition)
                if (condExpr == null) {
                    // A fact we can't encode just becomes an unknown
                    // — drop it. Safe (it weakens our assumption set),
                    // and the spike stays honest.
                    continue
                }
                session.assertExpr(f.inThenBranch ? condExpr : session.not(condExpr))
            }

            // 3. Translate the contract and assert its NEGATION. We're
            //    asking: is there a model where the path is satisfiable
            //    AND the precondition fails? If yes, that model is the
            //    counterexample we report.
            formalBindings.each { name, handle -> enc.bind(name, handle) }
            Object contractSmt = enc.translate(contractAst)
            if (contractSmt == null) {
                addStaticTypeError(
                    Reporter.formatSkipped(target.name,
                        "precondition contract is outside fragment"),
                    callExpr as ASTNode)
                return
            }
            // 3b. Tie the formal's size/nullity oracle to the actual's — but
            //     only for oracles the contract (or assumed context) actually
            //     minted on the formal. This carries a caller's knowledge
            //     (`xs.size() > 0`, `x != null`) across the boundary while
            //     keeping unused oracles out of the counterexample.
            oracleActuals.each { String formalName, String actualName ->
                if (enc.hasSizeOracle(formalName)) {
                    session.assertExpr(session.eq(
                        enc.sizeOf(formalName), enc.sizeOf(actualName)))
                }
                if (enc.hasNullityOracle(formalName)) {
                    session.assertExpr(session.eq(
                        enc.nullityOf(formalName), enc.nullityOf(actualName)))
                }
            }

            session.assertExpr(session.not(contractSmt))

            // 4. Check.
            CheckResult r = session.check()
            switch (r.status) {
                case CheckResult.Status.VERIFIED:
                    return  // silent success
                case CheckResult.Status.REFUTED:
                    addStaticTypeError(
                        Reporter.formatPreconditionFailure(
                            target.name, contractAst.text, r),
                        callExpr as ASTNode)
                    return
                case CheckResult.Status.UNKNOWN:
                    addStaticTypeError(
                        Reporter.formatPreconditionFailure(
                            target.name, contractAst.text, r),
                        callExpr as ASTNode)
                    return
            }
        } finally {
            try { session.close() } catch (Throwable ignored) {}
        }
    }

    private static boolean isCallExpr(Expression e) {
        e instanceof MethodCallExpression || e instanceof StaticMethodCallExpression
    }

    /**
     * Resolve a same-class method call by name + arity to a {@link MethodNode}
     * that carries an {@code @Ensures}. Self-calls are excluded — assuming a
     * method's own postcondition at a recursive call is the inductive hypothesis,
     * which needs {@code @Decreases} for well-foundedness and is a later slice.
     */
    private static MethodNode resolveContractedCallee(MethodNode caller, String name, int arity) {
        ClassNode dc = caller?.declaringClass
        if (dc == null || name == null) return null
        for (MethodNode m : dc.getMethods(name)) {
            if (m == caller) continue
            if (m.parameters.length != arity) continue
            if (findEnsures(m) == null) continue
            return m
        }
        null
    }

    /**
     * Assume the {@code @Ensures} of the method {@code callExpr} resolves to,
     * substituting its formals with the actual-argument handles and {@code result}
     * with {@code resultHandle} (null for a call whose value is unused). Returns
     * true iff a contract was found, fully substitutable, and asserted — so the
     * caller can fall back to "skipped" when it was not.
     */
    private boolean assumeCalleeEnsures(SmtSession s, Encoder enc, Expression callExpr,
                                        MethodNode caller, Object resultHandle) {
        if (!(callExpr instanceof MethodCall)) return false
        String name = ((MethodCall) callExpr).methodAsString
        List<Expression> actuals = collectArgumentExpressions((MethodCall) callExpr)
        if (name == null || actuals == null) return false
        MethodNode callee = resolveContractedCallee(caller, name, actuals.size())
        if (callee == null) return false
        Expression ensuresAst = contractAstFor(callee, 'ensures')
        if (ensuresAst == null) return false

        Parameter[] formals = callee.parameters
        Map<String, Object> bindings = new LinkedHashMap<String, Object>()
        for (int i = 0; i < formals.length; i++) {
            Object h = enc.translate(actuals.get(i))
            if (h == null) return false   // can't faithfully substitute → don't assume
            bindings.put(formals[i].name, h)
        }
        if (resultHandle != null) bindings.put('result', resultHandle)

        Object post = enc.translateWith(ensuresAst, bindings)
        if (post == null) return false    // @Ensures outside the fragment → honest skip
        s.assertExpr(post)
        return true
    }

    /** Find a @Requires on the method, walking declared and inherited methods. */
    private static AnnotationNode findRequires(MethodNode m) {
        List<AnnotationNode> direct = m.getAnnotations(REQUIRES_TYPE)
        if (direct != null && !direct.isEmpty()) return direct[0]
        // Inheritance: simplistic, just walk superclass.
        ClassNode dc = m.declaringClass
        ClassNode sc = dc?.superClass
        if (sc != null && sc != ClassHelper.OBJECT_TYPE) {
            MethodNode inherited = sc.getMethod(m.name, m.parameters)
            if (inherited != null) return findRequires(inherited)
        }
        null
    }

    /**
     * Resolve the contract expression of the given kind ("requires" or
     * "ensures") for a method. The verbatim source text lives on the
     * {@link ContractSource} that {@link ContractExpansionTransform}
     * attaches at producer-compile-time — a RUNTIME annotation, so it is
     * present even when {@code m} comes from a decompiled, already-compiled
     * {@link ClassNode} at a downstream call site. The text is re-parsed
     * back into an {@link Expression} for the encoder.
     */
    private static Expression contractAstFor(MethodNode m, String kind) {
        String text = findContractText(m, kind)
        return text != null ? parseContract(text) : null
    }

    /** Read @ContractSource's member, walking the superclass for inherited contracts. */
    private static String findContractText(MethodNode m, String kind) {
        List<AnnotationNode> sources = m.getAnnotations(CONTRACT_SOURCE_TYPE)
        if (sources != null && !sources.isEmpty()) {
            Expression member = sources[0].getMember(kind)
            if (member instanceof ConstantExpression) {
                Object v = ((ConstantExpression) member).value
                if (v instanceof String && !((String) v).isEmpty()) return (String) v
            }
        }
        ClassNode dc = m.declaringClass
        ClassNode sc = dc?.superClass
        if (sc != null && sc != ClassHelper.OBJECT_TYPE) {
            MethodNode inherited = sc.getMethod(m.name, m.parameters)
            if (inherited != null) return findContractText(inherited, kind)
        }
        return null
    }

    private static Expression parseContract(String contractText) {
        try {
            List<ASTNode> parsed = new AstBuilder().buildFromString(
                CompilePhase.CONVERSION, true, contractText)
            // AstBuilder wraps in BlockStatement → ExpressionStatement → Expression
            if (parsed.isEmpty()) return null
            ASTNode top = parsed[0]
            if (top instanceof BlockStatement) {
                BlockStatement bs = (BlockStatement) top
                if (bs.statements.size() == 1 &&
                    bs.statements[0] instanceof ExpressionStatement) {
                    return ((ExpressionStatement) bs.statements[0]).expression
                }
            }
            return null
        } catch (Throwable t) {
            return null
        }
    }

    /** Argument expressions in the order they appear at the call site. */
    private static List<Expression> collectArgumentExpressions(MethodCall mc) {
        Expression args = mc.arguments
        if (args == null) return Collections.<Expression>emptyList()
        // arguments is typically an ArgumentListExpression
        if (args.metaClass.respondsTo(args, 'getExpressions')) {
            try {
                List<Expression> es = (List<Expression>) args.invokeMethod('getExpressions', null)
                return es != null ? es : Collections.<Expression>emptyList()
            } catch (Throwable ignored) {}
        }
        Collections.<Expression>emptyList()
    }
}
