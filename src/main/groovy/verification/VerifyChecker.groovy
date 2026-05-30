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
import org.codehaus.groovy.ast.AnnotationNode
import org.codehaus.groovy.ast.ASTNode
import org.codehaus.groovy.ast.ClassHelper
import org.codehaus.groovy.ast.ClassNode
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.Parameter
import org.codehaus.groovy.ast.builder.AstBuilder
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.MethodCall
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.control.CompilePhase
import org.codehaus.groovy.transform.stc.StaticTypeCheckingVisitor
import org.codehaus.groovy.transform.stc.TypeCheckingExtension

/**
 * SMT-backed precondition verifier — the spike entry point.
 *
 * Usage from consumer code:
 *   {@code @TypeChecked(extensions = 'verification.VerifyChecker')}
 *
 * What this does on every method call inside the annotated scope:
 *   1. Look up the called method's {@code @Requires} contract.
 *   2. Bind the contract's formal parameters to the actual-argument
 *      expressions at this call site.
 *   3. Harvest the path condition from enclosing {@code if}
 *      statements (precomputed by {@link PathFacts}).
 *   4. Ask Z3 whether {@code path ∧ ¬precond} is satisfiable.
 *        - UNSAT  → verified, no diagnostic.
 *        - SAT    → refuted, emit error with counterexample.
 *        - UNKNOWN → emit warning ("could not decide").
 *
 * Anything outside the supported fragment becomes a "skipped"
 * warning rather than a silent pass — borrowed from OpenJML's ESC
 * mode discipline.
 */
@CompileStatic
class VerifyChecker extends TypeCheckingExtension {

    private static final ClassNode REQUIRES_TYPE = ClassHelper.make(Requires)
    private static final ClassNode ENSURES_TYPE = ClassHelper.make(Ensures)

    private SmtBackend backend
    private PathFacts currentFacts

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
            verifyPostcondition(node)
        } finally {
            currentFacts = null
        }
    }

    /**
     * Phase 2: discharge a method's own {@code @Ensures} postcondition
     * against its body. Enumerate the body's execution paths and, for
     * each, ask Z3 whether {@code pathFacts ∧ ¬postcondition} is
     * satisfiable — a model is a return on which the postcondition fails.
     */
    private void verifyPostcondition(MethodNode node) {
        AnnotationNode ens = findEnsures(node)
        if (ens == null || node.code == null) return

        Expression postAst = extractContractAst(ens)
        if (postAst == null) {
            addStaticTypeError(
                Reporter.formatPostconditionSkipped(node.name,
                    "contract was not captured by EnsuresTransformation"),
                node)
            return
        }

        // A method may use its own @Requires as an entry assumption.
        AnnotationNode reqOwn = findRequires(node)
        Expression reqAst = reqOwn != null ? extractContractAst(reqOwn) : null

        try {
            List<Path> paths = BodyEncoder.enumeratePaths(node.code)
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
                    if (rhs == null) {
                        throw new UnsupportedConstructException(
                            "assignment '${a.name} = ${a.rhs.text}' is outside fragment")
                    }
                    session.assertExpr(session.eq(enc.varFor(a.name), rhs))
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

    @Override
    void onMethodSelection(Expression expression, MethodNode target) {
        // We only care about resolvable, method-call-shaped expressions.
        if (!(expression instanceof MethodCall)) return
        if (target == null) return

        // Find @Requires on the callee. Walk superclasses too — a child
        // can inherit a contract via overriding.
        AnnotationNode req = findRequires(target)
        if (req == null) return

        Expression contractAst = extractContractAst(req)
        if (contractAst == null) {
            addStaticTypeError(
                Reporter.formatSkipped(target.name,
                    "contract was not captured by RequiresTransformation " +
                    "(producer may not have been recompiled with the transformation on its classpath)"),
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
     * Read the {@code contract} string member set by
     * {@link RequiresTransformation} and parse it back to a Groovy
     * expression AST. The annotation's {@code value} member by this
     * point is a synthetic class reference, not a closure — but the
     * transformation captured the body's source text into
     * {@code contract} at producer-compile-time so we have something
     * re-parseable here.
     */
    private static Expression extractContractAst(AnnotationNode anno) {
        Expression contractMember = anno.getMember('contract')
        if (!(contractMember instanceof ConstantExpression)) return null
        Object v = ((ConstantExpression) contractMember).value
        if (!(v instanceof String) || ((String) v).isEmpty()) return null
        String contractText = (String) v
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
