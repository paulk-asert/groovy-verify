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
import org.codehaus.groovy.ast.expr.BinaryExpression
import org.codehaus.groovy.ast.expr.DeclarationExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
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
        for (Statement st : stmts) {
            if (st instanceof BlockStatement) {
                symExec(((BlockStatement) st).statements, enc, s)
            } else if (st instanceof ExpressionStatement) {
                applyAssign((ExpressionStatement) st, enc, s)
            } else {
                throw new UnsupportedConstructException(
                    "unsupported statement ${st.class.simpleName} in loop region (line ${st.lineNumber})")
            }
        }
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
        (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.ASSIGN)
    }

    private static void applyAssign(ExpressionStatement st, Encoder enc, SmtSession s) {
        Expression e = st.expression
        if (e instanceof DeclarationExpression) {
            DeclarationExpression de = (DeclarationExpression) e
            if (!(de.leftExpression instanceof VariableExpression)) {
                throw new UnsupportedConstructException(
                    "multi-variable declaration unsupported (line ${st.lineNumber})")
            }
            String name = ((VariableExpression) de.leftExpression).name
            enc.bind(name, tr(enc, de.rightExpression, "initialiser of '${name}'"))
            return
        }
        if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.ASSIGN) {
            BinaryExpression be = (BinaryExpression) e
            if (!(be.leftExpression instanceof VariableExpression)) {
                throw new UnsupportedConstructException(
                    "assignment to a non-variable target (line ${st.lineNumber})")
            }
            String name = ((VariableExpression) be.leftExpression).name
            // Translate the RHS under the *current* store, then re-bind — this is
            // the SSA step: subsequent reads of `name` see the new handle.
            enc.bind(name, tr(enc, be.rightExpression, "assignment to '${name}'"))
            return
        }
        throw new UnsupportedConstructException(
            "unsupported statement in loop region (line ${st.lineNumber})")
    }
}
