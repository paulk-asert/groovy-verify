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
import org.codehaus.groovy.ast.expr.BooleanExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.NotExpression
import org.codehaus.groovy.ast.expr.UnaryMinusExpression
import org.codehaus.groovy.ast.expr.UnaryPlusExpression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.syntax.Types

/**
 * Translates the supported fragment of Groovy expressions into SMT
 * via {@link SmtSession}. Returns {@code null} for anything outside
 * the fragment — the caller treats that as "skipped: outside
 * fragment" and emits a warning rather than passing silently.
 *
 * Supported:
 *   - integer literals
 *   - variable references (declared on demand as integer constants)
 *   - unary +/-
 *   - binary +, -, * (multiplication only if at least one side is
 *     a literal; pure NIA is a documented non-goal of v1)
 *   - comparisons ==, !=, <, <=, >, >=
 *   - boolean &&, ||, !
 *
 * Not supported (yet, deliberately):
 *   - division / modulo (will need DBZ side conditions)
 *   - bitwise ops, shifts
 *   - quantifiers
 *   - method calls (including .size() on collections — easy next step)
 *   - array indexing
 */
@CompileStatic
class Encoder {

    final SmtSession session
    /** Variable name in source scope -> SMT handle. */
    private final Map<String, Object> env = [:]

    Encoder(SmtSession session) {
        this.session = session
    }

    /**
     * Get-or-declare an integer SMT variable for a source-level name.
     * Idempotent — the same name returns the same handle, so a
     * variable referenced in both the path condition and the
     * precondition refers to the same SMT constant.
     */
    Object varFor(String name) {
        Object cached = env.get(name)
        if (cached != null) return cached
        Object v = session.intVar(name)
        env.put(name, v)
        v
    }

    /** Explicit binding, used to wire formal parameters to actual-argument expressions. */
    void bind(String name, Object handle) {
        env.put(name, handle)
    }

    /**
     * Translate a Groovy expression to an SMT handle. Returns null
     * if anything in the subtree is outside the fragment.
     */
    Object translate(Expression expr) {
        if (expr == null) return null

        if (expr instanceof ConstantExpression) {
            Object v = ((ConstantExpression) expr).value
            if (v instanceof Integer || v instanceof Long || v instanceof Short || v instanceof Byte) {
                return session.intLit(((Number) v).longValue())
            }
            if (v instanceof Boolean) {
                return session.boolLit((Boolean) v)
            }
            return null  // strings, floats, etc — outside fragment
        }

        if (expr instanceof VariableExpression) {
            String name = ((VariableExpression) expr).name
            // Boolean literal as variable name shouldn't really happen at this
            // point post-parse, but defensive:
            if (name == "true")  return session.boolLit(true)
            if (name == "false") return session.boolLit(false)
            return varFor(name)
        }

        if (expr instanceof UnaryMinusExpression) {
            Object inner = translate(((UnaryMinusExpression) expr).expression)
            return inner == null ? null : session.neg(inner)
        }

        if (expr instanceof UnaryPlusExpression) {
            return translate(((UnaryPlusExpression) expr).expression)
        }

        if (expr instanceof NotExpression) {
            Object inner = translate(((NotExpression) expr).expression)
            return inner == null ? null : session.not(inner)
        }

        if (expr instanceof BooleanExpression) {
            // Groovy wraps if/while conditions in BooleanExpression
            return translate(((BooleanExpression) expr).expression)
        }

        if (expr instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) expr
            Object L = translate(be.leftExpression)
            Object R = translate(be.rightExpression)
            if (L == null || R == null) return null
            int op = be.operation.type
            switch (op) {
                case Types.PLUS:                return session.plus(L, R)
                case Types.MINUS:               return session.minus(L, R)
                case Types.MULTIPLY:
                    // Pure-NIA opt-out: refuse if BOTH sides are non-literal,
                    // so the encoder stays in QF_LIA for the spike.
                    if (!(be.leftExpression instanceof ConstantExpression) &&
                        !(be.rightExpression instanceof ConstantExpression)) {
                        return null
                    }
                    return session.times(L, R)
                case Types.COMPARE_EQUAL:       return session.eq(L, R)
                case Types.COMPARE_NOT_EQUAL:   return session.ne(L, R)
                case Types.COMPARE_LESS_THAN:           return session.lt(L, R)
                case Types.COMPARE_LESS_THAN_EQUAL:     return session.le(L, R)
                case Types.COMPARE_GREATER_THAN:        return session.gt(L, R)
                case Types.COMPARE_GREATER_THAN_EQUAL:  return session.ge(L, R)
                case Types.LOGICAL_AND:         return session.and([L, R])
                case Types.LOGICAL_OR:          return session.or([L, R])
                default:                        return null
            }
        }

        // Anything else: outside fragment.
        return null
    }

}
