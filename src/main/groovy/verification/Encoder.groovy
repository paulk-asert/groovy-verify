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
import org.codehaus.groovy.ast.Parameter
import org.codehaus.groovy.ast.expr.ArgumentListExpression
import org.codehaus.groovy.ast.expr.BinaryExpression
import org.codehaus.groovy.ast.expr.BooleanExpression
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.NotExpression
import org.codehaus.groovy.ast.expr.PropertyExpression
import org.codehaus.groovy.ast.expr.TupleExpression
import org.codehaus.groovy.ast.expr.UnaryMinusExpression
import org.codehaus.groovy.ast.expr.UnaryPlusExpression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.ReturnStatement
import org.codehaus.groovy.ast.stmt.Statement
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
 *   - collection/array size: {@code xs.size()}, {@code xs.length},
 *     {@code xs.isEmpty()} via a {@link #sizeOf size oracle} (an integer
 *     constant {@code <name>.size >= 0} shared with the array-bounds checks)
 *   - nullity: {@code x == null} / {@code x != null} via a {@link #nullityOf
 *     nullity oracle} (a boolean "is null" flag per reference)
 *   - {@code x.equals(y)} as a synonym for {@code x == y}
 *   - {@code xs.contains(y)} as an uninterpreted predicate (sound, but with
 *     no membership reasoning until Phase 5's quantifiers)
 *
 * Not supported (yet, deliberately):
 *   - the *value* of an indexed access {@code arr[i]} or a quotient
 *     {@code a / b} (only their safety side-conditions are checked, in
 *     {@link VerifyChecker}); array contents are not modelled
 *   - bitwise ops, shifts
 *   - quantifiers
 */
@CompileStatic
class Encoder {

    final SmtSession session
    /** Variable name in source scope -> SMT handle. */
    private final Map<String, Object> env = [:]
    /** Cache of size-oracle constants, keyed by their SMT name. */
    private final Map<String, Object> sizeEnv = [:]
    /** Cache of nullity-oracle booleans, keyed by reference name. */
    private final Map<String, Object> nullEnv = [:]
    /** Cache of array-content handles ({@code Array Int -> Int}), keyed by source name. */
    private final Map<String, Object> arrEnv = [:]
    /**
     * While translating a quantifier body, the {@code (select arr i)} terms are
     * collected here to serve as the quantifier's instantiation triggers; null
     * outside a quantifier.
     */
    private List<Object> triggerSink = null
    /** Counter for minting unique bound-variable names across nested/multiple quantifiers. */
    private int quantCounter = 0

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
     * Translate {@code expr} with {@code bindings} (source-name → handle) applied
     * over the current environment, then restore it. Used to assume a callee's
     * {@code @Ensures} in the caller's context — its formal parameters substituted
     * by the actual-argument handles, and {@code result} by the call's result
     * (Phase 7 inter-procedural reasoning).
     */
    Object translateWith(Expression expr, Map<String, Object> bindings) {
        Map<String, Object> prev = new LinkedHashMap<String, Object>()
        List<String> added = new ArrayList<String>()
        for (Map.Entry<String, Object> e : bindings.entrySet()) {
            if (env.containsKey(e.key)) prev.put(e.key, env.get(e.key)) else added.add(e.key)
            env.put(e.key, e.value)
        }
        try {
            return translate(expr)
        } finally {
            for (String k : added) env.remove(k)
            for (Map.Entry<String, Object> e : prev.entrySet()) env.put(e.key, e.value)
        }
    }

    /**
     * Re-bind {@code name} to a fresh, unconstrained integer — "havoc". Used by
     * symbolic execution when an assignment's right-hand side is outside the
     * fragment (e.g. {@code s = s + a[i]}): the variable's value becomes unknown
     * rather than aborting the whole analysis. Sound for the verification
     * conditions, which only ever get harder under havoc.
     */
    Object havoc(String name) {
        Object v = session.intVar(name + '$havoc$' + (havocCounter++))
        env.put(name, v)
        v
    }

    /** Array analogue of {@link #havoc}: re-bind {@code name}'s contents to a fresh, unconstrained array. */
    Object havocArray(String name) {
        Object v = session.arrayVar(name + '$havoc$' + (havocCounter++))
        arrEnv.put(name, v)
        v
    }
    private int havocCounter = 0

    /**
     * The size oracle: an integer constant {@code <recv>.size}, constrained
     * {@code >= 0} on first mint, modelling the length of an array/list/string
     * named {@code recv}. The same constant backs {@code recv.length},
     * {@code recv.size()}, {@code recv.isEmpty()} in contracts AND the
     * array-bounds obligation {@code i < recv.size} in {@link VerifyChecker},
     * so a contract that bounds the size and an indexing check agree.
     */
    Object sizeOf(String recv) {
        String key = recv + '.size'
        Object cached = sizeEnv.get(key)
        if (cached != null) return cached
        Object v = session.intVar(key)
        session.assertExpr(session.ge(v, session.intLit(0L)))  // a size is never negative
        sizeEnv.put(key, v)
        v
    }

    /** True if a size oracle has already been minted for {@code recv} (i.e. a contract referenced its size). */
    boolean hasSizeOracle(String recv) { sizeEnv.containsKey(recv + '.size') }

    /** True if a nullity oracle has already been minted for {@code recv}. */
    boolean hasNullityOracle(String recv) { nullEnv.containsKey(recv) }

    /**
     * Get-or-declare the array-content handle for a source-level name. Shares its
     * key with nothing else — the size oracle ({@link #sizeOf}) bounds the valid
     * index range, this models the element values.
     */
    Object arrayFor(String name) {
        Object cached = arrEnv.get(name)
        if (cached != null) return cached
        Object v = session.arrayVar(name)
        arrEnv.put(name, v)
        v
    }

    /**
     * Re-bind an array name to a new content handle — used to thread an array
     * update {@code a[i] = v} as {@code a := (store a i v)}, so a later read of
     * {@code a[i]} sees the post-update contents (value semantics, no aliasing).
     */
    void bindArray(String name, Object handle) {
        arrEnv.put(name, handle)
    }

    /** The nullity oracle: a boolean that is true exactly when {@code recv} is null. */
    Object nullityOf(String recv) {
        Object cached = nullEnv.get(recv)
        if (cached != null) return cached
        Object v = session.boolVar(recv + '?null')
        nullEnv.put(recv, v)
        v
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
            return null  // strings, floats, null — outside fragment (null handled at comparison level)
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

        if (expr instanceof PropertyExpression) {
            // xs.length / xs.size  ->  size oracle
            PropertyExpression pe = (PropertyExpression) expr
            String prop = pe.propertyAsString
            if ((prop == 'length' || prop == 'size') &&
                pe.objectExpression instanceof VariableExpression) {
                return sizeOf(((VariableExpression) pe.objectExpression).name)
            }
            return null
        }

        if (expr instanceof MethodCallExpression) {
            return translateMethodCall((MethodCallExpression) expr)
        }

        if (expr instanceof BinaryExpression) {
            return translateBinary((BinaryExpression) expr)
        }

        // Anything else: outside fragment.
        return null
    }

    private Object translateBinary(BinaryExpression be) {
        int op = be.operation.type

        // Array subscript a[i] -> (select a i). The element value, modelled under
        // Z3's array theory (Phase 6). Recorded as a trigger when inside a quantifier.
        if (op == Types.LEFT_SQUARE_BRACKET) {
            if (!(be.leftExpression instanceof VariableExpression)) return null
            Object arr = arrayFor(((VariableExpression) be.leftExpression).name)
            Object idx = translate(be.rightExpression)
            if (idx == null) return null
            Object sel = session.select(arr, idx)
            if (triggerSink != null) triggerSink.add(sel)
            return sel
        }

        // Nullity: x == null / x != null, before we try to translate `null`.
        if (op == Types.COMPARE_EQUAL || op == Types.COMPARE_NOT_EQUAL) {
            VariableExpression ref = nullComparisonTarget(be)
            if (ref != null) {
                Object isNull = nullityOf(ref.name)
                return op == Types.COMPARE_EQUAL ? isNull : session.not(isNull)
            }
        }

        Object L = translate(be.leftExpression)
        Object R = translate(be.rightExpression)
        if (L == null || R == null) return null
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

    private Object translateMethodCall(MethodCallExpression mce) {
        String m = mce.methodAsString
        if (m == null) return null
        Expression recv = mce.objectExpression
        List<Expression> args = argList(mce)

        // Forall.range(lo, hi, { i -> body }) -> bounded universal quantifier.
        // Accept both the imported `Forall` (a VariableExpression) and the
        // fully-qualified `verification.Forall` (a PropertyExpression) — the
        // latter is needed inside @Invariant, where groovy-contracts' loop
        // transform doesn't carry the import.
        boolean isForall = (recv instanceof VariableExpression && ((VariableExpression) recv).name == 'Forall') ||
                           (recv instanceof PropertyExpression && ((PropertyExpression) recv).propertyAsString == 'Forall')
        if (m == 'range' && isForall &&
            args.size() == 3 && args.get(2) instanceof ClosureExpression) {
            return translateForallRange(args.get(0), args.get(1), (ClosureExpression) args.get(2))
        }

        // size() / isEmpty() / contains() need a named receiver for their oracle.
        if (!mce.implicitThis && recv instanceof VariableExpression) {
            String rn = ((VariableExpression) recv).name
            if (m == 'size' && args.isEmpty()) {
                return sizeOf(rn)
            }
            if (m == 'isEmpty' && args.isEmpty()) {
                return session.eq(sizeOf(rn), session.intLit(0L))
            }
            if (m == 'contains' && args.size() == 1) {
                Object a = translate(args.get(0))
                return a == null ? null : session.uninterpretedPred('contains$' + rn, a)
            }
        }

        // equals(): accept the method form of numeric equality, x.equals(y) === x == y.
        if (m == 'equals' && args.size() == 1) {
            Object l = translate(recv)
            Object r = translate(args.get(0))
            return (l == null || r == null) ? null : session.eq(l, r)
        }

        return null
    }

    /**
     * Translate {@code Forall.range(lo, hi, { i -> body })} to the bounded
     * universal {@code ∀ i. (lo <= i < hi) ⇒ body}. The closure's single
     * parameter is bound to a fresh quantified integer while the body is
     * translated — shadowing any same-named variable in scope, restored
     * afterwards — and the {@code (select arr i)} terms the body produces become
     * the quantifier's instantiation triggers.
     */
    private Object translateForallRange(Expression lo, Expression hi, ClosureExpression clo) {
        // Index variable: the closure's single declared parameter (`{ i -> ... }`)
        // or Groovy's implicit `it` (`{ a[it] >= 0 }`, whose parameter list is
        // null or empty depending on parse phase).
        Parameter[] ps = clo.parameters
        String iname
        if (ps == null || ps.length == 0) iname = 'it'
        else if (ps.length == 1) iname = ps[0].name
        else return null
        Expression bodyExpr = singleExprOf(clo.code)
        if (bodyExpr == null) return null

        Object iv = session.boundIntVar(iname + '$q' + (quantCounter++))
        Object prevBinding = env.get(iname)
        List<Object> prevSink = triggerSink
        List<Object> triggers = new ArrayList<Object>()
        env.put(iname, iv)
        triggerSink = triggers
        try {
            Object loH = translate(lo)
            Object hiH = translate(hi)
            Object bodyH = translate(bodyExpr)
            if (loH == null || hiH == null || bodyH == null) return null
            Object range = session.and([session.le(loH, iv), session.lt(iv, hiH)])
            Object matrix = session.implies(range, bodyH)
            return session.forall([iv], matrix, triggers)
        } finally {
            triggerSink = prevSink
            if (prevBinding == null) env.remove(iname) else env.put(iname, prevBinding)
        }
    }

    /** The single expression a closure/contract body reduces to, or null if it isn't a lone expression. */
    private static Expression singleExprOf(Statement code) {
        if (code instanceof BlockStatement) {
            List<Statement> ss = ((BlockStatement) code).statements
            return ss.size() == 1 ? singleExprOf(ss.get(0)) : null
        }
        if (code instanceof ExpressionStatement) return ((ExpressionStatement) code).expression
        if (code instanceof ReturnStatement) return ((ReturnStatement) code).expression
        return null
    }

    /** The reference operand of a {@code x == null}/{@code x != null}, or null if neither shape. */
    private static VariableExpression nullComparisonTarget(BinaryExpression be) {
        if (isNullLiteral(be.rightExpression) && be.leftExpression instanceof VariableExpression) {
            return (VariableExpression) be.leftExpression
        }
        if (isNullLiteral(be.leftExpression) && be.rightExpression instanceof VariableExpression) {
            return (VariableExpression) be.rightExpression
        }
        return null
    }

    private static boolean isNullLiteral(Expression e) {
        e instanceof ConstantExpression && ((ConstantExpression) e).value == null
    }

    private static List<Expression> argList(MethodCallExpression mce) {
        Expression a = mce.arguments
        if (a instanceof ArgumentListExpression) return ((ArgumentListExpression) a).expressions
        if (a instanceof TupleExpression) return ((TupleExpression) a).expressions
        return Collections.<Expression> emptyList()
    }

}
