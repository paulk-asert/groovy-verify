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
import org.codehaus.groovy.ast.ClassNode
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.Parameter
import org.codehaus.groovy.ast.expr.ArgumentListExpression
import org.codehaus.groovy.ast.expr.BinaryExpression
import org.codehaus.groovy.ast.expr.BooleanExpression
import org.codehaus.groovy.ast.expr.ClassExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.NotExpression
import org.codehaus.groovy.ast.expr.PropertyExpression
import org.codehaus.groovy.ast.expr.StaticMethodCallExpression
import org.codehaus.groovy.ast.expr.TernaryExpression
import org.codehaus.groovy.ast.expr.TupleExpression
import org.codehaus.groovy.ast.expr.UnaryMinusExpression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.IfStatement
import org.codehaus.groovy.ast.stmt.ReturnStatement
import org.codehaus.groovy.ast.stmt.Statement
import org.codehaus.groovy.syntax.Types

/**
 * Phase 62 — bounded property-based refutation. When Z3 returns UNKNOWN on a postcondition (the weak
 * refutation direction: a recurrence/aggregation-axiom timeout, e.g. {@code result == Fib.of(n)}),
 * this concrete interpreter is run over a small grid of integer inputs. For each tuple it checks the
 * {@code @Requires}, executes the body to a {@code result}, and evaluates the {@code @Ensures},
 * reporting the first input on which the postcondition is *false* as a runnable {@code fails on:} repro.
 *
 * It is a *witness*, not a proof of falsity — a bug needing inputs outside the grid escapes, so the
 * diagnostic stays best-effort. Because groovy-contracts' annotations are executable Groovy, this is
 * the natural fallback: run the spec it couldn't prove. The evaluable fragment mirrors
 * {@link PureEvaluator} (Int arithmetic, comparisons, boolean connectives, {@code ?:}, {@code if}/
 * {@code return}, single-assignment locals, same-class contract-free calls) over {@code Long} values,
 * plus the {@code Fib.of} spec helper. Anything outside it makes the whole search bail (returns null),
 * never a false witness. Kept separate from {@link PureEvaluator} so the Phase-8a folding path is
 * untouched.
 */
@CompileStatic
class ContractTester {

    private final ClassNode owner
    private int budget
    private static final int BUDGET = 50000

    /** A symmetric grid of small magnitudes — enough to surface off-by-one / wrong-formula bugs. */
    private static final long[] GRID = [0L, 1L, -1L, 2L, -2L, 3L, -3L, 4L, 5L, 8L, 10L] as long[]

    ContractTester(ClassNode owner) { this.owner = owner }

    /**
     * Search the integer grid for a counterexample to {@code post} (assuming {@code pre}), running
     * {@code node}'s body to bind {@code result}. Returns the failing argument list, or null if none
     * is found in budget or the method/contract steps outside the evaluable fragment.
     */
    List<Long> findCounterexample(MethodNode node, Expression pre, Expression post) {
        if (owner == null || post == null) return null
        Parameter[] ps = node.parameters
        int n = ps.length
        if (n == 0 || n > 5) return null   // grid^n would explode beyond a useful budget
        int[] idx = new int[n]
        while (true) {
            Map<String, Long> env = new HashMap<String, Long>()
            for (int i = 0; i < n; i++) env.put(ps[i].name, GRID[idx[i]])
            try {
                budget = BUDGET
                Boolean preOk = (pre == null) ? Boolean.TRUE : asBool(eval(pre, env))
                if (preOk == null) return null            // precondition not evaluable → can't help
                if (preOk.booleanValue()) {
                    Long result = runBody(node, env)
                    if (result == null) return null       // body not evaluable → bail
                    env.put('result', result)
                    Boolean postOk = asBool(eval(post, env))
                    if (postOk == null) return null       // postcondition not evaluable → bail
                    if (!postOk.booleanValue()) {
                        List<Long> args = new ArrayList<Long>(n)
                        for (int i = 0; i < n; i++) args.add(GRID[idx[i]])
                        return args
                    }
                }
            } catch (NotEvaluable ignored) {
                return null
            }
            // odometer over the grid
            int k = n - 1
            while (k >= 0) { if (++idx[k] < GRID.length) break; idx[k] = 0; k-- }
            if (k < 0) return null
        }
    }

    private Long runBody(MethodNode m, Map<String, Long> argEnv) {
        Statement body = (Statement) m.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (body == null) body = m.code
        if (body == null) return null
        Map<String, Long> env = new HashMap<String, Long>(argEnv)
        env.remove('result')
        try {
            execBlock(body, env)
        } catch (ReturnSignal r) {
            return Long.valueOf(r.value)
        }
        null   // fell off the end without an explicit return value
    }

    private static Boolean asBool(Object v) { (v instanceof Boolean) ? (Boolean) v : null }

    private void execBlock(Statement st, Map<String, Long> env) {
        if (--budget < 0) throw new NotEvaluable()
        if (st instanceof BlockStatement) {
            List<Statement> stmts = ((BlockStatement) st).statements
            for (int i = 0; i < stmts.size(); i++) execStmt(stmts.get(i), env, i == stmts.size() - 1)
            return
        }
        execStmt(st, env, true)
    }

    private void execStmt(Statement st, Map<String, Long> env, boolean last) {
        if (st instanceof ReturnStatement) {
            throw new ReturnSignal(evalLong(((ReturnStatement) st).expression, env))
        }
        if (st instanceof IfStatement) {
            IfStatement ifs = (IfStatement) st
            if (evalBool(ifs.booleanExpression, env)) execBlock(ifs.ifBlock, env)
            else if (ifs.elseBlock != null) execBlock(ifs.elseBlock, env)
            return
        }
        if (st instanceof BlockStatement) { execBlock(st, env); return }
        if (st instanceof ExpressionStatement) {
            Expression e = ((ExpressionStatement) st).expression
            if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.ASSIGN
                    && ((BinaryExpression) e).leftExpression instanceof VariableExpression) {
                BinaryExpression be = (BinaryExpression) e
                env.put(((VariableExpression) be.leftExpression).name, evalLong(be.rightExpression, env))
                return
            }
            if (last) throw new ReturnSignal(evalLong(e, env))   // Groovy implicit return
        }
        throw new NotEvaluable()
    }

    private long evalLong(Expression e, Map<String, Long> env) {
        Object v = eval(e, env)
        if (v instanceof Long) return ((Long) v).longValue()
        throw new NotEvaluable()
    }

    private boolean evalBool(Expression e, Map<String, Long> env) {
        Object v = eval(e, env)
        if (v instanceof Boolean) return ((Boolean) v).booleanValue()
        throw new NotEvaluable()
    }

    private Object eval(Expression e, Map<String, Long> env) {
        if (--budget < 0) throw new NotEvaluable()
        if (e instanceof ConstantExpression) {
            Object v = ((ConstantExpression) e).value
            if (v instanceof Integer || v instanceof Long || v instanceof Short || v instanceof Byte) {
                return Long.valueOf(((Number) v).longValue())
            }
            if (v instanceof Boolean) return v
            throw new NotEvaluable()
        }
        if (e instanceof VariableExpression) {
            String n = ((VariableExpression) e).name
            if (n == 'true') return Boolean.TRUE
            if (n == 'false') return Boolean.FALSE
            Long v = env.get(n)
            if (v == null) throw new NotEvaluable()
            return v
        }
        if (e instanceof BooleanExpression) return eval(((BooleanExpression) e).expression, env)
        if (e instanceof NotExpression) return Boolean.valueOf(!evalBool(((NotExpression) e).expression, env))
        if (e instanceof UnaryMinusExpression) {
            return Long.valueOf(-evalLong(((UnaryMinusExpression) e).expression, env))
        }
        if (e instanceof TernaryExpression) {
            TernaryExpression te = (TernaryExpression) e
            return evalBool(te.booleanExpression, env) ? eval(te.trueExpression, env) : eval(te.falseExpression, env)
        }
        if (e instanceof BinaryExpression) return evalBinary((BinaryExpression) e, env)
        if (e instanceof MethodCallExpression) return evalMethodCall((MethodCallExpression) e, env)
        if (e instanceof StaticMethodCallExpression) {
            StaticMethodCallExpression sm = (StaticMethodCallExpression) e
            Long fib = tryFib(sm.ownerType?.nameWithoutPackage, sm.method, argsOf(sm.arguments), env)
            if (fib != null) return fib
            throw new NotEvaluable()
        }
        throw new NotEvaluable()
    }

    private Object evalBinary(BinaryExpression be, Map<String, Long> env) {
        int op = be.operation.type
        if (op == Types.LOGICAL_AND) return Boolean.valueOf(evalBool(be.leftExpression, env) && evalBool(be.rightExpression, env))
        if (op == Types.LOGICAL_OR)  return Boolean.valueOf(evalBool(be.leftExpression, env) || evalBool(be.rightExpression, env))
        // `==>` (Groovy 5 implication) lowers to !a || b
        if (be.operation.text == '==>') return Boolean.valueOf(!evalBool(be.leftExpression, env) || evalBool(be.rightExpression, env))
        if (be.operation.text == '/') throw new NotEvaluable()   // BigDecimal division: not a Long
        long l = evalLong(be.leftExpression, env)
        long r = evalLong(be.rightExpression, env)
        switch (op) {
            case Types.PLUS:                       return Long.valueOf(l + r)
            case Types.MINUS:                      return Long.valueOf(l - r)
            case Types.MULTIPLY:                   return Long.valueOf(l * r)
            case Types.COMPARE_EQUAL:              return Boolean.valueOf(l == r)
            case Types.COMPARE_NOT_EQUAL:          return Boolean.valueOf(l != r)
            case Types.COMPARE_LESS_THAN:          return Boolean.valueOf(l < r)
            case Types.COMPARE_LESS_THAN_EQUAL:    return Boolean.valueOf(l <= r)
            case Types.COMPARE_GREATER_THAN:       return Boolean.valueOf(l > r)
            case Types.COMPARE_GREATER_THAN_EQUAL: return Boolean.valueOf(l >= r)
        }
        if (be.operation.text == '%') { if (r == 0L) throw new NotEvaluable(); return Long.valueOf(l % r) }
        throw new NotEvaluable()
    }

    private Object evalMethodCall(MethodCallExpression mce, Map<String, Long> env) {
        List<Expression> args = argsOf(mce.arguments)
        // Fib.of(k) — the recognised spec helper (matches Encoder's isFib shapes).
        String recvName = fibReceiverName(mce.objectExpression)
        Long fib = tryFib(recvName, mce.methodAsString, args, env)
        if (fib != null) return fib
        // a.intdiv(b) / a.mod(b) — the integer-division idioms.
        if (mce.objectExpression != null && args.size() == 1) {
            String m = mce.methodAsString
            if (m == 'intdiv') {
                long a = evalLong(mce.objectExpression, env), b = evalLong(args.get(0), env)
                if (b == 0L) throw new NotEvaluable()
                return Long.valueOf((long) (a / b))            // truncate toward zero
            }
            if (m == 'mod') {
                long a = evalLong(mce.objectExpression, env), b = evalLong(args.get(0), env)
                if (b == 0L) throw new NotEvaluable()
                return Long.valueOf(Math.floorMod(a, b))       // BigInteger.mod: non-negative
            }
        }
        // A same-class (this/implicit) contract-free call.
        if (mce.implicitThis || isThis(mce.objectExpression)) {
            List<Long> vals = new ArrayList<Long>()
            for (Expression a : args) vals.add(Long.valueOf(evalLong(a, env)))
            return invoke(mce.methodAsString, vals)
        }
        throw new NotEvaluable()
    }

    private Long tryFib(String recvSimpleName, String method, List<Expression> args, Map<String, Long> env) {
        if (recvSimpleName == 'Fib' && method == 'of' && args.size() == 1) {
            return Long.valueOf(fib(evalLong(args.get(0), env)))
        }
        null
    }

    private static String fibReceiverName(Expression recv) {
        if (recv instanceof VariableExpression) return ((VariableExpression) recv).name
        if (recv instanceof PropertyExpression) return ((PropertyExpression) recv).propertyAsString
        if (recv instanceof ClassExpression) return ((ClassExpression) recv).type?.nameWithoutPackage
        null
    }

    private static boolean isThis(Expression recv) {
        recv instanceof VariableExpression && ((VariableExpression) recv).name == 'this'
    }

    /** Fibonacci matching {@link Fib#of}: of(0)=0, of(1)=1, of(2)=1, … (bounded, no deep recursion). */
    private long fib(long i) {
        if (i < 0) throw new NotEvaluable()
        if (i < 2) return i
        long a = 0, b = 1
        for (long k = 2; k <= i; k++) {
            if (--budget < 0) throw new NotEvaluable()
            long t = a + b; a = b; b = t
        }
        b
    }

    private Long invoke(String name, List<Long> args) {
        if (--budget < 0) throw new NotEvaluable()
        MethodNode m = resolve(name, args.size())
        if (m == null) throw new NotEvaluable()
        Map<String, Long> env = new HashMap<String, Long>()
        Parameter[] ps = m.parameters
        for (int i = 0; i < ps.length; i++) env.put(ps[i].name, args.get(i))
        Long r = runBody(m, env)
        if (r == null) throw new NotEvaluable()
        r
    }

    private MethodNode resolve(String name, int arity) {
        for (MethodNode m : owner.getMethods(name)) {
            if (m.parameters.length == arity) return hasContract(m) ? null : m
        }
        null
    }

    private static boolean hasContract(MethodNode m) {
        for (org.codehaus.groovy.ast.AnnotationNode an : m.getAnnotations()) {
            String n = an.classNode?.name
            if (n == 'groovy.contracts.Requires' || n == 'groovy.contracts.Ensures'
                    || n == 'verification.ContractSource') return true
        }
        false
    }

    private static List<Expression> argsOf(Expression a) {
        if (a instanceof ArgumentListExpression) return ((ArgumentListExpression) a).expressions
        if (a instanceof TupleExpression) return ((TupleExpression) a).expressions
        Collections.<Expression> emptyList()
    }

    private static class ReturnSignal extends RuntimeException {
        final long value
        ReturnSignal(long value) { super(null, null, false, false); this.value = value }
    }

    private static class NotEvaluable extends RuntimeException {
        NotEvaluable() { super(null, null, false, false) }
    }
}
