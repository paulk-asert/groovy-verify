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
import org.apache.groovy.ast.tools.ExpressionUtils
import org.codehaus.groovy.ast.AnnotationNode
import org.codehaus.groovy.ast.ClassHelper
import org.codehaus.groovy.ast.ClassNode
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.Parameter
import org.codehaus.groovy.ast.expr.ArgumentListExpression
import org.codehaus.groovy.ast.expr.BinaryExpression
import org.codehaus.groovy.ast.expr.BooleanExpression
import org.codehaus.groovy.ast.expr.ClassExpression
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.ExpressionTransformer
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.NotExpression
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
 * Phase 8a — closed evaluation. A small tree-walking interpreter that computes the value of a
 * same-class, side-effect-free method applied to <em>constant</em> arguments (e.g. {@code pow2(10)},
 * {@code factorial(5)}). It evaluates the *clean* CONVERSION body snapshot over the evaluable
 * fragment — integer literals, parameters, {@code + - * %}, unary minus, comparisons, boolean
 * connectives, {@code ?:}/{@code if}/{@code return}, single-assignment locals, and recursive or
 * other same-class evaluable calls. Anything else (division, array access, field access, an
 * unresolved or non-evaluable call) makes the call un-evaluable, so the verifier simply falls back
 * to "skipped" — the interpreter never guesses.
 * <p>
 * Soundness rests on two things: it only evaluates functions whose body lies entirely in this
 * fragment (a conservative purity proxy — no representable side effects), and it computes with
 * {@code long}, matching the encoder's mathematical-integer model (the 32-bit overflow gap is the
 * separate bounded-int item, not introduced here). A step budget bounds non-terminating recursion.
 */
@CompileStatic
class PureEvaluator {

    private final ClassNode owner
    private int budget

    PureEvaluator(ClassNode owner, int budget = 20000) {
        this.owner = owner
        this.budget = budget
    }

    /**
     * If {@code e} is a same-class call with all-constant arguments, evaluate it to a value;
     * otherwise null. This is the entry point the encoder uses.
     */
    Long tryEvaluate(Expression e) {
        try {
            Call c = callInfo(e)
            if (c == null) return null
            List<Long> vals = new ArrayList<Long>()
            for (Expression a : c.args) {
                Long v = foldLong(a)
                if (v == null) return null   // a non-constant argument → not a closed call
                vals.add(v)
            }
            return invoke(c.name, vals)
        } catch (NotEvaluable ignored) {
            return null
        }
    }

    /**
     * Phase 8a (bounded symbolic unfolding) — if {@code c} resolves to a same-class function whose
     * body is a <em>single expression</em>, return that body with the formals substituted by the
     * call's argument expressions (a faithful inline of the definition; cf. F\*'s unfolding). The
     * encoder translates the result, re-entering for any nested calls, so recursion unfolds one level
     * per call up to a fuel bound. Returns null for a call that doesn't resolve to a single-expression
     * body — {@code if}/{@code return} chains (e.g. the statement form of {@code factorial}) are not
     * inlined, so the encoder leaves such a call to the uninterpreted-function bottom.
     */
    Expression unfoldBody(Call c) {
        MethodNode m = resolve(c.name, c.args.size())
        if (m == null) return null
        Statement body = (Statement) m.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (body == null) body = m.getCode()
        Expression expr = singleExpr(body)
        if (expr == null) return null
        Parameter[] ps = m.parameters
        if (ps.length != c.args.size()) return null
        Map<String, Expression> sub = new HashMap<String, Expression>()
        for (int i = 0; i < ps.length; i++) sub.put(ps[i].name, c.args.get(i))
        return substitute(expr, sub)
    }

    /** The single expression a body reduces to — {@code { expr }} or {@code { return expr }}; else null. */
    private static Expression singleExpr(Statement body) {
        if (body == null) return null
        Statement st = body
        if (body instanceof BlockStatement) {
            List<Statement> stmts = ((BlockStatement) body).statements
            if (stmts.size() != 1) return null
            st = stmts.get(0)
        }
        if (st instanceof ReturnStatement) return ((ReturnStatement) st).expression
        if (st instanceof ExpressionStatement) return ((ExpressionStatement) st).expression
        return null
    }

    /**
     * Deep-copy {@code e}, replacing each formal-parameter variable with its argument expression.
     *
     * Phase 198 — closure-aware. A helper body's quantifier closures ({@code (0..<N).every { r -> … }})
     * previously kept their formal names UNSUBSTITUTED (the transformer never descended into closure
     * statements), so the unfolded body resolved against the CALLER's same-named scope — for a goal-side
     * unfold like {@code valid(N, ticket2, …, cs2, t2)} the closures still said {@code ticket}/{@code cs},
     * i.e. the goal silently became the pre-state fact and any preservation lemma "verified" vacuously.
     * Now: (a) substitution descends into closure code (expression statements only — a helper body is an
     * expression tree); (b) closure parameters shadow (hygiene); (c) the SAM shorthand {@code cs(r)} — an
     * implicit-this call whose NAME is the formal — is renamed when the actual is a plain variable, and
     * the whole unfold is REFUSED (null → the call stays uninterpreted, a sound over-approximation) when
     * such a shorthand's actual is any other expression shape.
     */
    private static Expression substitute(Expression e, Map<String, Expression> sub) {
        boolean[] refuse = [false]
        ExpressionTransformer t = new ExpressionTransformer() {
            private Map<String, Expression> active = sub
            @Override
            Expression transform(Expression expr) {
                if (expr instanceof VariableExpression) {
                    Expression rep = active.get(((VariableExpression) expr).name)
                    return rep != null ? rep : expr
                }
                if (expr instanceof MethodCallExpression) {
                    MethodCallExpression mc = (MethodCallExpression) expr
                    Expression rep = mc.implicitThis ? active.get(mc.methodAsString) : null
                    if (rep != null) {
                        // f(x) shorthand on a substituted formal: rename to the actual when it is a plain
                        // variable; anything else can't be spliced as a call name — refuse the unfold.
                        if (rep instanceof VariableExpression) {
                            MethodCallExpression out = new MethodCallExpression(mc.objectExpression,
                                ((VariableExpression) rep).name, transform(mc.arguments))
                            out.implicitThis = true
                            out.setSourcePosition(mc)
                            return out
                        }
                        refuse[0] = true
                        return expr
                    }
                    return expr.transformExpression(this)
                }
                if (expr instanceof ClosureExpression) {
                    ClosureExpression ce = (ClosureExpression) expr
                    // Hygiene: closure parameters shadow same-named formals inside this closure.
                    Map<String, Expression> outer = active
                    Map<String, Expression> inner = new HashMap<String, Expression>(outer)
                    if (ce.parameters != null) for (Parameter cp : ce.parameters) inner.remove(cp.name)
                    if (ce.parameters == null || ce.parameters.length == 0) inner.remove('it')
                    active = inner
                    try {
                        Statement code = ce.code
                        if (code instanceof BlockStatement) {
                            List<Statement> stmts = ((BlockStatement) code).statements
                            List<Statement> out = new ArrayList<Statement>(stmts.size())
                            boolean changed = false
                            for (Statement st : stmts) {
                                if (st instanceof ExpressionStatement) {
                                    Expression oldE = ((ExpressionStatement) st).expression
                                    Expression newE = transform(oldE)
                                    if (!newE.is(oldE)) {
                                        Statement ns = new ExpressionStatement(newE)
                                        ns.setSourcePosition(st)
                                        out.add(ns); changed = true
                                        continue
                                    }
                                } else if (st instanceof ReturnStatement) {
                                    Expression oldE = ((ReturnStatement) st).expression
                                    Expression newE = transform(oldE)
                                    if (!newE.is(oldE)) {
                                        Statement ns = new ReturnStatement(newE)
                                        ns.setSourcePosition(st)
                                        out.add(ns); changed = true
                                        continue
                                    }
                                } else if (!active.isEmpty()) {
                                    // a statement shape we can't rewrite — refuse rather than half-substitute
                                    refuse[0] = true
                                }
                                out.add(st)
                            }
                            if (changed) {
                                ClosureExpression nce = new ClosureExpression(ce.parameters,
                                    new BlockStatement(out, ((BlockStatement) code).variableScope))
                                nce.setSourcePosition(ce)
                                return nce
                            }
                        }
                        return ce
                    } finally {
                        active = outer
                    }
                }
                return expr.transformExpression(this)
            }
        }
        Expression out = t.transform(e)
        return refuse[0] ? null : out
    }

    /**
     * Recognise a same-class (owner) call to a <em>pure</em> (contract-free) method — implicit/explicit
     * {@code this}, owner-class receiver, or static. Returns null for any other receiver, or for a call
     * that resolves to a contracted method (left to the inter-procedural/induction path).
     */
    Call callInfo(Expression e) {
        if (e instanceof StaticMethodCallExpression) {
            StaticMethodCallExpression sce = (StaticMethodCallExpression) e
            if (owner != null && sce.ownerType != null && sce.ownerType.name == owner.name) {
                return pureCall(sce.method, argsOf(sce.arguments))
            }
            return null
        }
        if (e instanceof MethodCallExpression) {
            MethodCallExpression mce = (MethodCallExpression) e
            Expression recv = mce.objectExpression
            boolean sameClass = mce.implicitThis ||
                (recv instanceof VariableExpression && ((VariableExpression) recv).name == 'this') ||
                (recv instanceof ClassExpression && owner != null && recv.type?.name == owner.name)
            if (sameClass) return pureCall(mce.methodAsString, argList(mce))
            return null
        }
        return null
    }

    /** A {@link Call} only if {@code name}/arity resolves to a pure (contract-free) same-class method. */
    private Call pureCall(String name, List<Expression> args) {
        if (resolve(name, args.size()) == null) return null
        new Call(name: name, args: args)
    }

    /** Fold a closed expression to a {@code long}, or null if it isn't an integral constant. */
    private static Long foldLong(Expression e) {
        Expression folded = ExpressionUtils.transformInlineConstants(e, ClassHelper.int_TYPE)
        if (folded instanceof ConstantExpression) {
            Object v = ((ConstantExpression) folded).value
            if (v instanceof Integer || v instanceof Long || v instanceof Short || v instanceof Byte) {
                return ((Number) v).longValue()
            }
        }
        return null
    }

    private Long invoke(String name, List<Long> args) {
        if (--budget < 0) throw new NotEvaluable()
        MethodNode m = resolve(name, args.size())
        if (m == null) throw new NotEvaluable()
        Statement body = (Statement) m.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (body == null) body = m.getCode()
        if (body == null) throw new NotEvaluable()

        Map<String, Long> env = new HashMap<String, Long>()
        Parameter[] ps = m.parameters
        if (ps.length != args.size()) throw new NotEvaluable()
        for (int i = 0; i < ps.length; i++) env.put(ps[i].name, args.get(i))

        try {
            execBlock(body, env)
        } catch (ReturnSignal r) {
            return r.value
        }
        throw new NotEvaluable()   // fell off the end without returning a value
    }

    /**
     * The declared return type of the pure function a {@code Call} resolves to, or {@code null} if it
     * cannot be resolved. Lets the Encoder pick the SMT range sort of the call's shared symbol from the
     * callee's signature (so an enum/Boolean-returning helper is declared over its real sort, not Int).
     */
    ClassNode returnType(Call c) {
        if (c == null) return null
        MethodNode m = resolve(c.name, c.args.size())
        m?.returnType
    }

    /** Phase 211 — the callee's declared parameter types (null when unresolvable), so the encoder can
     *  translate each argument of a pure-helper call in its DECLARED sort (a String param must not be
     *  translated as an Int term). */
    ClassNode[] paramTypes(Call c) {
        if (c == null) return null
        MethodNode m = resolve(c.name, c.args.size())
        m?.parameters?.collect { it.type } as ClassNode[]
    }

    private MethodNode resolve(String name, int arity) {
        if (owner == null || name == null) return null
        for (MethodNode m : owner.getMethods(name)) {
            // A contracted method is the inter-procedural/induction path's territory (its @Ensures is
            // assumed, or its inductive hypothesis applied); evaluating or unfolding it here would steal
            // the call from that machinery, so treat only contract-free methods as pure functions.
            if (m.parameters.length == arity) return hasContract(m) ? null : m
        }
        null
    }

    private static boolean hasContract(MethodNode m) {
        for (AnnotationNode an : m.getAnnotations()) {
            String n = an.classNode?.name
            if (n == 'groovy.contracts.Requires' || n == 'groovy.contracts.Ensures'
                    || n == 'verification.ContractSource') {
                return true
            }
        }
        false
    }

    /** Execute a statement (block), throwing {@link ReturnSignal} when a value is returned. */
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
        if (st instanceof BlockStatement) {
            execBlock(st, env)
            return
        }
        if (st instanceof ExpressionStatement) {
            Expression e = ((ExpressionStatement) st).expression
            // single-assignment local: def x = <expr>  (x usable later in the body)
            if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.ASSIGN
                    && ((BinaryExpression) e).leftExpression instanceof VariableExpression) {
                BinaryExpression be = (BinaryExpression) e
                env.put(((VariableExpression) be.leftExpression).name, evalLong(be.rightExpression, env))
                return
            }
            if (last) {
                throw new ReturnSignal(evalLong(e, env))   // Groovy implicit return
            }
        }
        throw new NotEvaluable()
    }

    private long evalLong(Expression e, Map<String, Long> env) {
        Object v = eval(e, env)
        if (v instanceof Long) return (Long) v
        throw new NotEvaluable()
    }

    private boolean evalBool(Expression e, Map<String, Long> env) {
        Object v = eval(e, env)
        if (v instanceof Boolean) return (Boolean) v
        throw new NotEvaluable()
    }

    private Object eval(Expression e, Map<String, Long> env) {
        if (--budget < 0) throw new NotEvaluable()

        if (e instanceof ConstantExpression) {
            Object v = ((ConstantExpression) e).value
            if (v instanceof Integer || v instanceof Long || v instanceof Short || v instanceof Byte) {
                return ((Number) v).longValue()
            }
            if (v instanceof Boolean) return v
            throw new NotEvaluable()
        }
        if (e instanceof VariableExpression) {
            String n = ((VariableExpression) e).name
            if (n == 'true') return Boolean.TRUE
            if (n == 'false') return Boolean.FALSE
            Long v = env.get(n)
            if (v == null) throw new NotEvaluable()   // unbound (e.g. a field) → not evaluable
            return v
        }
        // NotExpression IS-A BooleanExpression — it must be matched FIRST or the unwrap drops the
        // negation and `!x` evaluates as `x` (Phase 205).
        if (e instanceof NotExpression) return !evalBool(((NotExpression) e).expression, env)
        if (e instanceof BooleanExpression) return eval(((BooleanExpression) e).expression, env)
        if (e instanceof UnaryMinusExpression) return -evalLong(((UnaryMinusExpression) e).expression, env)
        if (e instanceof TernaryExpression) {
            TernaryExpression te = (TernaryExpression) e
            return evalBool(te.booleanExpression, env) ? eval(te.trueExpression, env) : eval(te.falseExpression, env)
        }
        if (e instanceof BinaryExpression) return evalBinary((BinaryExpression) e, env)
        if (e instanceof MethodCallExpression || e instanceof StaticMethodCallExpression) {
            Call c = callInfo(e)                        // same-class call (this/owner/static)
            if (c == null) throw new NotEvaluable()
            List<Long> vals = new ArrayList<Long>()
            for (Expression a : c.args) vals.add(evalLong(a, env))
            return invoke(c.name, vals)                 // recurse; ReturnSignal handled per-invoke
        }
        throw new NotEvaluable()
    }

    private Object evalBinary(BinaryExpression be, Map<String, Long> env) {
        int op = be.operation.type
        switch (op) {
            case Types.LOGICAL_AND: return evalBool(be.leftExpression, env) && evalBool(be.rightExpression, env)
            case Types.LOGICAL_OR:  return evalBool(be.leftExpression, env) || evalBool(be.rightExpression, env)
        }
        long l = evalLong(be.leftExpression, env)
        long r = evalLong(be.rightExpression, env)
        switch (op) {
            case Types.PLUS:                       return l + r
            case Types.MINUS:                      return l - r
            case Types.MULTIPLY:                   return l * r
            case Types.MOD:                        if (r == 0L) throw new NotEvaluable(); return l % r
            case Types.COMPARE_EQUAL:              return l == r
            case Types.COMPARE_NOT_EQUAL:          return l != r
            case Types.COMPARE_LESS_THAN:          return l < r
            case Types.COMPARE_LESS_THAN_EQUAL:    return l <= r
            case Types.COMPARE_GREATER_THAN:       return l > r
            case Types.COMPARE_GREATER_THAN_EQUAL: return l >= r
            default:                               throw new NotEvaluable()
        }
    }

    private static List<Expression> argList(MethodCallExpression mce) {
        argsOf(mce.arguments)
    }

    private static List<Expression> argsOf(Expression a) {
        if (a instanceof ArgumentListExpression) return ((ArgumentListExpression) a).expressions
        if (a instanceof TupleExpression) return ((TupleExpression) a).expressions
        return Collections.<Expression> emptyList()
    }

    /** A recognised same-class call: method name + argument expressions. */
    @CompileStatic
    static class Call {
        String name
        List<Expression> args
    }

    /** Control-flow signal carrying a returned value. */
    @CompileStatic
    private static class ReturnSignal extends RuntimeException {
        final long value
        ReturnSignal(long value) { super(null, null, false, false); this.value = value }
    }

    /** Raised when an expression/statement is outside the evaluable fragment. */
    @CompileStatic
    private static class NotEvaluable extends RuntimeException {
        NotEvaluable() { super(null, null, false, false) }
    }
}
