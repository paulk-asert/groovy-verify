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
import org.codehaus.groovy.ast.expr.DeclarationExpression
import org.codehaus.groovy.ast.expr.EmptyExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.ExpressionTransformer
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.NotExpression
import org.codehaus.groovy.ast.expr.PostfixExpression
import org.codehaus.groovy.ast.expr.PrefixExpression
import org.codehaus.groovy.ast.expr.StaticMethodCallExpression
import org.codehaus.groovy.ast.expr.TernaryExpression
import org.codehaus.groovy.ast.expr.TupleExpression
import org.codehaus.groovy.ast.expr.UnaryMinusExpression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.EmptyStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.IfStatement
import org.codehaus.groovy.ast.stmt.ReturnStatement
import org.codehaus.groovy.ast.stmt.Statement
import org.codehaus.groovy.syntax.Token
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
    private final int stepBudget

    PureEvaluator(ClassNode owner, int budget = 20000) {
        this.owner = owner
        this.budget = budget
        this.stepBudget = budget
    }

    /**
     * If {@code e} is a same-class call with all-constant arguments, evaluate it to a value;
     * otherwise null. This is the entry point the encoder uses.
     */
    Long tryEvaluate(Expression e) {
        // Phase 356 — each closed evaluation gets the whole step budget: it was one per evaluator (per method), so a
        // single call that exhausted it — easy once loops run — left every later call in the method unevaluable
        budget = stepBudget
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
     * per call up to a fuel bound. Phase 353 — a body that is not a single expression is FOLDED into one
     * ({@link #foldStatements}): local declarations and reassignments become substitutions, {@code return e}
     * (or a trailing expression) the value, and an {@code if} a ternary over the two continuations — so
     * {@code int n = x; n = n + 1; return n} unfolds to {@code (x + 1)} and the statement form of
     * {@code factorial} to {@code n <= 0 ? 1 : n * factorial(n - 1)}. Any other statement (a loop, a
     * {@code switch}, a {@code throw}, a compound assignment) refuses: null, and the encoder leaves the call
     * to the uninterpreted-function bottom, as before.
     */
    Expression unfoldBody(Call c, List<Expression> facts = null) {
        MethodNode m = resolve(c.name, c.args.size())
        if (m == null) return null
        Statement body = (Statement) m.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (body == null) body = m.getCode()
        Parameter[] ps = m.parameters
        if (ps.length != c.args.size()) return null
        Map<String, Expression> sub = new HashMap<String, Expression>()
        for (int i = 0; i < ps.length; i++) sub.put(ps[i].name, c.args.get(i))
        Expression expr = singleExpr(body)
        Expression out
        FoldCtx ctx = new FoldCtx()
        if (expr != null) {
            out = substitute(expr, sub)
        } else {
            ctx.types = declaredTypes(m, body)
            out = foldStatements(statementsOf(body), 0, sub, ctx, null)
        }
        // Phase 353 — the unfolded body is translated in the CALLER's scope, where a sibling class's field name means
        // the caller's same-named field (or nothing): a sibling helper reading its own state (`x + base` on Util) is
        // not inlined — the call stays an uninterpreted function, a sound over-approximation
        if (out != null && m.declaringClass != null && owner != null && m.declaringClass.name != owner.name &&
                (mentionsField(out, m.declaringClass) || ctx.facts.any { Expression f -> mentionsField(f, m.declaringClass) })) return null
        if (out != null && facts != null) facts.addAll(ctx.facts)
        out
    }

    /** Phase 353/355 — one fold's state: its statement budget, the loop-exit facts it has gathered (Phase 355), and the
     *  helper's declared local and parameter types. */
    private static class FoldCtx {
        int budget = FOLD_BUDGET
        List<Expression> facts = new ArrayList<Expression>()
        Map<String, ClassNode> types = new HashMap<String, ClassNode>()
    }

    /** Phase 355 — a fresh suffix per loop summary, so each ground call term's exit state has its own names. */
    private static final java.util.concurrent.atomic.AtomicInteger LOOP_SEQ = new java.util.concurrent.atomic.AtomicInteger()

    /** Phase 355 — the declared type of each parameter and local of {@code m}. */
    private static Map<String, ClassNode> declaredTypes(MethodNode m, Statement body) {
        Map<String, ClassNode> out = new HashMap<String, ClassNode>()
        for (Parameter p : m.parameters) out.put(p.name, p.type)
        body?.visit(new org.codehaus.groovy.ast.CodeVisitorSupport() {
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (de.leftExpression instanceof VariableExpression) {
                    out.put(((VariableExpression) de.leftExpression).name, ((VariableExpression) de.leftExpression).originType)
                }
                super.visitDeclarationExpression(de)
            }
            @Override void visitForLoop(org.codehaus.groovy.ast.stmt.ForStatement fs) {
                if (fs.variable != null && fs.variable != org.codehaus.groovy.ast.stmt.ForStatement.FOR_LOOP_DUMMY) {
                    out.put(fs.variable.name, fs.variable.originType)
                }
                super.visitForLoop(fs)
            }
        })
        out
    }

    /** Phase 353 — does {@code e} read (bare or as {@code this.f}) a field of {@code cls} or a superclass? */
    private static boolean mentionsField(Expression e, ClassNode cls) {
        Set<String> fields = new HashSet<String>()
        for (ClassNode c = cls; c != null; c = c.superClass) for (org.codehaus.groovy.ast.FieldNode f : c.fields) fields.add(f.name)
        if (fields.isEmpty()) return false
        boolean[] hit = [false] as boolean[]
        e.visit(new org.codehaus.groovy.ast.CodeVisitorSupport() {
            @Override void visitVariableExpression(VariableExpression v) { if (fields.contains(v.name)) hit[0] = true }
            @Override void visitPropertyExpression(org.codehaus.groovy.ast.expr.PropertyExpression pe) {
                if (fields.contains(pe.propertyAsString)) hit[0] = true
                super.visitPropertyExpression(pe)
            }
        })
        hit[0]
    }

    /** Phase 353 — the most statements one fold may visit (an {@code if} visits its continuation twice). */
    private static final int FOLD_BUDGET = 64

    private static List<Statement> statementsOf(Statement s) {
        if (s == null || s instanceof EmptyStatement) return Collections.<Statement> emptyList()
        if (s instanceof BlockStatement) return ((BlockStatement) s).statements
        Collections.singletonList(s)
    }

    /**
     * Phase 353 — the value of running {@code stmts[i..]} under {@code env} (formals ↦ actuals, locals ↦ their
     * current value, both already substituted), as one expression; null when a statement can't be folded or
     * the path falls off the end without a value. {@code pc} is the path condition reaching here (null: true),
     * which guards the loop-exit facts a summarised loop adds to {@code ctx} (Phase 355).
     */
    private static Expression foldStatements(List<Statement> stmts, int i, Map<String, Expression> env, FoldCtx ctx, Expression pc) {
        if (--ctx.budget < 0 || i >= stmts.size()) return null
        Statement st = stmts.get(i)
        if (st instanceof EmptyStatement) return foldStatements(stmts, i + 1, env, ctx, pc)
        // Phase 355 — a loop with a proven variant is summarised by its exit state (see foldLoop)
        Object spec = st.getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY)
        if (spec instanceof LoopSpec) {
            Map<String, Expression> after = foldLoop((LoopSpec) spec, env, ctx, pc)
            return after == null ? null : foldStatements(stmts, i + 1, after, ctx, pc)
        }
        if (st instanceof BlockStatement) {   // a nested block: its statements, then the rest
            List<Statement> rest = new ArrayList<Statement>(((BlockStatement) st).statements)
            rest.addAll(stmts.subList(i + 1, stmts.size()))
            return foldStatements(rest, 0, env, ctx, pc)
        }
        if (st instanceof ReturnStatement) return pure(substitute(((ReturnStatement) st).expression, env))
        if (st instanceof IfStatement) {
            IfStatement ifs = (IfStatement) st
            Expression cond = pure(substitute(ifs.booleanExpression, env))
            if (cond == null) return null
            List<Statement> rest = stmts.subList(i + 1, stmts.size())
            List<Statement> thenL = new ArrayList<Statement>(statementsOf(ifs.ifBlock))
            thenL.addAll(rest)
            List<Statement> elseL = new ArrayList<Statement>(statementsOf(ifs.elseBlock))
            elseL.addAll(rest)
            BooleanExpression be = cond instanceof BooleanExpression ? (BooleanExpression) cond : new BooleanExpression(cond)
            Expression t = foldStatements(thenL, 0, env, ctx, conj(pc, be))
            if (t == null) return null
            Expression f = foldStatements(elseL, 0, env, ctx, conj(pc, new NotExpression(be)))
            if (f == null) return null
            TernaryExpression te = new TernaryExpression(be, t, f)
            te.setSourcePosition(ifs)
            return te
        }
        Map<String, Expression> next = bindStatement(st, env)
        if (next != null) return next.is(env) ? null : foldStatements(stmts, i + 1, next, ctx, pc)
        // a trailing expression is the method's value (Groovy's implicit return); anywhere else it is a statement
        // whose effect the fold can't see
        Expression e = st instanceof ExpressionStatement ? ((ExpressionStatement) st).expression : null
        e != null && i == stmts.size() - 1 ? pure(substitute(e, env)) : null
    }

    /** Phase 353/354 — {@code env} updated by a binding statement (a declaration, a plain or compound assignment to a
     *  variable, or {@code x++} / {@code --x}); {@code env} itself when it is one but its value can't be folded;
     *  null when it isn't a binding statement. */
    private static Map<String, Expression> bindStatement(Statement st, Map<String, Expression> env) {
        if (!(st instanceof ExpressionStatement)) return null
        Expression e = ((ExpressionStatement) st).expression
        String bound = null
        Expression value = null
        if (e instanceof DeclarationExpression) {
            DeclarationExpression de = (DeclarationExpression) e
            if (!(de.leftExpression instanceof VariableExpression)) return env
            bound = ((VariableExpression) de.leftExpression).name
            // `int r;` — read before any assignment it is an unknown (hidden, `$`-prefixed) value, never a name the
            // caller's scope could capture
            value = de.rightExpression instanceof EmptyExpression ? new VariableExpression('$unassigned$' + bound) : de.rightExpression
        } else if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.ASSIGN &&
                ((BinaryExpression) e).leftExpression instanceof VariableExpression) {
            bound = ((VariableExpression) ((BinaryExpression) e).leftExpression).name
            value = ((BinaryExpression) e).rightExpression
        }
        // Phase 354 — `x op= e` is `x = x op e`; `x++` / `--x` as a statement is `x = x ± 1`
        if (bound == null && e instanceof BinaryExpression && ((BinaryExpression) e).leftExpression instanceof VariableExpression) {
            int base = compoundBase(((BinaryExpression) e).operation.type)
            if (base >= 0) {
                BinaryExpression be = (BinaryExpression) e
                bound = ((VariableExpression) be.leftExpression).name
                value = new BinaryExpression(be.leftExpression, Token.newSymbol(base, be.operation.startLine, be.operation.startColumn), be.rightExpression)
            }
        }
        if (bound == null && (e instanceof PostfixExpression || e instanceof PrefixExpression)) {
            Expression operand = e instanceof PostfixExpression ? ((PostfixExpression) e).expression : ((PrefixExpression) e).expression
            Token op = e instanceof PostfixExpression ? ((PostfixExpression) e).operation : ((PrefixExpression) e).operation
            if (operand instanceof VariableExpression && (op.type == Types.PLUS_PLUS || op.type == Types.MINUS_MINUS)) {
                bound = ((VariableExpression) operand).name
                value = new BinaryExpression(operand, Token.newSymbol(op.type == Types.PLUS_PLUS ? Types.PLUS : Types.MINUS,
                    op.startLine, op.startColumn), new ConstantExpression(1, true))
            }
        }
        if (bound == null) return null
        Expression v = substitute(value, env)
        if (v == null || hasEffect(v)) return env
        Map<String, Expression> next = new HashMap<String, Expression>(env)
        next.put(bound, v)
        next
    }

    /**
     * Phase 355 — a helper's loop, summarised by its exit state: each variable the loop writes becomes a fresh name
     * (`$loopK$s`), and the facts at exit — every invariant and the negated guard, over those names — are added to
     * {@code ctx}, guarded by the path condition {@code pc}. The fold then continues after the loop.
     *
     * Sound because the helper's own loop verification proves the invariant established and preserved, and its
     * variant decreasing, for every input reaching the loop (a contract-free helper has no @Requires): so an exit
     * state exists and satisfies them. The VARIANT is required — without proven termination there may be no exit
     * state, and `¬guard` over a variable the loop doesn't write would contradict (a vacuous caller proof). A loop
     * the summary can't describe — one that breaks, returns or throws; writes anything but plain variables
     * (`a[i] = v`, `xs.add(v)`); calls a method on an object; nests a loop; or comes from `.each` — refuses (null),
     * and the call stays uninterpreted.
     */
    private static Map<String, Expression> foldLoop(LoopSpec spec, Map<String, Expression> env, FoldCtx ctx, Expression pc) {
        if (spec.variant == null || spec.fromEach || spec.forInBind != null || spec.guard == null) return null
        Map<String, Expression> cur = env
        for (Statement s0 : (spec.init ?: Collections.<Statement> emptyList())) {
            Map<String, Expression> nx = bindStatement(s0, cur)
            if (nx == null || nx.is(cur)) return null
            cur = nx
        }
        Set<String> declared = new HashSet<String>()
        Set<String> written = loopWrites(spec.body, declared)
        if (written == null || hasEffect(spec.guard)) return null
        written.removeAll(declared)   // body-locals die with the iteration
        int k = LOOP_SEQ.incrementAndGet()
        Map<String, Expression> exit = new HashMap<String, Expression>(cur)
        for (String w : written) {
            if (!cur.containsKey(w)) return null                     // a name the summary can't own (a field)
            ClassNode t = ctx.types.get(w)
            if (t == null || !(t.name in ['int', 'long', 'java.lang.Integer', 'java.lang.Long'])) return null
            exit.put(w, new VariableExpression('$loop' + k + '$' + w))
        }
        List<Expression> got = new ArrayList<Expression>()
        for (Expression inv : spec.invariants) {
            Expression f = pure(substitute(inv, exit))
            if (f != null) got.add(f)                                 // an invariant it can't carry is just left out
        }
        Expression g = pure(substitute(spec.guard, exit))
        if (g != null) got.add(new NotExpression(g instanceof BooleanExpression ? (BooleanExpression) g : new BooleanExpression(g)))
        for (Expression f : got) {
            ctx.facts.add(pc == null ? f : new BinaryExpression(new NotExpression(pc instanceof BooleanExpression ? (BooleanExpression) pc :
                new BooleanExpression(pc)), Token.newSymbol(Types.LOGICAL_OR, -1, -1), f))
        }
        exit
    }

    /** Phase 355 — the variables a loop body writes (declarations go to {@code declared}); null when it does anything
     *  the exit summary can't describe (see {@link #foldLoop}). */
    private static Set<String> loopWrites(List<Statement> body, Set<String> declared) {
        Set<String> out = new LinkedHashSet<String>()
        boolean[] bad = [false] as boolean[]
        org.codehaus.groovy.ast.CodeVisitorSupport v = new org.codehaus.groovy.ast.CodeVisitorSupport() {
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (de.leftExpression instanceof VariableExpression) declared.add(((VariableExpression) de.leftExpression).name)
                else bad[0] = true
                de.rightExpression.visit(this)
            }
            @Override void visitBinaryExpression(BinaryExpression be) {
                if (Types.ofType(be.operation.type, Types.ASSIGNMENT_OPERATOR)) {
                    if (be.leftExpression instanceof VariableExpression) out.add(((VariableExpression) be.leftExpression).name)
                    else bad[0] = true
                }
                super.visitBinaryExpression(be)
            }
            @Override void visitPostfixExpression(PostfixExpression pe) {
                if (pe.expression instanceof VariableExpression) out.add(((VariableExpression) pe.expression).name) else bad[0] = true
            }
            @Override void visitPrefixExpression(PrefixExpression pe) {
                if (pe.expression instanceof VariableExpression) out.add(((VariableExpression) pe.expression).name) else bad[0] = true
            }
            @Override void visitMethodCallExpression(MethodCallExpression mce) {
                Expression r = mce.objectExpression
                boolean ownOrStatic = mce.implicitThis || r instanceof ClassExpression ||
                    (r instanceof VariableExpression && ((VariableExpression) r).name == 'this')
                if (!ownOrStatic) bad[0] = true
                super.visitMethodCallExpression(mce)
            }
            @Override void visitClosureExpression(ClosureExpression ce) { bad[0] = true }
            @Override void visitBreakStatement(org.codehaus.groovy.ast.stmt.BreakStatement s) { bad[0] = true }
            @Override void visitReturnStatement(ReturnStatement s) { bad[0] = true }
            @Override void visitThrowStatement(org.codehaus.groovy.ast.stmt.ThrowStatement s) { bad[0] = true }
            @Override void visitWhileLoop(org.codehaus.groovy.ast.stmt.WhileStatement s) { bad[0] = true }
            @Override void visitDoWhileLoop(org.codehaus.groovy.ast.stmt.DoWhileStatement s) { bad[0] = true }
            @Override void visitForLoop(org.codehaus.groovy.ast.stmt.ForStatement s) { bad[0] = true }
            @Override void visitSwitch(org.codehaus.groovy.ast.stmt.SwitchStatement s) { bad[0] = true }
            @Override void visitTryCatchFinally(org.codehaus.groovy.ast.stmt.TryCatchStatement s) { bad[0] = true }
        }
        for (Statement st : body) st.visit(v)
        bad[0] ? null : out
    }

    /** {@code a && b}, with a null {@code a} read as true. */
    private static Expression conj(Expression a, Expression b) {
        a == null ? b : new BinaryExpression(a, Token.newSymbol(Types.LOGICAL_AND, -1, -1), b)
    }

    /** Phase 354 — the compound-assignment op type's base binary op, or -1 (`?=` and the rest aren't folded). */
    private static int compoundBase(int t) {
        switch (t) {
            case Types.PLUS_EQUAL: return Types.PLUS
            case Types.MINUS_EQUAL: return Types.MINUS
            case Types.MULTIPLY_EQUAL: return Types.MULTIPLY
            case Types.DIVIDE_EQUAL: return Types.DIVIDE
            case Types.INTDIV_EQUAL: return Types.INTDIV
            case Types.MOD_EQUAL: return Types.MOD
            case Types.REMAINDER_EQUAL: return Types.REMAINDER
            case Types.POWER_EQUAL: return Types.POWER
            case Types.LEFT_SHIFT_EQUAL: return Types.LEFT_SHIFT
            case Types.RIGHT_SHIFT_EQUAL: return Types.RIGHT_SHIFT
            case Types.RIGHT_SHIFT_UNSIGNED_EQUAL: return Types.RIGHT_SHIFT_UNSIGNED
            case Types.BITWISE_AND_EQUAL: return Types.BITWISE_AND
            case Types.BITWISE_OR_EQUAL: return Types.BITWISE_OR
            case Types.BITWISE_XOR_EQUAL: return Types.BITWISE_XOR
            default: return -1
        }
    }

    /** Phase 354 — {@code e}, or null when it still holds an assignment or an increment ({@code return n++},
     *  {@code (n = 5) + 1}): a folded value is a pure term, and such an expression's value isn't one. */
    private static Expression pure(Expression e) { e == null || hasEffect(e) ? null : e }

    private static boolean hasEffect(Expression e) {
        boolean[] hit = [false] as boolean[]
        e.visit(new org.codehaus.groovy.ast.CodeVisitorSupport() {
            @Override void visitBinaryExpression(BinaryExpression be) {
                if (Types.ofType(be.operation.type, Types.ASSIGNMENT_OPERATOR)) hit[0] = true
                super.visitBinaryExpression(be)
            }
            @Override void visitPostfixExpression(PostfixExpression pe) { hit[0] = true }
            @Override void visitPrefixExpression(PrefixExpression pe) { hit[0] = true }
            @Override void visitClosureExpression(ClosureExpression ce) { }   // a closure's own statements are its own
        })
        hit[0]
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
            // Phase 350 — a static on a SIBLING class of the compilation unit (`Util.tweak(x)`): its body is at hand,
            // so a contract-free function there unfolds like a same-class one, under a class-qualified symbol
            ClassNode sib = sce.ownerType != null ? siblingClass(sce.ownerType.name) : null
            if (sib != null) return pureCall(sib.nameWithoutPackage + '$' + sce.method, argsOf(sce.arguments))
            return null
        }
        if (e instanceof MethodCallExpression) {
            MethodCallExpression mce = (MethodCallExpression) e
            Expression recv = mce.objectExpression
            boolean sameClass = mce.implicitThis ||
                (recv instanceof VariableExpression && ((VariableExpression) recv).name == 'this') ||
                (recv instanceof ClassExpression && owner != null && recv.type?.name == owner.name)
            if (sameClass) return pureCall(mce.methodAsString, argList(mce))
            if (recv instanceof ClassExpression) {   // Phase 350 — `Util.tweak(x)` on a sibling class
                ClassNode sib = siblingClass(recv.type?.name)
                if (sib != null) return pureCall(sib.nameWithoutPackage + '$' + mce.methodAsString, argList(mce))
            }
            return null
        }
        return null
    }

    /** A {@link Call} only if {@code name}/arity resolves to a pure (contract-free) same-class method. */
    private Call pureCall(String name, List<Expression> args) {
        if (resolve(name, args.size()) == null) return null
        new Call(name: name, args: args)
    }

    /** Phase 350 — another class of the owner's compilation unit, by fully-qualified or simple name; null otherwise. */
    private ClassNode siblingClass(String n) {
        if (n == null || owner == null || owner.module == null || n == owner.name) return null
        for (ClassNode cn : owner.module.classes) {
            if (!cn.is(owner) && (cn.name == n || cn.nameWithoutPackage == n)) return cn
        }
        null
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
        ClassNode in = owner
        int q = name.indexOf('$')   // Phase 350 — `Util$tweak`: a sibling class's STATIC, found under its own name
        boolean sibling = false
        if (q > 0) {
            in = siblingClass(name.substring(0, q))
            if (in == null) return null
            name = name.substring(q + 1)
            sibling = true
        }
        for (MethodNode m : in.getMethods(name)) {
            if (sibling && !m.isStatic()) continue
            // A contracted method is the inter-procedural/induction path's territory (its @Ensures is
            // assumed, or its inductive hypothesis applied); evaluating or unfolding it here would steal
            // the call from that machinery, so treat only contract-free methods as pure functions.
            // Phase 347 — and only a method whose body writes nothing caller-visible is a FUNCTION: one that
            // assigns a field or stores into a parameter is framed at its call site instead (VerifyChecker.calleeWrites)
            if (m.parameters.length == arity) {
                if (hasContract(m)) return null
                Set<String> writes = VerifyChecker.calleeWrites(m)
                return (writes != null && writes.isEmpty()) ? m : null
            }
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
        if (--budget < 0) throw new NotEvaluable()
        // Phase 356 — loops run for real, bounded by the step budget (a budget exhausted is "not evaluable", and the
        // call falls back to the symbolic routes: the Phase 355 loop summary, or an uninterpreted function). An
        // annotated loop runs from its LoopSpec — the raw statement carries groovy-contracts' woven checks.
        Object spec = st.getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY)
        if (spec instanceof LoopSpec) { execSpecLoop((LoopSpec) spec, env); return }
        if (st instanceof org.codehaus.groovy.ast.stmt.WhileStatement) {
            org.codehaus.groovy.ast.stmt.WhileStatement ws = (org.codehaus.groovy.ast.stmt.WhileStatement) st
            while (evalBool(ws.booleanExpression, env)) { if (!iterate(ws.loopBlock, env)) break }
            return
        }
        if (st instanceof org.codehaus.groovy.ast.stmt.DoWhileStatement) {
            org.codehaus.groovy.ast.stmt.DoWhileStatement ds = (org.codehaus.groovy.ast.stmt.DoWhileStatement) st
            while (true) {
                if (!iterate(ds.loopBlock, env)) break
                if (!evalBool(ds.booleanExpression, env)) break
            }
            return
        }
        if (st instanceof org.codehaus.groovy.ast.stmt.ForStatement) { execFor((org.codehaus.groovy.ast.stmt.ForStatement) st, env); return }
        if (st instanceof org.codehaus.groovy.ast.stmt.BreakStatement) {
            if (((org.codehaus.groovy.ast.stmt.BreakStatement) st).label != null) throw new NotEvaluable()
            throw new BreakSignal()
        }
        if (st instanceof org.codehaus.groovy.ast.stmt.ContinueStatement) {
            if (((org.codehaus.groovy.ast.stmt.ContinueStatement) st).label != null) throw new NotEvaluable()
            throw new ContinueSignal()
        }
        if (st instanceof EmptyStatement) return
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
            if (execBinding(e, env)) return
            if (last) {
                throw new ReturnSignal(evalLong(e, env))   // Groovy implicit return
            }
        }
        throw new NotEvaluable()
    }

    /** A binding expression run for its effect on {@code env}: a declaration (`int r;` leaves {@code r} unbound, so a
     *  read before assignment is not evaluable), a plain or (Phase 356) compound assignment to a variable, or
     *  {@code x++} / {@code --x}. False when {@code e} is none of those. */
    private boolean execBinding(Expression e, Map<String, Long> env) {
        if (e instanceof DeclarationExpression && ((DeclarationExpression) e).rightExpression instanceof EmptyExpression) {
            if (!(((DeclarationExpression) e).leftExpression instanceof VariableExpression)) throw new NotEvaluable()
            env.remove(((VariableExpression) ((DeclarationExpression) e).leftExpression).name)
            return true
        }
        if (e instanceof BinaryExpression && ((BinaryExpression) e).leftExpression instanceof VariableExpression) {
            BinaryExpression be = (BinaryExpression) e
            String n = ((VariableExpression) be.leftExpression).name
            if (be.operation.type == Types.ASSIGN) { env.put(n, evalLong(be.rightExpression, env)); return true }
            int base = compoundBase(be.operation.type)
            if (base >= 0) {
                BinaryExpression comb = new BinaryExpression(be.leftExpression, Token.newSymbol(base, -1, -1), be.rightExpression)
                env.put(n, evalLong(comb, env))
                return true
            }
        }
        if (e instanceof PostfixExpression || e instanceof PrefixExpression) {
            Expression operand = e instanceof PostfixExpression ? ((PostfixExpression) e).expression : ((PrefixExpression) e).expression
            int t = (e instanceof PostfixExpression ? ((PostfixExpression) e).operation : ((PrefixExpression) e).operation).type
            if (operand instanceof VariableExpression && (t == Types.PLUS_PLUS || t == Types.MINUS_MINUS)) {
                String n = ((VariableExpression) operand).name
                env.put(n, evalLong(operand, env) + (t == Types.PLUS_PLUS ? 1L : -1L))
                return true
            }
        }
        false
    }

    /** Phase 356 — one iteration of a loop body: false when it broke out ({@code continue} just ends the iteration). */
    private boolean iterate(Statement body, Map<String, Long> env) {
        if (--budget < 0) throw new NotEvaluable()
        try {
            execBlock(body, env)
        } catch (ContinueSignal ignored) {
        } catch (BreakSignal ignored) {
            return false
        }
        true
    }

    /** Phase 356 — an annotated loop, from the specification CET captured: its init, then the guard and the body (a
     *  {@code for}'s update runs after a {@code continue} too, as in Java). A collection for-in and an {@code .each}
     *  aren't evaluated; a range for-in whose range would run backwards isn't either (the desugar models forwards). */
    private void execSpecLoop(LoopSpec spec, Map<String, Long> env) {
        if (spec.forInBind != null || spec.fromEach || spec.guard == null) throw new NotEvaluable()
        for (Statement s0 : (spec.init ?: Collections.<Statement> emptyList())) execStmt(s0, env, false)
        if (spec.rangeForward != null && !evalBool(spec.rangeForward, env)) throw new NotEvaluable()
        boolean first = spec.isDoWhile
        while (first || evalBool(spec.guard, env)) {
            first = false
            if (--budget < 0) throw new NotEvaluable()
            boolean broke = false
            try {
                for (Statement s : spec.body) {
                    if (spec.update != null && s.is(spec.update)) continue
                    execStmt(s, env, false)
                }
            } catch (ContinueSignal ignored) {
            } catch (BreakSignal ignored) {
                broke = true
            }
            if (broke) break
            if (spec.update != null) execStmt(spec.update, env, false)
        }
    }

    /** Phase 356 — an unannotated {@code for}: the classic {@code (init; cond; update)} form, or {@code for (x in lo..hi)}
     *  over a forwards range. */
    private void execFor(org.codehaus.groovy.ast.stmt.ForStatement fs, Map<String, Long> env) {
        Expression coll = fs.collectionExpression
        if (coll instanceof org.codehaus.groovy.ast.expr.ClosureListExpression) {
            List<Expression> parts = ((org.codehaus.groovy.ast.expr.ClosureListExpression) coll).expressions
            if (parts.size() != 3) throw new NotEvaluable()
            if (!(parts[0] instanceof EmptyExpression) && !execBinding(parts[0], env)) throw new NotEvaluable()
            while (parts[1] instanceof EmptyExpression || evalBool(parts[1], env)) {
                if (!iterate(fs.loopBlock, env)) break
                if (!(parts[2] instanceof EmptyExpression) && !execBinding(parts[2], env)) throw new NotEvaluable()
            }
            return
        }
        if (coll instanceof org.codehaus.groovy.ast.expr.RangeExpression && fs.variable != null &&
                fs.variable != org.codehaus.groovy.ast.stmt.ForStatement.FOR_LOOP_DUMMY) {
            org.codehaus.groovy.ast.expr.RangeExpression re = (org.codehaus.groovy.ast.expr.RangeExpression) coll
            if (re.exclusiveLeft) throw new NotEvaluable()
            long lo = evalLong(re.from, env)
            long hi = evalLong(re.to, env)
            if (re.exclusiveRight) hi = hi - 1
            if (lo > hi + (re.exclusiveRight ? 1L : 0L)) throw new NotEvaluable()   // a backwards range
            for (long v = lo; v <= hi; v++) {
                env.put(fs.variable.name, v)
                if (!iterate(fs.loopBlock, env)) break
            }
            return
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
        // Phase 356 — `n.intdiv(d)`: Groovy's integer division, truncating towards zero like Java's `/` on ints
        if (e instanceof MethodCallExpression && ((MethodCallExpression) e).methodAsString == 'intdiv' &&
                !((MethodCallExpression) e).implicitThis && argList((MethodCallExpression) e).size() == 1) {
            long l = evalLong(((MethodCallExpression) e).objectExpression, env)
            long r = evalLong(argList((MethodCallExpression) e).get(0), env)
            if (r == 0L) throw new NotEvaluable()
            return l.intdiv(r) as long
        }
        // Phase 356 — `Math.max` / `min` / `abs` on integers (the clamp idiom a helper's bounds use)
        if (e instanceof MethodCallExpression && ((MethodCallExpression) e).objectExpression instanceof ClassExpression &&
                ((MethodCallExpression) e).objectExpression.type?.name == 'java.lang.Math') {
            String mm = ((MethodCallExpression) e).methodAsString
            List<Expression> as = argList((MethodCallExpression) e)
            if ((mm == 'max' || mm == 'min') && as.size() == 2) {
                long a = evalLong(as.get(0), env), b = evalLong(as.get(1), env)
                return mm == 'max' ? Math.max(a, b) : Math.min(a, b)
            }
            if (mm == 'abs' && as.size() == 1) return Math.abs(evalLong(as.get(0), env))
            throw new NotEvaluable()
        }
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
            // Phase 356 — Groovy 6 parses `%` as REMAINDER (Phase 343): Java's remainder, sign of the dividend
            case Types.REMAINDER:                  if (r == 0L) throw new NotEvaluable(); return l % r
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

    /** Phase 356 — an unlabelled {@code break} / {@code continue}, caught by the innermost loop. */
    @CompileStatic
    private static class BreakSignal extends RuntimeException {
        BreakSignal() { super(null, null, false, false) }
    }

    @CompileStatic
    private static class ContinueSignal extends RuntimeException {
        ContinueSignal() { super(null, null, false, false) }
    }

    /** Raised when an expression/statement is outside the evaluable fragment. */
    @CompileStatic
    private static class NotEvaluable extends RuntimeException {
        NotEvaluable() { super(null, null, false, false) }
    }
}
