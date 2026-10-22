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
import org.codehaus.groovy.ast.ASTNode
import org.codehaus.groovy.ast.ClassHelper
import org.codehaus.groovy.ast.CodeVisitorSupport
import org.codehaus.groovy.ast.expr.ArgumentListExpression
import org.codehaus.groovy.ast.expr.BinaryExpression
import org.codehaus.groovy.ast.expr.BooleanExpression
import org.codehaus.groovy.ast.expr.CastExpression
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.DeclarationExpression
import org.codehaus.groovy.ast.expr.ElvisOperatorExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.NotExpression
import org.codehaus.groovy.ast.expr.PostfixExpression
import org.codehaus.groovy.ast.expr.PrefixExpression
import org.codehaus.groovy.ast.expr.TernaryExpression
import org.codehaus.groovy.ast.expr.TupleExpression
import org.codehaus.groovy.ast.expr.UnaryMinusExpression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.ast.stmt.AssertStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.IfStatement
import org.codehaus.groovy.ast.stmt.ReturnStatement
import org.codehaus.groovy.ast.stmt.Statement
import org.codehaus.groovy.syntax.Token
import org.codehaus.groovy.syntax.Types

import java.util.concurrent.atomic.AtomicInteger

/**
 * Phase 374 — a statement's evaluation, in order, as straight-line paths the replay runs exactly. A write inside an
 * expression (`(n = m) >= 0`, `b ? (d = 0) : 1`, `i++ + i`, `g(i++, i - 1)`) becomes its own assignment, where Java
 * evaluates it; a value read before a later write to what it reads is snapshotted first (`$eoN`); `&&`, `||`, a
 * ternary and an elvis branch into one path per way, each with its condition assumed. Lowered up to a site (its
 * {@code stop}), a path ends where the site is evaluated, and only the ways that reach it are kept.
 *
 * Used only for the witness search: the obligation is decided by the havocked check (Phase 373); a path here only
 * shows a call that gets there. Anything not modelled returns null, and no path is offered.
 */
@CompileStatic
class EvalOrder {

    /** The paths kept per expression, at most. */
    static final int CAP = 16

    private static final AtomicInteger TEMPS = new AtomicInteger()

    /** One way an expression evaluates: the writes before its value, its value, the names those writes write, and
     *  whether it stopped at the site. */
    static final class Lowered {
        final List<Statement> pre
        final Expression value
        final Set<String> writes
        final boolean reached
        Lowered(List<Statement> pre, Expression value, Set<String> writes, boolean reached) {
            this.pre = pre; this.value = value; this.writes = writes; this.reached = reached
        }
    }

    /**
     * The paths that run {@code st} — up to {@code stop} when it is inside (a site in its expression, or in its if's
     * branch, entered with the condition assumed). Null when a part isn't modelled.
     */
    static List<List<Statement>> lowerStatement(Statement st, ASTNode stop) {
        List<List<Statement>> out = new ArrayList<List<Statement>>()
        if (st instanceof ExpressionStatement) {
            Expression e = ((ExpressionStatement) st).expression
            if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.ASSIGN) {
                BinaryExpression be = (BinaryExpression) e
                List<Lowered> ls
                if (be.leftExpression instanceof VariableExpression) {
                    ls = lower(be.rightExpression, stop)
                    if (ls == null) return null
                    for (Lowered l : ls) {
                        if (l.reached) { out.add(l.pre); continue }
                        BinaryExpression nb = be instanceof DeclarationExpression ?
                            new DeclarationExpression((VariableExpression) be.leftExpression, be.operation, l.value) :
                            new BinaryExpression(be.leftExpression, be.operation, l.value)
                        out.add(plus(l.pre, stmt(nb, st)))
                    }
                    return out
                }
                if (be.leftExpression instanceof BinaryExpression &&
                    ((BinaryExpression) be.leftExpression).operation.type == Types.LEFT_SQUARE_BRACKET &&
                    ((BinaryExpression) be.leftExpression).leftExpression instanceof VariableExpression) {
                    // `a[idx] = value`: the index, then the value, then the store
                    BinaryExpression sub = (BinaryExpression) be.leftExpression
                    ls = sequence([sub.rightExpression, be.rightExpression], stop)
                    if (ls == null) return null
                    for (Lowered l : ls) {
                        if (l.reached) { out.add(l.pre); continue }
                        List<Expression> vs = ((TupleExpression) l.value).expressions
                        BinaryExpression store = new BinaryExpression(
                            new BinaryExpression(sub.leftExpression, sub.operation, vs.get(0)), be.operation, vs.get(1))
                        out.add(plus(l.pre, stmt(store, st)))
                    }
                    return out
                }
                return null
            }
            List<Lowered> ls = lower(e, stop)
            if (ls == null) return null
            for (Lowered l : ls) {
                if (l.reached || !(l.value instanceof MethodCallExpression)) out.add(l.pre)
                else out.add(plus(l.pre, stmt(l.value, st)))   // a call kept for what it does
            }
            return out
        }
        if (st instanceof IfStatement) {
            IfStatement ifs = (IfStatement) st
            List<Lowered> ls = lower(ifs.booleanExpression.expression, stop)
            if (ls == null) return null
            boolean inIf = stop != null && contains(ifs.ifBlock, stop)
            boolean inElse = stop != null && ifs.elseBlock != null && contains(ifs.elseBlock, stop)
            for (Lowered l : ls) {
                if (l.reached) out.add(l.pre)
                else if (inIf) out.add(plus(l.pre, assume(l.value)))
                else if (inElse) out.add(plus(l.pre, assume(new NotExpression(l.value))))
                else if (stop == null || !contains(st, stop)) {
                    IfStatement rebuilt = new IfStatement(new BooleanExpression(l.value), ifs.ifBlock, ifs.elseBlock)
                    rebuilt.setSourcePosition(ifs)
                    out.add(plus(l.pre, rebuilt))
                }
            }
            return out
        }
        if (st instanceof ReturnStatement && stop != null && contains(((ReturnStatement) st).expression, stop)) {
            List<Lowered> ls = lower(((ReturnStatement) st).expression, stop)
            if (ls == null) return null
            for (Lowered l : ls) if (l.reached) out.add(l.pre)
            return out
        }
        null
    }

    /** The ways {@code e} evaluates (up to {@code stop} when it is inside); null when a part isn't modelled. */
    static List<Lowered> lower(Expression e, ASTNode stop) {
        if (e == null) return null
        if (stop != null && e.is(stop)) {   // the site: its operands are evaluated, then it is checked
            List<Lowered> full = lower(e, null)
            if (full == null) return null
            return full.collect { Lowered l -> new Lowered(l.pre, l.value, l.writes, true) }
        }
        boolean inside = stop != null && contains(e, stop)
        if (!writes(e) && !inside) return [new Lowered(Collections.<Statement> emptyList(), e, Collections.<String> emptySet(), false)]
        if (!writes(e) && inside) {
            // nothing on the way writes: the site sees the state before the expression
            return [new Lowered(Collections.<Statement> emptyList(), e, Collections.<String> emptySet(), true)]
        }
        List<Lowered> out = lowerComposite(e, inside ? stop : null)
        if (out == null) return null
        if (inside) out = out.findAll { it.reached }
        out.size() > CAP ? new ArrayList<Lowered>(out.subList(0, CAP)) : out
    }

    private static List<Lowered> lowerComposite(Expression e, ASTNode stop) {
        if (e instanceof BinaryExpression && !(e instanceof DeclarationExpression)) {
            BinaryExpression be = (BinaryExpression) e
            int op = be.operation.type
            if (Types.ofType(op, Types.ASSIGNMENT_OPERATOR)) {
                if (!(be.leftExpression instanceof VariableExpression)) return null
                VariableExpression lhs = (VariableExpression) be.leftExpression
                Token arith = compoundArith(be.operation)
                if (op != Types.ASSIGN && arith == null) return null
                List<Lowered> rs = lower(be.rightExpression, stop)
                if (rs == null) return null
                List<Lowered> out = new ArrayList<Lowered>()
                for (Lowered r : rs) {
                    if (r.reached) { out.add(r); continue }
                    Expression v = op == Types.ASSIGN ? r.value : new BinaryExpression(lhs, arith, r.value)
                    out.add(new Lowered(plus(r.pre, assign(lhs.name, v, e)), lhs, plusName(r.writes, lhs.name), false))
                }
                return out
            }
            if (op == Types.LOGICAL_AND || op == Types.LOGICAL_OR) {
                boolean and = op == Types.LOGICAL_AND
                List<Lowered> ls = lower(be.leftExpression, stop)
                if (ls == null) return null
                List<Lowered> out = new ArrayList<Lowered>()
                for (Lowered l : ls) {
                    if (l.reached) { out.add(l); continue }
                    // the right operand runs when the left is true for &&, false for ||
                    Expression runs = and ? l.value : new NotExpression(l.value)
                    List<Lowered> rs = lower(be.rightExpression, stop)
                    if (rs == null) return null
                    for (Lowered r : rs) {
                        List<Statement> p = plus(plus(l.pre, assume(runs)), r.pre)
                        out.add(new Lowered(p, r.value, union(l.writes, r.writes), r.reached))
                    }
                    Expression skips = and ? new NotExpression(l.value) : l.value
                    out.add(new Lowered(plus(l.pre, assume(skips)), and ? ConstantExpression.PRIM_FALSE : ConstantExpression.PRIM_TRUE,
                        l.writes, false))
                }
                return out
            }
            List<Lowered> ls = sequence([be.leftExpression, be.rightExpression], stop)
            if (ls == null) return null
            return ls.collect { Lowered l ->
                if (l.reached) return l
                List<Expression> vs = ((TupleExpression) l.value).expressions
                new Lowered(l.pre, (Expression) new BinaryExpression(vs.get(0), be.operation, vs.get(1)), l.writes, false)
            }
        }
        if (e instanceof ElvisOperatorExpression) {
            ElvisOperatorExpression el = (ElvisOperatorExpression) e
            List<Lowered> ls = lower(el.trueExpression, stop)
            if (ls == null) return null
            List<Lowered> out = new ArrayList<Lowered>()
            for (Lowered l : ls) {
                if (l.reached) { out.add(l); continue }
                out.add(new Lowered(plus(l.pre, assume(l.value)), l.value, l.writes, false))
                List<Lowered> fs = lower(el.falseExpression, stop)
                if (fs == null) return null
                for (Lowered f : fs) {
                    out.add(new Lowered(plus(plus(l.pre, assume(new NotExpression(l.value))), f.pre), f.value,
                        union(l.writes, f.writes), f.reached))
                }
            }
            return out
        }
        if (e instanceof TernaryExpression) {
            TernaryExpression te = (TernaryExpression) e
            List<Lowered> cs = lower(te.booleanExpression.expression, stop)
            if (cs == null) return null
            List<Lowered> out = new ArrayList<Lowered>()
            for (Lowered c : cs) {
                if (c.reached) { out.add(c); continue }
                for (int arm = 0; arm < 2; arm++) {
                    Expression cond = arm == 0 ? c.value : new NotExpression(c.value)
                    List<Lowered> bs = lower(arm == 0 ? te.trueExpression : te.falseExpression, stop)
                    if (bs == null) return null
                    for (Lowered b : bs) {
                        out.add(new Lowered(plus(plus(c.pre, assume(cond)), b.pre), b.value, union(c.writes, b.writes), b.reached))
                    }
                }
            }
            return out
        }
        if (e instanceof PostfixExpression || e instanceof PrefixExpression) {
            Expression target = e instanceof PostfixExpression ? ((PostfixExpression) e).expression : ((PrefixExpression) e).expression
            Token op = e instanceof PostfixExpression ? ((PostfixExpression) e).operation : ((PrefixExpression) e).operation
            if (!(target instanceof VariableExpression)) return null
            if (op.type != Types.PLUS_PLUS && op.type != Types.MINUS_MINUS) return null
            String n = ((VariableExpression) target).name
            Token arith = Token.newSymbol(op.type == Types.PLUS_PLUS ? Types.PLUS : Types.MINUS, -1, -1)
            Statement step = assign(n, new BinaryExpression(target, arith, new ConstantExpression(1, true)), e)
            if (e instanceof PrefixExpression) {
                return [new Lowered([step] as List<Statement>, target, [n] as Set<String>, false)]
            }
            String tmp = temp()
            return [new Lowered([assign(tmp, target, e), step] as List<Statement>, (Expression) new VariableExpression(tmp),
                [n, tmp] as Set<String>, false)]
        }
        if (e instanceof NotExpression || e instanceof BooleanExpression || e instanceof UnaryMinusExpression ||
            e instanceof CastExpression) {
            Expression inner = e instanceof NotExpression ? ((NotExpression) e).expression :
                e instanceof BooleanExpression ? ((BooleanExpression) e).expression :
                e instanceof UnaryMinusExpression ? ((UnaryMinusExpression) e).expression : ((CastExpression) e).expression
            List<Lowered> ls = lower(inner, stop)
            if (ls == null) return null
            return ls.collect { Lowered l ->
                if (l.reached) return l
                Expression v = e instanceof NotExpression ? new NotExpression(l.value) :
                    e instanceof BooleanExpression ? new BooleanExpression(l.value) :
                    e instanceof UnaryMinusExpression ? new UnaryMinusExpression(l.value) :
                    (Expression) new CastExpression(((CastExpression) e).type, l.value)
                new Lowered(l.pre, v, l.writes, false)
            }
        }
        if (e instanceof MethodCallExpression) {
            MethodCallExpression mce = (MethodCallExpression) e
            if (Encoder.isCallableCall(mce) || !(mce.arguments instanceof ArgumentListExpression)) return null
            List<Expression> parts = new ArrayList<Expression>()
            parts.add(mce.objectExpression)
            parts.addAll(((ArgumentListExpression) mce.arguments).expressions)
            List<Lowered> ls = sequence(parts, stop)
            if (ls == null) return null
            return ls.collect { Lowered l ->
                if (l.reached) return l
                List<Expression> vs = ((TupleExpression) l.value).expressions
                MethodCallExpression c = new MethodCallExpression(vs.get(0), mce.method,
                    new ArgumentListExpression(vs.subList(1, vs.size())))
                c.implicitThis = mce.implicitThis
                c.safe = mce.safe
                c.spreadSafe = mce.spreadSafe
                c.methodTarget = mce.methodTarget
                c.copyNodeMetaData(mce)
                c.setSourcePosition(mce)
                new Lowered(l.pre, (Expression) c, l.writes, false)
            }
        }
        null
    }

    /** {@code parts} evaluated left to right: one way per combination, its value a tuple of theirs. A value read before
     *  a later part writes what it reads is snapshotted into a temp first. */
    private static List<Lowered> sequence(List<Expression> parts, ASTNode stop) {
        List<Lowered> acc = [new Lowered(Collections.<Statement> emptyList(), (Expression) new TupleExpression(),
            Collections.<String> emptySet(), false)]
        for (Expression part : parts) {
            List<Lowered> ps = lower(part, stop)
            if (ps == null) return null
            List<Lowered> next = new ArrayList<Lowered>()
            for (Lowered a : acc) {
                if (a.reached) { next.add(a); continue }
                for (Lowered p : ps) {
                    List<Expression> vs = new ArrayList<Expression>(((TupleExpression) a.value).expressions)
                    List<Statement> pre = new ArrayList<Statement>(a.pre)
                    Set<String> ws = union(a.writes, p.writes)
                    if (!p.writes.isEmpty()) {
                        for (int k = 0; k < vs.size(); k++) {
                            if (!namesRead(vs.get(k)).any { p.writes.contains(it) }) continue
                            String tmp = temp()
                            pre.add(assign(tmp, vs.get(k), part))
                            vs.set(k, new VariableExpression(tmp))
                        }
                    }
                    pre.addAll(p.pre)
                    vs.add(p.value)
                    next.add(new Lowered(pre, (Expression) new TupleExpression(vs), ws, p.reached))
                    if (next.size() >= CAP) break
                }
            }
            acc = next
        }
        acc
    }

    /** Does {@code e} write (an assignment, `++`/`--`) or hold a closure, which isn't evaluated in place? */
    static boolean writes(Expression e) {
        boolean[] found = [false]
        e.visit(new CodeVisitorSupport() {
            @Override void visitBinaryExpression(BinaryExpression be) {
                if (Types.ofType(be.operation.type, Types.ASSIGNMENT_OPERATOR)) found[0] = true
                super.visitBinaryExpression(be)
            }
            @Override void visitPostfixExpression(PostfixExpression pe) { found[0] = true }
            @Override void visitPrefixExpression(PrefixExpression pe) { found[0] = true }
            @Override void visitClosureExpression(ClosureExpression ce) { found[0] = true }
        })
        found[0]
    }

    /** Is {@code inner} the node {@code outer}, or inside its source range (both ends)? */
    static boolean contains(ASTNode outer, ASTNode inner) {
        if (outer == null || inner == null) return false
        if (outer.is(inner)) return true
        if (inner.lineNumber < 0 || outer.lineNumber < 0 || inner.lastLineNumber < 0 || outer.lastLineNumber < 0) return false
        boolean startIn = inner.lineNumber > outer.lineNumber ||
            (inner.lineNumber == outer.lineNumber && inner.columnNumber >= outer.columnNumber)
        boolean endIn = inner.lastLineNumber < outer.lastLineNumber ||
            (inner.lastLineNumber == outer.lastLineNumber && inner.lastColumnNumber <= outer.lastColumnNumber)
        startIn && endIn
    }

    /** An assume marker (Phase 311's, which the exact replay asserts in full). A value that isn't a condition (an
     *  elvis operand, `xs` in `xs && …`) is assumed by its Groovy truth, `(v as boolean)`. */
    static Statement assume(Expression cond) {
        if (!isCondition(cond)) cond = new CastExpression(ClassHelper.boolean_TYPE, cond)
        AssertStatement marker = new AssertStatement(new BooleanExpression(cond))
        marker.putNodeMetaData(VerifyChecker.REPLAY_ASSUME_KEY, Boolean.TRUE)
        marker
    }

    private static boolean isCondition(Expression e) {
        if (e instanceof NotExpression || e instanceof BooleanExpression) return true
        if (e instanceof ConstantExpression) return ((ConstantExpression) e).value instanceof Boolean
        if (e instanceof BinaryExpression) {
            int op = ((BinaryExpression) e).operation.type
            return op == Types.LOGICAL_AND || op == Types.LOGICAL_OR || Types.ofType(op, Types.COMPARISON_OPERATOR) ||
                op == Types.KEYWORD_INSTANCEOF || op == Types.KEYWORD_IN
        }
        ClassHelper.boolean_TYPE == e.type || ClassHelper.Boolean_TYPE == e.type
    }

    private static Statement assign(String name, Expression value, ASTNode at) {
        Token tok = Token.newSymbol(Types.ASSIGN, at.lineNumber, at.columnNumber)
        stmt(new BinaryExpression(new VariableExpression(name), tok, value), at)
    }

    private static Statement stmt(Expression e, ASTNode at) {
        Statement s = new ExpressionStatement(e)
        s.setSourcePosition(at)
        s
    }

    private static String temp() { '$eo' + TEMPS.incrementAndGet() }

    private static Token compoundArith(Token op) {
        int t = op.type == Types.PLUS_EQUAL ? Types.PLUS : op.type == Types.MINUS_EQUAL ? Types.MINUS :
            op.type == Types.MULTIPLY_EQUAL ? Types.MULTIPLY : -1
        t < 0 ? null : Token.newSymbol(t, op.startLine, op.startColumn)
    }

    private static Set<String> namesRead(Expression e) {
        Set<String> out = new HashSet<String>()
        e.visit(new CodeVisitorSupport() {
            @Override void visitVariableExpression(VariableExpression ve) { out.add(ve.name) }
        })
        out
    }

    private static List<Statement> plus(List<Statement> a, Statement s) {
        List<Statement> out = new ArrayList<Statement>(a)
        out.add(s)
        out
    }

    private static List<Statement> plus(List<Statement> a, List<Statement> b) {
        List<Statement> out = new ArrayList<Statement>(a)
        out.addAll(b)
        out
    }

    private static Set<String> plusName(Set<String> a, String n) {
        Set<String> out = new LinkedHashSet<String>(a)
        out.add(n)
        out
    }

    private static Set<String> union(Set<String> a, Set<String> b) {
        Set<String> out = new LinkedHashSet<String>(a)
        out.addAll(b)
        out
    }
}
