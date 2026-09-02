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
import static verification.VerifyChecker.CHANNEL_DRAIN_OPS
import static verification.VerifyChecker.bin
import static verification.VerifyChecker.CLAIM_SELECT
import static verification.VerifyChecker.boundsAssert
import static verification.VerifyChecker.collectBodyLocalNames
import static verification.VerifyChecker.isNonIntScalar
import static verification.VerifyChecker.noArgs
import static verification.VerifyChecker.stripCasts
import org.codehaus.groovy.ast.AnnotationNode
import org.codehaus.groovy.ast.ASTNode
import org.codehaus.groovy.ast.ConstructorNode
import org.codehaus.groovy.ast.ClassCodeVisitorSupport
import org.codehaus.groovy.ast.ClassHelper
import org.codehaus.groovy.ast.GenericsType
import org.codehaus.groovy.ast.tools.GenericsUtils
import org.codehaus.groovy.ast.ClassNode
import org.codehaus.groovy.transform.stc.StaticTypesMarker
import org.codehaus.groovy.ast.FieldNode
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.Parameter
import org.codehaus.groovy.ast.CodeVisitorSupport
import org.codehaus.groovy.ast.Variable
import org.codehaus.groovy.ast.VariableScope
import org.codehaus.groovy.ast.builder.AstBuilder
import org.codehaus.groovy.ast.expr.AnnotationConstantExpression
import org.codehaus.groovy.ast.expr.ArgumentListExpression
import org.codehaus.groovy.ast.expr.BinaryExpression
import org.codehaus.groovy.ast.expr.BooleanExpression
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.expr.ClosureListExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.ConstructorCallExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.ListExpression
import org.codehaus.groovy.ast.expr.MethodCall
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.NotExpression
import org.codehaus.groovy.ast.expr.PropertyExpression
import org.codehaus.groovy.ast.expr.RangeExpression
import org.codehaus.groovy.ast.expr.PostfixExpression
import org.codehaus.groovy.ast.expr.PrefixExpression
import org.codehaus.groovy.ast.expr.ClassExpression
import org.codehaus.groovy.ast.expr.CastExpression
import groovyjarjarasm.asm.Opcodes
import org.codehaus.groovy.ast.expr.StaticMethodCallExpression
import org.codehaus.groovy.ast.expr.DeclarationExpression
import org.codehaus.groovy.ast.expr.ExpressionTransformer
import org.codehaus.groovy.ast.expr.TernaryExpression
import org.codehaus.groovy.ast.expr.UnaryMinusExpression
import org.codehaus.groovy.ast.expr.TupleExpression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.AssertStatement
import org.codehaus.groovy.ast.stmt.DoWhileStatement
import org.codehaus.groovy.ast.stmt.EmptyStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.ForStatement
import org.codehaus.groovy.ast.stmt.IfStatement
import org.codehaus.groovy.ast.stmt.LoopingStatement
import org.codehaus.groovy.ast.stmt.ReturnStatement
import org.codehaus.groovy.ast.stmt.Statement
import org.codehaus.groovy.ast.stmt.ThrowStatement
import org.codehaus.groovy.ast.stmt.WhileStatement
import org.codehaus.groovy.ast.stmt.TryCatchStatement
import org.codehaus.groovy.ast.stmt.CatchStatement
import org.codehaus.groovy.control.CompilePhase
import org.codehaus.groovy.control.SourceUnit
import org.codehaus.groovy.syntax.Token
import org.codehaus.groovy.syntax.Types
import org.codehaus.groovy.transform.stc.StaticTypeCheckingVisitor
import org.codehaus.groovy.transform.stc.TypeCheckingExtension
/**
 * The channel/dataflow DESUGARING half of the checker, split out of {@link VerifyChecker} (which was a
 * single 15.5k-line class). Everything here is static AST-to-AST rewriting — dataflow variables, the
 * async-channel pipeline, symbolic and bounded streaming, and the guarded ALT's index — with no dependence
 * on the checker's mutable per-method state, which is why it separates cleanly. The verdict-reporting
 * passes that consume these rewrites stay in VerifyChecker.
 *
 * <p>Split for two reasons. It is easier to navigate and to edit correctly: several near-identical
 * `List&lt;ChanUse&gt; uses = ctx.chanUses` gates live in this file's former neighbours, and edits have gone
 * to the wrong one. And the Groovy compiler's per-class cost grows with the distinct type pairs inside one
 * class, so a 15.5k-line class needed materially more heap than the same code split in two.
 */
@CompileStatic
class ChannelDesugar {
    // ── Phase 118 — dataflow desugaring ─────────────────────────────────────────────────────────
    /** Rewrite a body using `DataflowVariable`/`<<`/`await`/`async` into plain single-assignment code; returns
     *  the same body unchanged if it uses none of them. */
    static Statement desugarDataflow(Statement body) {
        if (!(body instanceof BlockStatement)) return body
        Set<String> df = new HashSet<String>()
        collectDataflowVars((BlockStatement) body, df)
        if (df.isEmpty()) return body
        List<Statement> out = new ArrayList<Statement>()
        rewriteDfStatements(((BlockStatement) body).statements, df, out)
        new BlockStatement(out, ((BlockStatement) body).variableScope)
    }

    static void collectDataflowVars(BlockStatement body, Set<String> df) {
        body.visit(new CodeVisitorSupport() {
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (de.leftExpression instanceof VariableExpression && isDataflowNew(de.rightExpression)) {
                    df.add(((VariableExpression) de.leftExpression).name)
                }
                super.visitDeclarationExpression(de)
            }
        })
    }

    static boolean isDataflowNew(Expression e) {
        if (!(e instanceof ConstructorCallExpression)) return false
        String n = ((ConstructorCallExpression) e).type?.nameWithoutPackage
        n == 'DataflowVariable' || n == 'Dataflows'
    }

    static boolean isDfVarRef(Expression e, Set<String> df) {
        e instanceof VariableExpression && df.contains(((VariableExpression) e).name)
    }

    /** The single closure argument of an `async { … }` call (MethodCall or static), else null. */
    static ClosureExpression asyncClosure(Expression e) {
        Expression argsExpr = null
        if (e instanceof MethodCallExpression && ((MethodCallExpression) e).methodAsString == 'async') {
            argsExpr = ((MethodCallExpression) e).arguments
        } else if (e instanceof StaticMethodCallExpression && ((StaticMethodCallExpression) e).method == 'async') {
            argsExpr = ((StaticMethodCallExpression) e).arguments
        }
        if (!(argsExpr instanceof ArgumentListExpression)) return null
        List<Expression> a = ((ArgumentListExpression) argsExpr).expressions
        (a.size() == 1 && a.get(0) instanceof ClosureExpression) ? (ClosureExpression) a.get(0) : null
    }

    static void rewriteDfStatements(List<Statement> stmts, Set<String> df, List<Statement> out) {
        for (Statement st : stmts) {
            if (st instanceof BlockStatement) { rewriteDfStatements(((BlockStatement) st).statements, df, out); continue }
            if (st instanceof ExpressionStatement) {
                Expression e = ((ExpressionStatement) st).expression
                ClosureExpression cl = asyncClosure(e)               // async { … } → flatten inline (transparent)
                if (cl != null) {
                    if (cl.code instanceof BlockStatement) rewriteDfStatements(((BlockStatement) cl.code).statements, df, out)
                    continue
                }
                if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.LEFT_SHIFT &&
                    isDfVarRef(((BinaryExpression) e).leftExpression, df)) {           // x << v → x = v
                    BinaryExpression be = (BinaryExpression) e
                    out.add(new ExpressionStatement(bin(be.leftExpression, Types.ASSIGN, rewriteDfExpr(be.rightExpression, df))))
                    continue
                }
                if (e instanceof DeclarationExpression && isDataflowNew(((DeclarationExpression) e).rightExpression) &&
                    ((DeclarationExpression) e).leftExpression instanceof VariableExpression) {
                    // def x = new DataflowVariable() → def x = 0 (a fresh dynamic local; the bind reassigns it)
                    DeclarationExpression de = (DeclarationExpression) e
                    VariableExpression lhs = new VariableExpression(((VariableExpression) de.leftExpression).name)
                    out.add(new ExpressionStatement(new DeclarationExpression(lhs, de.operation, new ConstantExpression(Integer.valueOf(0)))))
                    continue
                }
                out.add(new ExpressionStatement(rewriteDfExpr(e, df)))
                continue
            }
            if (st instanceof ReturnStatement) {
                Expression r = ((ReturnStatement) st).expression
                out.add(new ReturnStatement(r == null ? r : rewriteDfExpr(r, df)))
                continue
            }
            out.add(st)
        }
    }

    /** Rewrite `await(x)` / `x.get()` / `x.val` (x a dataflow var) to `x`, recursively. */
    static Expression rewriteDfExpr(Expression e, Set<String> df) {
        if (e == null) return e
        ExpressionTransformer t = new ExpressionTransformer() {
            @Override Expression transform(Expression expr) {
                if (expr instanceof MethodCallExpression) {
                    MethodCallExpression m = (MethodCallExpression) expr
                    if (m.methodAsString == 'await') {
                        List<Expression> a = (m.arguments instanceof ArgumentListExpression) ?
                            ((ArgumentListExpression) m.arguments).expressions : null
                        if (a != null && a.size() == 1 && isDfVarRef(a.get(0), df)) return a.get(0)
                    }
                    if (m.methodAsString == 'get' && isDfVarRef(m.objectExpression, df) &&
                        (!(m.arguments instanceof ArgumentListExpression) || ((ArgumentListExpression) m.arguments).expressions.isEmpty())) {
                        return m.objectExpression
                    }
                } else if (expr instanceof StaticMethodCallExpression) {
                    StaticMethodCallExpression m = (StaticMethodCallExpression) expr
                    if (m.method == 'await' && m.arguments instanceof ArgumentListExpression) {
                        List<Expression> a = ((ArgumentListExpression) m.arguments).expressions
                        if (a.size() == 1 && isDfVarRef(a.get(0), df)) return a.get(0)
                    }
                } else if (expr instanceof PropertyExpression) {
                    PropertyExpression pe = (PropertyExpression) expr
                    if (pe.propertyAsString == 'val' && isDfVarRef(pe.objectExpression, df)) return pe.objectExpression
                }
                expr.transformExpression(this)
            }
        }
        t.transform(e)
    }


    // ── Phase 275 — the GUARDED ALT's index, independent of the stream model ──────────────────────
    /**
     * Bind {@code r.index} for a MASKED select (GROOVY-12324's {@code select(boolean... enabled)}).
     *
     * <p>The stream machinery cannot carry this one. {@code rewriteChStatements} does not descend into
     * {@code while} bodies, and {@link #loopingAlt} is gated on a {@code ConsumerInfo} built from per-branch
     * streams — but the shape c05 is written in is a SERVER loop whose branches have no statically known
     * producers at all, and whose invariant is about a local counter rather than about values. So the index
     * is bound here instead, by a plain body-wide desugaring that needs no channel model:
     *
     * <pre>
     *   ChannelSelect.Result r = await alt.select(counter &lt; cap, counter &gt; 0)
     *     ⇒  def r$index = $channelSelect.guarded(0, counter &lt; cap, 1, counter &gt; 0)
     *   r.index  ⇒  r$index
     * </pre>
     *
     * The declaration stays where it was — inside the loop body — so the flags are re-translated each
     * iteration against that iteration's bindings, which is the whole point of a guard. The Encoder reads
     * the marker as "the committed index is one whose flag holds", and the existing if/else ITE machinery
     * then carries the arms. Fires ONLY on a select that actually carries flags, so an unmasked ALT keeps
     * the stream model's richer treatment (values included) untouched.
     */
    static Statement desugarGuardedSelects(Statement body) {
        if (!(body instanceof BlockStatement)) return body
        Map<String, List<Expression>> guards = new LinkedHashMap<String, List<Expression>>()   // select var → per-offer guards
        collectHeldOfferGuards(body, guards)
        Map<String, String> bound = new LinkedHashMap<String, String>()          // result var → its $index var
        collectMaskedSelects(body, bound, guards)
        if (bound.isEmpty()) return body
        return rewriteGuardedStmt(body, bound, guards)
    }

    /** Phase 276 — select instances whose OFFERS carry guards, so a held `alt` declared outside the loop
     *  still tells the loop body what each branch is guarded by. */
    static void collectHeldOfferGuards(Statement body, Map<String, List<Expression>> out) {
        body.visit(new CodeVisitorSupport() {
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (de.leftExpression instanceof VariableExpression) {
                    List<Expression> g = selectOfferGuards(de.rightExpression)
                    if (g != null) out.put(((VariableExpression) de.leftExpression).name, g)
                }
                super.visitDeclarationExpression(de)
            }
        })
    }

    /** Result vars declared by an awaited select that is guarded at all — by positional flags
     *  (GROOVY-12324) or per-offer (GROOVY-12326), the two spellings of the same thing. */
    static void collectMaskedSelects(Statement body, Map<String, String> out, Map<String, List<Expression>> guards) {
        body.visit(new CodeVisitorSupport() {
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (de.leftExpression instanceof VariableExpression &&
                    guardedSelectArity(de.rightExpression, guards) > 0) {
                    String n = ((VariableExpression) de.leftExpression).name
                    out.put(n, n + '$index')
                }
                super.visitDeclarationExpression(de)
            }
        })
    }

    /** The branch count of an awaited GUARDED select, or 0 when it carries no guard of either kind. */
    static int guardedSelectArity(Expression rhs, Map<String, List<Expression>> guards) {
        List<Expression> mask = awaitedSelectMask(rhs)
        if (mask != null && !mask.isEmpty()) return mask.size()
        List<Expression> og = offerGuardsFor(rhs, guards)
        og == null ? 0 : og.size()
    }

    /** The per-offer guards behind an awaited select — through a held instance, or inline. */
    static List<Expression> offerGuardsFor(Expression rhs, Map<String, List<Expression>> guards) {
        MethodCallExpression sel = awaitedSelectCall(rhs)
        if (sel == null) return null
        Expression recv = stripCasts(sel.objectExpression)
        if (recv instanceof VariableExpression) return guards == null ? null : guards.get(((VariableExpression) recv).name)
        selectOfferGuards(recv)
    }

    /** `r.index` / `r.getIndex()` → `r$index`, for the result vars bound above. */
    static Expression rewriteGuardedExpr(Expression e, Map<String, String> bound) {
        if (e == null) return null
        ExpressionTransformer t = new ExpressionTransformer() {
            @Override Expression transform(Expression expr) {
                if (expr instanceof PropertyExpression) {
                    PropertyExpression pe = (PropertyExpression) expr
                    Expression o = stripCasts(pe.objectExpression)
                    if (o instanceof VariableExpression && bound.containsKey(((VariableExpression) o).name) &&
                        pe.propertyAsString == 'index') return new VariableExpression(bound.get(((VariableExpression) o).name))
                }
                if (expr instanceof MethodCallExpression) {
                    MethodCallExpression m = (MethodCallExpression) expr
                    Expression o = stripCasts(m.objectExpression)
                    if (o instanceof VariableExpression && bound.containsKey(((VariableExpression) o).name) &&
                        m.methodAsString == 'getIndex' && noArgs(m)) return new VariableExpression(bound.get(((VariableExpression) o).name))
                }
                expr.transformExpression(this)
            }
        }
        t.transform(e)
    }

    /** Phase 276 — GROOVY-12326's offer-level guard. The arguments of `ChannelSelect.offers(...)`, else null. */
    static List<Expression> selectOffersArgs(Expression e) {
        Expression x = stripCasts(e)
        Expression args = null
        if (x instanceof StaticMethodCallExpression) {
            StaticMethodCallExpression sm = (StaticMethodCallExpression) x
            if (sm.method == 'offers' && sm.ownerType?.nameWithoutPackage == 'ChannelSelect') args = sm.arguments
        } else if (x instanceof MethodCallExpression) {
            MethodCallExpression m = (MethodCallExpression) x
            if (m.methodAsString == 'offers' && channelOwnerName(m.objectExpression) == 'ChannelSelect') args = m.arguments
        }
        (args instanceof TupleExpression) ? ((TupleExpression) args).expressions : null
    }

    /** The single expression a `{ … }` guard closure evaluates to, else null (a block guard is unmodelled). */
    static Expression guardClosureBody(Expression e) {
        Expression x = stripCasts(e)
        if (!(x instanceof ClosureExpression)) return null
        Statement code = ((ClosureExpression) x).code
        if (code instanceof BlockStatement) {
            List<Statement> ss = ((BlockStatement) code).statements
            if (ss.size() != 1) return null
            code = ss.get(0)
        }
        if (code instanceof ExpressionStatement) return ((ExpressionStatement) code).expression
        if (code instanceof ReturnStatement) return ((ReturnStatement) code).expression
        null
    }

    /** Phase 280 — the channel an offer names: `receive(c)` or `send(c, v)`, through any `.when { … }`
     *  wrappers. Null when the offer is not one of those two shapes. */
    static Expression offerChannelOf(Expression offer) {
        Expression x = stripCasts(offer)
        while (x instanceof MethodCallExpression && ((MethodCallExpression) x).methodAsString == 'when') {
            x = stripCasts(((MethodCallExpression) x).objectExpression)
        }
        // RECEIVE offers only. A `send(c, v)` offer is an OUTPUT guard: the select's branch list is read
        // downstream as the channels it consumes, so counting a send there makes two peers of a mixed
        // choice look like two receivers on one channel — a linearity violation that is not there. The
        // racing mixed choice stays the session layer's business (Phase 271), where it already is.
        Expression args = null
        if (x instanceof StaticMethodCallExpression) {
            StaticMethodCallExpression sm = (StaticMethodCallExpression) x
            if (sm.method == 'receive' && sm.ownerType?.nameWithoutPackage == 'ChannelSelect') args = sm.arguments
        } else if (x instanceof MethodCallExpression) {
            MethodCallExpression m = (MethodCallExpression) x
            if (m.methodAsString == 'receive' && channelOwnerName(m.objectExpression) == 'ChannelSelect') args = m.arguments
        }
        if (!(args instanceof TupleExpression)) return null
        List<Expression> a = ((TupleExpression) args).expressions
        a.isEmpty() ? null : a.get(0)
    }

    /** One offer's conjoined guard — `receive(c).when { a }.when { b }` is `a && b` — else null when unguarded.
     *  A `when` whose argument is not a single-expression closure yields null too, and the caller then treats
     *  the offer as unmodelled rather than as unguarded (silently dropping a guard would be unsound). */
    static Expression offerGuardOf(Expression offer, boolean[] unmodelled) {
        Expression x = stripCasts(offer)
        List<Expression> gs = new ArrayList<Expression>()
        while (x instanceof MethodCallExpression && ((MethodCallExpression) x).methodAsString == 'when') {
            MethodCallExpression m = (MethodCallExpression) x
            List<Expression> a = (m.arguments instanceof TupleExpression) ? ((TupleExpression) m.arguments).expressions : null
            if (a == null || a.size() != 1) { unmodelled[0] = true; return null }
            Expression body = guardClosureBody(a.get(0))
            if (body == null) { unmodelled[0] = true; return null }
            gs.add(0, body)
            x = stripCasts(m.objectExpression)
        }
        if (gs.isEmpty()) return null
        Expression conj = gs.get(0)
        for (int i = 1; i < gs.size(); i++) {
            conj = new BinaryExpression(conj, Token.newSymbol(Types.LOGICAL_AND, -1, -1), gs.get(i))
        }
        conj
    }

    /** Per-offer guards of a select expression, positionally; null when it is not an `offers(...)` select or
     *  carries a guard outside the fragment. Entries are null for unguarded offers. */
    static List<Expression> selectOfferGuards(Expression selectExpr) {
        Expression x = stripCasts(selectExpr)
        while (x instanceof MethodCallExpression &&
               (((MethodCallExpression) x).methodAsString == 'fair' || ((MethodCallExpression) x).methodAsString == 'random') &&
               noArgs((MethodCallExpression) x)) {
            x = stripCasts(((MethodCallExpression) x).objectExpression)
        }
        List<Expression> offers = selectOffersArgs(x)
        if (offers == null) return null
        boolean[] bad = new boolean[1]
        List<Expression> out = new ArrayList<Expression>()
        for (Expression o : offers) out.add(offerGuardOf(o, bad))
        if (bad[0]) return null
        boolean any = false
        for (Expression g : out) if (g != null) any = true
        any ? out : null
    }

    /** Phase 275 — carry a loop's spec across the rewrite, over the rewritten statements. */
    static void rebindLoopSpec(Statement from, Statement to, Map<String, String> bound, Map<String, List<Expression>> guards) {
        Object o = from.getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY)
        if (!(o instanceof LoopSpec)) return
        LoopSpec sp = (LoopSpec) o, ns = new LoopSpec()
        ns.invariants = sp.invariants.collect { Expression e -> rewriteGuardedExpr(e, bound) }
        ns.variant = sp.variant == null ? null : rewriteGuardedExpr(sp.variant, bound)
        ns.guard = sp.guard == null ? null : rewriteGuardedExpr(sp.guard, bound)
        ns.body = sp.body.collect { Statement x -> rewriteGuardedStmt(x, bound, guards) }
        ns.init = sp.init == null ? null : sp.init.collect { Statement x -> rewriteGuardedStmt(x, bound, guards) }
        ns.forInVar = sp.forInVar
        ns.forInBind = sp.forInBind == null ? null : rewriteGuardedStmt(sp.forInBind, bound, guards)
        ns.isDoWhile = sp.isDoWhile
        ns.autoInvariantOnly = sp.autoInvariantOnly
        to.putNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY, ns)
    }

    /** The statement walk: replace the masked-select declaration, rewrite `r.index` everywhere else. */
    static Statement rewriteGuardedStmt(Statement st, Map<String, String> bound, Map<String, List<Expression>> guards) {
        if (st == null || st instanceof EmptyStatement) return st
        if (st instanceof BlockStatement) {
            BlockStatement b = (BlockStatement) st
            List<Statement> out = new ArrayList<Statement>()
            for (Statement s : b.statements) out.add(rewriteGuardedStmt(s, bound, guards))
            BlockStatement nb = new BlockStatement(out, b.variableScope)
            nb.setSourcePosition(b); return nb
        }
        if (st instanceof WhileStatement) {
            WhileStatement w = (WhileStatement) st
            WhileStatement nw = new WhileStatement(
                new BooleanExpression(rewriteGuardedExpr(w.booleanExpression.expression, bound)),
                rewriteGuardedStmt(w.loopBlock, bound, guards))
            nw.setSourcePosition(w); nw.copyNodeMetaData(w)
            // The LoopSpec rides as node metadata and holds its OWN statement list — the one the loop
            // encoder actually executes. Copying the metadata onto a rebuilt loop would carry the stale
            // pre-rewrite body, so the spec is rebuilt over the rewritten statements too.
            rebindLoopSpec(w, nw, bound, guards)
            return nw
        }
        if (st instanceof IfStatement) {
            IfStatement i = (IfStatement) st
            IfStatement ni = new IfStatement(
                new BooleanExpression(rewriteGuardedExpr(i.booleanExpression.expression, bound)),
                rewriteGuardedStmt(i.ifBlock, bound, guards),
                i.elseBlock == null ? EmptyStatement.INSTANCE : rewriteGuardedStmt(i.elseBlock, bound, guards))
            ni.setSourcePosition(i); ni.copyNodeMetaData(i); return ni
        }
        if (st instanceof ExpressionStatement) {
            Expression e = ((ExpressionStatement) st).expression
            if (e instanceof DeclarationExpression && ((DeclarationExpression) e).leftExpression instanceof VariableExpression) {
                DeclarationExpression de = (DeclarationExpression) e
                String n = ((VariableExpression) de.leftExpression).name
                // Phase 276 — the two spellings of one guard: a positional flag (GROOVY-12324) and a
                // per-offer `when` (GROOVY-12326). The runtime conjoins them, so the model does too.
                List<Expression> mask = awaitedSelectMask(de.rightExpression)
                List<Expression> og = offerGuardsFor(de.rightExpression, guards)
                int arity = mask != null && !mask.isEmpty() ? mask.size() : (og == null ? 0 : og.size())
                if (bound.containsKey(n) && arity > 0 && (og == null || og.size() == arity)) {
                    List<Expression> gargs = new ArrayList<Expression>()
                    for (int i = 0; i < arity; i++) {
                        Expression flag = (mask != null && i < mask.size()) ? mask.get(i) : null
                        Expression guard = og == null ? null : og.get(i)
                        Expression term = flag == null ? guard
                            : guard == null ? flag
                            : new BinaryExpression(flag, Token.newSymbol(Types.LOGICAL_AND, -1, -1), guard)
                        if (term == null) term = new ConstantExpression(true, true)
                        gargs.add(new ConstantExpression(i, true))
                        gargs.add(rewriteGuardedExpr(term, bound))
                    }
                    MethodCallExpression call = new MethodCallExpression(
                        new VariableExpression(Encoder.CHANNEL_SELECT_MARKER), 'guarded', new ArgumentListExpression(gargs))
                    call.setSourcePosition(de)
                    DeclarationExpression nd = new DeclarationExpression(new VariableExpression(bound.get(n)),
                        Token.newSymbol(Types.ASSIGN, de.lineNumber, de.columnNumber), call)
                    nd.setSourcePosition(de)
                    ExpressionStatement ns = new ExpressionStatement(nd)
                    ns.setSourcePosition(st); return ns
                }
            }
            ExpressionStatement ns = new ExpressionStatement(rewriteGuardedExpr(e, bound))
            ns.setSourcePosition(st); ns.copyNodeMetaData(st); return ns
        }
        if (st instanceof TryCatchStatement) {           // groovy-contracts wraps an @Invariant loop in one
            TryCatchStatement t = (TryCatchStatement) st
            TryCatchStatement nt = new TryCatchStatement(rewriteGuardedStmt(t.tryStatement, bound, guards),
                t.finallyStatement == null ? EmptyStatement.INSTANCE : rewriteGuardedStmt(t.finallyStatement, bound, guards))
            for (CatchStatement c : t.catchStatements) {
                CatchStatement nc = new CatchStatement(c.variable, rewriteGuardedStmt(c.code, bound, guards))
                nc.setSourcePosition(c); nt.addCatch(nc)
            }
            nt.setSourcePosition(t); nt.copyNodeMetaData(t); return nt
        }
        if (st instanceof DoWhileStatement) {
            DoWhileStatement w = (DoWhileStatement) st
            DoWhileStatement nw = new DoWhileStatement(
                new BooleanExpression(rewriteGuardedExpr(w.booleanExpression.expression, bound)),
                rewriteGuardedStmt(w.loopBlock, bound, guards))
            nw.setSourcePosition(w); nw.copyNodeMetaData(w); rebindLoopSpec(w, nw, bound, guards); return nw
        }
        if (st instanceof ForStatement) {
            ForStatement f = (ForStatement) st
            ForStatement nf = new ForStatement(f.variable, rewriteGuardedExpr(f.collectionExpression, bound),
                rewriteGuardedStmt(f.loopBlock, bound, guards))
            nf.setSourcePosition(f); nf.copyNodeMetaData(f); return nf
        }
        st
    }

    // ── Phase 119 — async-channel pipeline desugaring ───────────────────────────────────────────
    /** Rewrite an `AsyncChannel` network into plain single-assignment code; returns the body unchanged
     *  if it builds no channel or exceeds the model (the guard's verdicts are reported loudly by
     *  {@link #checkChannelLinearity}). Phase 247 — the channel is a BOUNDED FIFO: the k-th send on
     *  a channel declares its k-th element (`src.send(v)` is `def src$k = v`), the k-th receive on a
     *  stream (`first()` / awaited `receive()`) reads it, a `map { f }` stage is the pure transform `f`
     *  applied to whichever element flows through it, and a drain (`toList()` / `collect {}` /
     *  `for (v in ch)`) unrolls over the whole known sequence. FIFO delivery (the i-th value received
     *  is the i-th sent) is exact when one process owns each end and every op is unconditional —
     *  precisely what the guard admits. Pipeline-derived vars resolve lazily at the receive site. */
    static Statement desugarChannels(Statement body, Map<String, List<long[]>> bounds,
                                             Map<String, ClassNode> scalarTypes, Set<String> params, MethodNode method, List<Object[]> ghostSink = null) {
        if (!(body instanceof BlockStatement)) return body
        Set<String> ch = new HashSet<String>()
        collectChannelVars((BlockStatement) body, ch)
        if (ch.isEmpty()) return body
        body = desugarPartnerDrains((BlockStatement) body, ch, params)   // Phase 262 — a drain of a cycle partner's stream
        // Phase 241/247 — the bounded-FIFO guard: refuse the rewrite for any body with a channel
        // beyond the model (the body then skips loudly downstream; checkChannelLinearity names the
        // channel and the reason), so nothing proves an order-dependent or count-dependent value.
        if (!channelModelVerdicts((BlockStatement) body, ch, params, scalarTypes).isEmpty()) return body
        body = alphaRenameArms((BlockStatement) body)                   // Phase 252 — arm locals apart from the body's
        ChanRewrite rw = new ChanRewrite()
        rw.ch = ch; rw.bounds = bounds; rw.scalarTypes = scalarTypes; rw.method = method
        collectChannelParents((BlockStatement) body, ch, rw.parent, rw.subscribers)
        countChannelSends((BlockStatement) body, ch, rw.sendTotals)
        StreamScan scan = scanStreams((BlockStatement) body, ch, rw.parent, rw.subscribers, params, scalarTypes)   // Phase 251/252
        rw.streams.putAll(scan.streams)
        rw.consumers.putAll(scan.consumers)
        rw.partnerStreams.putAll(scan.partnerStreams)                         // Phase 258
        rw.cycleOf.putAll(scan.cycleOf)
        rw.sanctionedReceives.addAll(scan.sanctionedReceives)
        rw.sanctionedFroms.addAll(scan.sanctionedFroms)
        rw.selectRefs = scan.selectRefs
        for (StreamInfo info : rw.streams.values()) rw.sendTotals.remove(info.root)
        List<Statement> out = new ArrayList<Statement>()
        rewriteChStatements(((BlockStatement) body).statements, rw, out)
        if (ghostSink != null) ghostSink.addAll(rw.ghostErrors)                    // Phase 259 — reported by the caller
        new BlockStatement(rw.schedule(out), ((BlockStatement) body).variableScope)
    }

    /** Phase 249 — one ALT's branches for the scheduler's readiness pruning. */
    static class AltInfo {
        String name
        List<Integer> branches = new ArrayList<Integer>()
        List<String> elems = new ArrayList<String>()
        List<Expression> heads = new ArrayList<Expression>()
        List<Integer> keep
    }

    /** Phase 247 — the state of one channel rewrite: the var classes, and the per-channel element
     *  counters that make the FIFO pairing explicit (send k ↔ receive k). */
    static class ChanRewrite {
        Set<String> ch
        Map<String, List<long[]>> bounds
        Map<String, ClassNode> scalarTypes
        final Map<String, Expression> defs = new HashMap<String, Expression>()   // derived var → its definition
        final Map<String, String> parent = new HashMap<String, String>()         // derived/subscriber var → source var
        final Set<String> subscribers = new HashSet<String>()                    // vars declared from subscribe()
        final Map<String, Integer> sendTotals = new HashMap<String, Integer>()   // channel var → number of sends
        final Map<String, Integer> sendIdx = new HashMap<String, Integer>()      // channel var → sends rewritten so far
        final Map<String, Integer> recvIdx = new HashMap<String, Integer>()      // stream var → receives rewritten so far
        String subRoot, subName                                                  // active element substitution
        final Set<String> selectVars = new HashSet<String>()                      // Phase 249 — ALT result vars
        final Map<String, StreamInfo> streams = new LinkedHashMap<String, StreamInfo>()   // Phase 251 — streaming roots
        MethodNode method                                                        // for ContractNormalizer on injected invariants
        final Set<Statement> streamLoops = Collections.newSetFromMap(new IdentityHashMap<Statement, Boolean>())
        final Map<Statement, ConsumerInfo> consumers = new IdentityHashMap<Statement, ConsumerInfo>()   // Phase 252
        final Map<Statement, List<String>> producedBy = new IdentityHashMap<Statement, List<String>>()  // rewritten loop → its streams
        final Set<Expression> sanctionedReceives = Collections.newSetFromMap(new IdentityHashMap<Expression, Boolean>())
        final Set<Expression> sanctionedFroms = Collections.newSetFromMap(new IdentityHashMap<Expression, Boolean>())
        Map<String, SelectRef> selectRefs = new HashMap<String, SelectRef>()   // Phase 257 — held select instances
        ConsumerInfo curConsumer                                                 // while rewriting a consumer loop's body
        int fuelCounter                                                          // Phase 254 — free guards for while (true) loops
        final Map<Statement, Set<String>> partnerStreams = new IdentityHashMap<Statement, Set<String>>()   // Phase 258
        final Map<Statement, List<Statement>> cycleOf = new IdentityHashMap<Statement, List<Statement>>()
        int relyCounter                                                          // Phase 258 — fresh rely views
        final Map<String, String> relyName = new HashMap<String, String>()       // stream var → its current rely view name
        boolean readsAsTaken = true                                              // invariants read a partner as its taken-ghost; a BODY read (rewriteStreamStmts) as its rely view
        final List<Object[]> ghostErrors = new ArrayList<Object[]>()             // Phase 259 — [ghost text, reason, node]
        List<StreamInfo> curInfos = Collections.<StreamInfo>emptyList()          // Phase 260 — the streams the loop being rewritten produces
        boolean relyMode                                                         // instantiating a PARTNER's spec: its ghosts resolve in its context, misuse not re-reported
        /** Phase 258 — is stream var {@code v} read by the current consumer loop from a cycle partner? */
        boolean partner(String v) {
            if (curConsumer == null) return false
            Set<String> ps = partnerStreams.get((Statement) curConsumer.loop)
            ps != null && ps.contains(rootOf(v))
        }
        boolean partnerLoop(Statement loop, Statement other) {
            List<Statement> m = cycleOf.get(loop)
            m != null && m.any { Statement x -> x.is(other) }
        }
        /** The shadow list a streaming root or its map stage is drained from, else null. */
        String streamListOf(String v) {
            String r = rootOf(v)
            if (!streams.containsKey(r)) return null
            (v == r || streams.get(r).derived.contains(v)) ? v + '$q' : null
        }
        Object curProc                                                           // null = main; an arm's closure while flattening it
        final List<Object> tags = new ArrayList<Object>()                        // per emitted statement: its process
        final Map<Object, Integer> forkAt = new IdentityHashMap<Object, Integer>() // arm → emitted-count at its fork
        final List<Object> arms = new ArrayList<Object>()                        // arms in fork order

        /** Phase 249 — per ALT statement (index / value decl, by emitted position): the ALT's
         *  branches, their head elements and head expressions, and the keep-set once scheduled. */
        final Map<Integer, AltInfo> selectInfo = new HashMap<Integer, AltInfo>()

        /** Emit a rewritten statement, tagged with the process it belongs to. */
        void emit(List<Statement> out, Statement st) { out.add(st); tags.add(curProc) }

        /** Rebuild an ALT statement over the branches that are READY at its scheduling point — those
         *  whose head element has been declared by the time nothing else can run. A branch served only
         *  after the ALT's process moves on can never be the one taken: the static "which guards are
         *  ready", and it keeps the index/value pair exact (the keep-set is fixed at the index decl). */
        Statement pruneAlt(Statement st, int at, Set<String> declared) {
            AltInfo info = selectInfo.get(at)
            if (info == null) return st
            if (info.keep == null) {
                info.keep = new ArrayList<Integer>()
                for (int j = 0; j < info.branches.size(); j++) if (declared.contains(info.elems.get(j))) info.keep.add(j)
            }
            DeclarationExpression de = (DeclarationExpression) ((ExpressionStatement) st).expression
            MethodCallExpression call = (MethodCallExpression) de.rightExpression
            List<Expression> args = new ArrayList<Expression>()
            if (call.methodAsString == 'index') {
                for (Integer j : info.keep) args.add(new ConstantExpression(info.branches.get(j), true))
            } else {
                args.add(new VariableExpression(info.name + '$index'))
                for (Integer j : info.keep) { args.add(new ConstantExpression(info.branches.get(j), true)); args.add(info.heads.get(j)) }
            }
            MethodCallExpression nc = new MethodCallExpression(call.objectExpression, call.methodAsString, new ArgumentListExpression(args))
            nc.setSourcePosition(call)
            DeclarationExpression nd = new DeclarationExpression(de.leftExpression, de.operation, nc)
            nd.setSourcePosition(de)
            ExpressionStatement ns = new ExpressionStatement(nd)
            ns.setSourcePosition(st)
            ns
        }
        /** Rewrite a nested statement list (an if-branch) into its own block — no scheduling tags. */
        BlockStatement sub(List<Statement> stmts, VariableScope scope) {
            List<Statement> tmp = new ArrayList<Statement>()
            int mark = tags.size()
            rewriteChStatements(stmts, this, tmp)
            while (tags.size() > mark) tags.remove(tags.size() - 1)
            new BlockStatement(tmp, scope)
        }

        /**
         * Phase 249 — the dataflow-driven linearisation. The flattened statements are emitted per
         * PROCESS in program order, but a process's next statement runs only once every channel
         * element it reads has been declared (a receive blocks until its send) — the scheduler's own
         * rule, mechanised — and an arm becomes runnable only once main has passed its fork. Main is
         * preferred, then arms in fork order. When nothing is runnable (the network is stuck — Phase
         * 243 reports that separately) the remaining statements are emitted in textual order, so an
         * unsatisfiable read stays an unbound, unconstrained element exactly as before.
         */
        List<Statement> schedule(List<Statement> out) {
            Set<String> elements = new HashSet<String>()
            for (Map.Entry<String, Integer> e : sendTotals.entrySet()) {
                String root = rootOf(e.key)
                for (int k = 1; k <= e.value; k++) elements.add(element(root, k))
            }
            // Phase 251/252 — a stream's readers wait for its `$produced` marker (emitted after the producer
            // loop — the loop is atomic in the model); its shadow lists name the stream. A loop's own
            // produced streams are exempt (a stage as a process reads one stream and builds another).
            Map<String, String> listOwner = new HashMap<String, String>()
            for (StreamInfo info : streams.values()) {
                elements.add(info.root + '$produced')
                listOwner.put(info.root + '$q', info.root)
                for (String d : info.derived) listOwner.put(d + '$q', info.root)
            }
            Map<String, Object> producerTag = new HashMap<String, Object>()          // Phase 255 — a stream's producing process
            for (int i = 0; i < out.size(); i++) if (producedBy.containsKey(out.get(i))) for (String r : producedBy.get(out.get(i))) producerTag.put(r, tags.get(i))
            List<Set<String>> uses = new ArrayList<Set<String>>(), defs = new ArrayList<Set<String>>()
            for (int si = 0; si < out.size(); si++) {
                Statement st = out.get(si)
                final Object myTag = tags.get(si)
                final Set<String> u = new HashSet<String>(), d = new HashSet<String>()
                final Collection<String> ownStreams = producedBy.containsKey(st) ? producedBy.get(st) : Collections.<String>emptyList()
                st.visit(new CodeVisitorSupport() {
                    @Override void visitDeclarationExpression(DeclarationExpression de) {
                        if (de.leftExpression instanceof VariableExpression) {
                            String n = ((VariableExpression) de.leftExpression).name
                            if (elements.contains(n)) d.add(n)
                            if (listOwner.containsKey(n)) { de.rightExpression?.visit(this); return }   // the shadow decl itself
                        }
                        de.rightExpression?.visit(this)
                    }
                    @Override void visitVariableExpression(VariableExpression ve) {
                        if (elements.contains(ve.name)) u.add(ve.name)
                        if (listOwner.containsKey(ve.name) && !ownStreams.contains(listOwner.get(ve.name)) &&
                            !(producerTag.containsKey(listOwner.get(ve.name)) && producerTag.get(listOwner.get(ve.name)) == myTag)) {
                            u.add(listOwner.get(ve.name) + '$produced')
                        }
                    }
                })
                uses.add(u); defs.add(d)
            }
            List<Object> procs = new ArrayList<Object>()
            procs.add(null); procs.addAll(arms)
            Map<Object, List<Integer>> queue = new IdentityHashMap<Object, List<Integer>>()
            for (Object p : procs) queue.put(p, new ArrayList<Integer>())
            for (int i = 0; i < out.size(); i++) {
                Object t = tags.get(i)
                List<Integer> q = queue.get(t)
                if (q == null) { q = new ArrayList<Integer>(); queue.put(t, q); procs.add(t) }
                q.add(i)
            }
            Map<Object, Integer> mainBefore = new IdentityHashMap<Object, Integer>()
            for (Object a : arms) {
                Integer at = forkAt.get(a)
                int cnt = 0
                for (int i = 0; i < out.size() && at != null && i < at; i++) if (tags.get(i) == null) cnt++
                mainBefore.put(a, cnt)
            }
            Set<String> declared = new HashSet<String>()
            List<Statement> result = new ArrayList<Statement>()
            int mainEmitted = 0
            int remaining = out.size()
            while (remaining > 0) {
                int pick = -1, altPick = -1
                for (Object p : procs) {
                    List<Integer> q = queue.get(p)
                    if (q.isEmpty()) continue
                    if (p != null && mainBefore.containsKey(p) && mainEmitted < mainBefore.get(p)) continue
                    int head = q.get(0)
                    if (selectInfo.containsKey(head)) { if (altPick < 0) altPick = head; continue }   // an ALT runs last
                    if (declared.containsAll(uses.get(head))) { pick = head; break }
                }
                if (pick < 0 && altPick >= 0) {                  // nothing else can run: the ALT's ready branches are known
                    pick = altPick
                    out.set(pick, pruneAlt(out.get(pick), pick, declared))
                }
                if (pick < 0) {                                  // stuck: fall back to textual order
                    for (int i = 0; i < out.size(); i++) {
                        List<Integer> q = queue.get(tags.get(i))
                        if (!q.isEmpty() && q.get(0) == i) { pick = i; break }
                    }
                    if (pick < 0) for (Object p : procs) { List<Integer> q = queue.get(p); if (!q.isEmpty()) { pick = q.get(0); break } }
                }
                if (selectInfo.containsKey(pick)) out.set(pick, pruneAlt(out.get(pick), pick, declared))
                queue.get(tags.get(pick)).remove(0)
                if (tags.get(pick) == null) mainEmitted++
                declared.addAll(defs.get(pick))
                result.add(out.get(pick))
                remaining--
            }
            result
        }

        /** The created channel a var derives from ({@code out → src}, {@code branch1 → b}). */
        String rootOf(String v) { String r = v; int g = 0; while (parent.containsKey(r) && g++ < 100) r = parent.get(r); r }
        /** The stream a receive on {@code v} consumes: the nearest subscriber var (each subscriber
         *  sees every broadcast element from its own cursor), else the root. */
        String streamOf(String v) {
            String r = v; int g = 0
            while (!subscribers.contains(r) && parent.containsKey(r) && g++ < 100) r = parent.get(r)
            r
        }
        int next(Map<String, Integer> m, String k) { Integer n = m.get(k); int v = (n == null ? 0 : n) + 1; m.put(k, v); v }
        int total(String root) { Integer n = sendTotals.get(root); n == null ? 0 : n }
        String element(String root, int k) { root + '$' + k }
        /** Run {@code body} with the root's occurrences standing for the given element. */
        Expression withElement(String root, String name, Closure<Expression> body) {
            String sr = subRoot, sn = subName
            subRoot = root; subName = name
            try { return body.call() } finally { subRoot = sr; subName = sn }
        }
        /** An element name takes its channel's registered element type (Phase 246: non-Int scalars). */
        void registerType(String root, String name) {
            ClassNode t = scalarTypes.get(root)
            if (t != null && !scalarTypes.containsKey(name)) scalarTypes.put(name, t)
        }
    }

    /** The base channel var an end-use targets, walking pipeline ops down to the variable:
     *  {@code src.map{f}.first()} → {@code src}; a non-channel receiver → null. (Phase 241) */
    static String chanRoot(Expression recv, Set<String> ch) {
        Expression e = stripCasts(recv)
        while (e instanceof MethodCallExpression && ((MethodCallExpression) e).methodAsString in CHANNEL_PIPE_OPS) {
            e = stripCasts(((MethodCallExpression) e).objectExpression)
        }
        (e instanceof VariableExpression && ch.contains(((VariableExpression) e).name)) ? ((VariableExpression) e).name : null
    }

    /** The pipeline ops applied between {@code recv} and its base var, bottom-up. */
    static List<String> chanChainOps(Expression recv) {
        List<String> ops = new ArrayList<String>()
        Expression e = stripCasts(recv)
        while (e instanceof MethodCallExpression && ((MethodCallExpression) e).methodAsString in CHANNEL_PIPE_OPS) {
            ops.add(0, ((MethodCallExpression) e).methodAsString)
            e = stripCasts(((MethodCallExpression) e).objectExpression)
        }
        ops
    }

    /** Phase 247 — derivation edges: {@code def out = src.map{..}} records {@code out → src}; a var whose
     *  chain includes {@code subscribe()} is a subscriber (its own receive cursor). */
    static void collectChannelParents(BlockStatement body, Set<String> ch, Map<String, String> parent,
                                              Set<String> subscribers) {
        body.visit(new CodeVisitorSupport() {
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (de.leftExpression instanceof VariableExpression && isChannelExpr(de.rightExpression, ch) &&
                    !(de.rightExpression instanceof VariableExpression)) {
                    String name = ((VariableExpression) de.leftExpression).name
                    String base = chanRoot(de.rightExpression, ch)
                    if (base != null) parent.put(name, base)
                    if (chanChainOps(de.rightExpression).contains('subscribe')) subscribers.add(name)
                }
                super.visitDeclarationExpression(de)
            }
        })
    }

    /** Phase 247 — sends per channel var (the guard has already required every send unconditional). */
    static void countChannelSends(BlockStatement body, Set<String> ch, Map<String, Integer> totals) {
        body.visit(new CodeVisitorSupport() {
            @Override void visitMethodCallExpression(MethodCallExpression m) {
                Expression recv = stripCasts(m.objectExpression)
                if (m.methodAsString == 'send' && recv instanceof VariableExpression &&
                    ch.contains(((VariableExpression) recv).name)) {
                    String name = ((VariableExpression) recv).name
                    Integer n = totals.get(name)
                    totals.put(name, n == null ? 1 : n + 1)
                }
                super.visitMethodCallExpression(m)
            }
        })
    }

    /** The stage kinds through which element identity (and count) is exact: a map is a per-element
     *  transform, a subscribe is the identity. filter/split/merge/tap change the count or interleave. */
    static final List<String> CHANNEL_EXACT_OPS = ['map', 'subscribe'].asImmutable()

    /**
     * Phase 247 — the bounded-FIFO model's verdicts: channel var → the reason it is beyond the model
     * (empty when every channel is in). In the model a channel carries a statically-known sequence:
     * every send, receive, drain and derivation is UNCONDITIONAL (not inside an if / loop / catch /
     * switch / non-async closure), all sends come from ONE process and all receives from ONE process
     * (the flattened program order is then the FIFO order), a channel has at most ONE consumer family
     * (direct receives, or one derived stage), and a drain runs over an exact chain (map/subscribe
     * only) with an unrollable loop body. Everything else refuses the value rewrite — the runtime
     * would be FIFO-first / count-dependent where the rewrite would prove last-write-wins.
     * (Phase 241 introduced the guard as one-in-flight; Phase 247 widened it to the bounded FIFO.)
     */
    static Map<String, String> channelModelVerdicts(BlockStatement body, Set<String> ch, Set<String> params,
                                                            Map<String, ClassNode> scalarTypes) {
        final Map<String, String> verdict = new LinkedHashMap<String, String>()
        final Map<String, Set<Object>> sendProcs = new HashMap<String, Set<Object>>()
        final Map<String, Set<Object>> recvProcs = new HashMap<String, Set<Object>>()
        final Map<String, Set<String>> families = new HashMap<String, Set<String>>()
        final Map<String, String> parent = new HashMap<String, String>()
        final Set<String> subscribers = new HashSet<String>()
        final Map<String, Boolean> exactVar = new HashMap<String, Boolean>()   // derived var → chain exact so far
        collectChannelParents(body, ch, parent, subscribers)
        // Phase 251 — streaming channels: their one loop send is sanctioned; other loop sends carry a reason.
        final StreamScan streamScan = scanStreams(body, ch, parent, subscribers, params, scalarTypes)
        final Set<String> selected = new HashSet<String>()                 // Phase 249 — channels an ALT has chosen over
        final Map<String, String> selectResult = new HashMap<String, String>()   // ALT result var → its first channel
        final Set<Expression> sanctionedFrom = Collections.newSetFromMap(new IdentityHashMap<Expression, Boolean>())
        body.visit(new CodeVisitorSupport() {
            private int condDepth
            private Object proc = 'main'
            private void flag(String name, String reason) { if (!verdict.containsKey(name)) verdict.put(name, reason) }
            private void afterSelect(String name) {
                if (selected.contains(name)) flag(name, 'is received from after an ALT that may have consumed its element (a one-shot ALT must be the last receive on each of its channels)')
            }
            /** Phase 273 — a guarded ALT whose arms do not agree positionally: `r.index` would name a
             *  different channel depending on which arm built the select, so no branch-wise spec means
             *  anything. Named exactly, because it is the API's own gap: JCSP's `select(preCon)` masks a
             *  guard while KEEPING its index, and a positional `ChannelSelect.from(…)` cannot. */
            private void guardedMismatch(SelectRef r) {
                for (Expression a : r.chans) {
                    String n = chanNameOf(a)
                    if (n != null && ch.contains(n)) {
                        flag(n, "is a branch of a guarded ALT whose branch POSITIONS differ between the arms of its " +
                                "condition, so r.index would not name the same channel in every arm. Offer the branches " +
                                "in the same positions (a guarded ALT may drop a branch only from the END) — " +
                                "ChannelSelect.from(…) is positional, where JCSP's select(preCon) masks a guard while " +
                                "keeping its index; this API has no equivalent")
                        return
                    }
                }
            }
            private void fromOutsideShape(Expression call) {
                List<Expression> args = selectFromArgs(call)
                if (args == null || sanctionedFrom.contains(stripCasts(call))) return
                for (Expression a : args) {
                    Expression x = stripCasts(a)
                    if (x instanceof VariableExpression && ch.contains(((VariableExpression) x).name)) {
                        flag(((VariableExpression) x).name, 'is passed to a ChannelSelect outside the supported shapes (Result r = await ChannelSelect.from(a, b)[.fair()|.random()].select(), inline or via a held instance used only as alt.select(); r used via .index / .value)')
                    }
                }
            }
            @Override void visitStaticMethodCallExpression(StaticMethodCallExpression m) {
                ClosureExpression arm = asyncClosure(m)
                if (arm != null) { visitArm(arm); return }
                fromOutsideShape(m)
                super.visitStaticMethodCallExpression(m)
            }
            @Override void visitPropertyExpression(PropertyExpression pe) {
                Expression obj = stripCasts(pe.objectExpression)
                if (obj instanceof VariableExpression && selectResult.containsKey(((VariableExpression) obj).name) &&
                    (pe.propertyAsString == 'index' || pe.propertyAsString == 'value')) return    // the sanctioned reads
                super.visitPropertyExpression(pe)
            }
            @Override void visitVariableExpression(VariableExpression ve) {
                if (selectResult.containsKey(ve.name)) flag(selectResult.get(ve.name), "has an ALT result ('${ve.name}') used beyond .index / .value")
                if (streamScan.selectRefs.containsKey(ve.name)) {              // Phase 257 — a held instance escaping its select() use
                    SelectRef r = streamScan.selectRefs.get(ve.name)
                    for (Expression a : r.chans) { Expression x = stripCasts(a); if (x instanceof VariableExpression && ch.contains(((VariableExpression) x).name)) { flag(((VariableExpression) x).name, "has its ChannelSelect instance ('${ve.name}') used beyond alt.select()"); break } }
                }
                super.visitVariableExpression(ve)
            }
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                Expression rhs0 = stripCasts(de.rightExpression)          // Phase 273 — the guarded-ALT index check
                if (rhs0 instanceof TernaryExpression) {
                    SelectRef gr = selectChainInfo(rhs0)
                    if (gr != null && gr.indexUnstable) guardedMismatch(gr)
                }
                // Phase 257 — a held select instance's declaration: its from() is sanctioned; the var must only be selected on
                if (de.leftExpression instanceof VariableExpression && streamScan.selectRefs.containsKey(((VariableExpression) de.leftExpression).name)) {
                    sanctionedFrom.addAll(streamScan.selectRefs.get(((VariableExpression) de.leftExpression).name).fromCalls)
                    de.rightExpression.visit(this)
                    return
                }
                SelectRef ref = awaitedSelect(de.rightExpression, streamScan.selectRefs)
                List<Expression> alt = ref == null ? null : ref.chans
                if (alt != null && de.leftExpression instanceof VariableExpression) {
                    boolean loopingAlt = streamScan.sanctionedFroms.contains(awaitedSelectCall(de.rightExpression))   // Phase 253 — the select() call
                    String first = null
                    for (Expression a : alt) {
                        Expression x = stripCasts(a)
                        String name = (x instanceof VariableExpression && ch.contains(((VariableExpression) x).name)) ? ((VariableExpression) x).name : null
                        if (name == null) { if (first != null) flag(first, 'is in an ALT with a non-channel-variable branch (declare each stage as a variable first)'); continue }
                        if (first == null) first = name
                        if (condDepth > 0 && !loopingAlt) flag(name, "has a channel operation that is not one-shot — inside an if / loop / catch / closure (line ${de.lineNumber})")
                        afterSelect(name)
                        owner(name, recvProcs, 'receive'); family(name, 'reads')
                        selected.add(name)
                    }
                    if (first != null) selectResult.put(((VariableExpression) de.leftExpression).name, first)
                    if (!ref.held) sanctionedFrom.addAll(ref.fromCalls)
                    de.rightExpression.visit(this)          // still walk it (nested arms / other channels), the from() sanctioned
                    return
                }
                if (de.leftExpression instanceof VariableExpression && parent.containsKey(((VariableExpression) de.leftExpression).name)) {
                    List<String> ops = chanChainOps(de.rightExpression)
                    boolean exact = true
                    for (String op : ops) if (!(op in CHANNEL_EXACT_OPS)) exact = false
                    exactVar.put(((VariableExpression) de.leftExpression).name, exact)
                }
                super.visitDeclarationExpression(de)
            }
            private void owner(String name, Map<String, Set<Object>> procs, String end) {
                Set<Object> s = procs.get(name)
                if (s == null) { s = new HashSet<Object>(); procs.put(name, s) }
                s.add(proc)
                if (s.size() > 1) flag(name, "has ${end}s from more than one process")
            }
            private void family(String name, String key) {
                Set<String> f = families.get(name)
                if (f == null) { f = new HashSet<String>(); families.put(name, f) }
                f.add(key)
                if (f.size() > 1) flag(name, 'has more than one consumer (direct receives and/or pipeline stages)')
            }
            private String parentRoot(String name) {
                String r = name; int g = 0
                while (parent.containsKey(r) && g++ < 100) r = parent.get(r)
                r
            }
            private boolean exactChain(String name) {
                String r = name; int g = 0
                while (parent.containsKey(r) && g++ < 100) {
                    if (exactVar.get(r) == Boolean.FALSE) return false
                    r = parent.get(r)
                }
                true
            }
            private void visitArm(ClosureExpression arm) {   // an async arm: its own process, one-shot
                Object saved = proc
                proc = arm
                try { arm.code?.visit(this) } finally { proc = saved }
            }
            @Override void visitMethodCallExpression(MethodCallExpression m) {
                ClosureExpression arm = asyncClosure(m)
                if (arm != null) { visitArm(arm); return }
                fromOutsideShape(m)
                Expression recv = stripCasts(m.objectExpression)
                if (recv instanceof VariableExpression && selectResult.containsKey(((VariableExpression) recv).name) && noArgs(m) &&
                    (m.methodAsString == 'getIndex' || m.methodAsString == 'getValue')) return   // the sanctioned getters
                if (recv instanceof VariableExpression && streamScan.selectRefs.containsKey(((VariableExpression) recv).name) &&
                    m.methodAsString == 'select' && noArgs(m)) return                            // Phase 257 — alt.select(): the sanctioned use
                if (recv instanceof VariableExpression && ch.contains(((VariableExpression) recv).name)) {
                    String name = ((VariableExpression) recv).name
                    String mm = m.methodAsString
                    boolean isSend = mm == 'send'
                    boolean isRead = mm == 'first' || mm == 'receive'
                    boolean isDrain = mm in CHANNEL_DRAIN_OPS
                    boolean isDerive = mm in CHANNEL_PIPE_OPS && mm != 'subscribe'
                    if (isSend || isRead || isDrain || isDerive) {
                        boolean streaming = streamScan.streams.containsKey(name) || streamScan.streams.containsKey(parentRoot(name))
                        if (isSend && streamScan.sanctionedSends.contains(m)) {
                            // Phase 251 — the producer loop's send: the streaming model's own shape
                        } else if (isRead && streamScan.sanctionedReceives.contains(m)) {
                            // Phase 252 — a consumer loop's receive: element k of the stream
                        } else if (isRead && streaming) {
                            flag(name, "is received one element at a time from a streaming producer outside a specified unit-counter consumer loop (drain it — toList() — or read it once per iteration in a while / C-style loop with an @Invariant / @Decreases)")
                        } else if (isDrain && streaming && mm != 'toList') {
                            flag(name, "is drained by ${mm} {} from a streaming producer (toList() is the drained-value spelling)")
                        } else if (condDepth > 0 && (isSend || isRead) && streamScan.whyNot.containsKey(name)) {   // Phase 258 — the reason, at either end
                            flag(name, streamScan.whyNot.get(name))
                        } else if (condDepth > 0 && !(isDerive && streaming)) {
                            flag(name, "has a channel operation that is not one-shot — inside an if / loop / catch / closure (line ${m.lineNumber})")
                        }
                        if (isSend) owner(name, sendProcs, 'send')
                        if (isRead || isDrain) { afterSelect(name); owner(name, recvProcs, 'receive'); family(name, 'reads') }
                        if (isDerive) family(name, "stage@${m.lineNumber}:${m.columnNumber}")
                        if (isDrain && (mm == 'each' || !exactChain(name))) {
                            flag(name, mm == 'each' ? "is drained by each {} (an accumulating each carries no invariant — use for (v in ch) or toList())" :
                                 'is drained through a filter / split / merge / tap stage (element count unknown)')
                        }
                    }
                }
                super.visitMethodCallExpression(m)
            }
            @Override void visitForLoop(ForStatement st) {
                Expression coll = stripCasts(st.collectionExpression)
                String base = chanRoot(coll, ch)
                if (base != null) {                       // for (v in ch) — a drain, unrolled over the sequence
                    String name = coll instanceof VariableExpression ? base : null
                    if (name == null) flag(base, "is iterated through an inline pipeline expression (declare the stage as a variable first)")
                    else {
                        if (condDepth > 0) flag(name, "has a channel operation that is not one-shot — inside an if / loop / catch / closure (line ${coll.lineNumber})")
                        afterSelect(name)
                        owner(name, recvProcs, 'receive'); family(name, 'reads')
                        if (!exactChain(name)) flag(name, 'is drained through a filter / split / merge / tap stage (element count unknown)')
                        boolean streaming = streamScan.streams.containsKey(parentRoot(name))
                        if (!streaming && !unrollableLoopBody(st.loopBlock)) flag(name, "is drained by a loop whose body is beyond the unrolling fragment (nested loop / try / switch / break)")
                    }
                } else {
                    st.collectionExpression?.visit(this)
                }
                condDepth++
                try { st.loopBlock?.visit(this) } finally { condDepth-- }
            }
            @Override void visitWhileLoop(WhileStatement st) {
                st.booleanExpression?.visit(this)
                condDepth++
                try { st.loopBlock?.visit(this) } finally { condDepth-- }
            }
            @Override void visitDoWhileLoop(DoWhileStatement st) {
                condDepth++
                try { st.loopBlock?.visit(this) } finally { condDepth-- }
                st.booleanExpression?.visit(this)
            }
            @Override void visitIfElse(IfStatement st) {
                st.booleanExpression?.visit(this)
                condDepth++
                try { st.ifBlock?.visit(this); st.elseBlock?.visit(this) } finally { condDepth-- }
            }
            @Override void visitTryCatchFinally(org.codehaus.groovy.ast.stmt.TryCatchStatement st) {
                condDepth++
                try { super.visitTryCatchFinally(st) } finally { condDepth-- }
            }
            @Override void visitSwitch(org.codehaus.groovy.ast.stmt.SwitchStatement st) {
                condDepth++
                try { super.visitSwitch(st) } finally { condDepth-- }
            }
            @Override void visitClosureExpression(ClosureExpression c) {      // a non-async closure's interior
                condDepth++
                try { super.visitClosureExpression(c) } finally { condDepth-- }
            }
        })
        verdict
    }

    /** Phase 247 — a drain-loop body the unroller can copy: blocks, expression statements, returns and
     *  if/else (no nested loops, try, switch, break/continue — those need the loop's own semantics). */
    static boolean unrollableLoopBody(Statement s) {
        if (s == null || s instanceof EmptyStatement) return true
        if (s instanceof BlockStatement) {
            for (Statement st : ((BlockStatement) s).statements) if (!unrollableLoopBody(st)) return false
            return true
        }
        if (s instanceof IfStatement) {
            IfStatement i = (IfStatement) s
            return unrollableLoopBody(i.ifBlock) && unrollableLoopBody(i.elseBlock)
        }
        s instanceof ExpressionStatement || s instanceof ReturnStatement
    }

    /** A var is a channel var if declared from `AsyncChannel.create(...)` / `BroadcastChannel.create(...)` or
     *  from a pipeline op whose source is already a channel var. Single forward pass — declarations are in
     *  source order. */
    static void collectChannelVars(BlockStatement body, Set<String> ch) {
        body.visit(new CodeVisitorSupport() {
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (de.leftExpression instanceof VariableExpression &&
                    (isChannelCreate(de.rightExpression) || isBroadcastCreate(de.rightExpression) ||
                     isChannelExpr(de.rightExpression, ch))) {
                    ch.add(((VariableExpression) de.leftExpression).name)
                }
                super.visitDeclarationExpression(de)
            }
        })
    }

    /** `AsyncChannel.create(...)` — interface static factory, either AST shape (post-STC static call, or a
     *  method call on a class/property reference named {@code AsyncChannel}). */
    static boolean isChannelCreate(Expression e) {
        if (e instanceof StaticMethodCallExpression) {
            StaticMethodCallExpression m = (StaticMethodCallExpression) e
            return m.method == 'create' && m.ownerType?.nameWithoutPackage == 'AsyncChannel'
        }
        if (e instanceof MethodCallExpression) {
            MethodCallExpression m = (MethodCallExpression) e
            return m.methodAsString == 'create' && channelOwnerName(m.objectExpression) == 'AsyncChannel'
        }
        false
    }

    static String channelOwnerName(Expression obj) {
        if (obj instanceof ClassExpression) return ((ClassExpression) obj).type?.nameWithoutPackage
        if (obj instanceof PropertyExpression) return ((PropertyExpression) obj).propertyAsString
        if (obj instanceof VariableExpression) return ((VariableExpression) obj).name
        null
    }

    /** `BroadcastChannel.create(...)` — one-to-many delivery; each `subscribe()` hands the receiver its own
     *  per-subscriber `AsyncChannel` (Phase 241). Same AST shapes as {@link #isChannelCreate}. */
    static boolean isBroadcastCreate(Expression e) {
        if (e instanceof StaticMethodCallExpression) {
            StaticMethodCallExpression m = (StaticMethodCallExpression) e
            return m.method == 'create' && m.ownerType?.nameWithoutPackage == 'BroadcastChannel'
        }
        if (e instanceof MethodCallExpression) {
            MethodCallExpression m = (MethodCallExpression) e
            return m.methodAsString == 'create' && channelOwnerName(m.objectExpression) == 'BroadcastChannel'
        }
        false
    }

    /** The pipeline/derivation ops that yield a channel from a channel (Phase 119; `subscribe` Phase 241). */
    static final List<String> CHANNEL_PIPE_OPS = ['map', 'filter', 'tap', 'merge', 'split', 'subscribe'].asImmutable()

    /** A channel-valued expression: a channel var, or a pipeline/derivation op on one. */
    static boolean isChannelExpr(Expression e, Set<String> ch) {
        if (e instanceof VariableExpression) return ch.contains(((VariableExpression) e).name)
        if (e instanceof MethodCallExpression) {
            MethodCallExpression m = (MethodCallExpression) e
            return (m.methodAsString in CHANNEL_PIPE_OPS) && isChannelExpr(m.objectExpression, ch)
        }
        false
    }

    static void rewriteChStatements(List<Statement> stmts, ChanRewrite rw, List<Statement> out) {
        Set<String> ch = rw.ch
        for (Statement st : stmts) {
            if (st instanceof BlockStatement) { rewriteChStatements(((BlockStatement) st).statements, rw, out); continue }
            if (st instanceof ExpressionStatement) {
                Expression e = ((ExpressionStatement) st).expression
                ClosureExpression cl = asyncClosure(e)                       // async { … } → flatten inline (transparent)
                if (cl != null) {
                    // Phase 249 — the arm's statements are tagged as its own process and scheduled by
                    // dataflow (ChanRewrite.schedule), no longer by their textual position.
                    Object saved = rw.curProc
                    rw.forkAt.put(cl, out.size()); rw.arms.add(cl); rw.curProc = cl
                    try {
                        if (cl.code instanceof BlockStatement) rewriteChStatements(((BlockStatement) cl.code).statements, rw, out)
                    } finally { rw.curProc = saved }
                    continue
                }
                if (e instanceof MethodCallExpression) {
                    MethodCallExpression m = (MethodCallExpression) e
                    if (isChannelExpr(m.objectExpression, ch) && m.methodAsString == 'close') continue   // close → drop
                    if (m.methodAsString == 'send' && m.objectExpression instanceof VariableExpression &&
                        rw.streams.containsKey(((VariableExpression) m.objectExpression).name)) {   // Phase 255 — a priming send appends
                        String c = ((VariableExpression) m.objectExpression).name
                        StreamInfo info = rw.streams.get(c)
                        List<Expression> a = (m.arguments instanceof ArgumentListExpression) ?
                            ((ArgumentListExpression) m.arguments).expressions : Collections.<Expression>emptyList()
                        if (a.size() == 1) {
                            Expression val = rewriteChExpr(a.get(0), rw)
                            List<long[]> bs = rw.bounds.get(c)
                            if (bs != null && !bs.isEmpty()) rw.emit(out, boundsAssert(val, bs, m))
                            rw.emit(out, addStmt(c + '$q', val, m))
                            for (String d : info.derived) rw.emit(out, addStmt(d + '$q', derivedValue(d, val, rw), m))
                            continue
                        }
                    }
                    if (isChannelExpr(m.objectExpression, ch) && m.methodAsString == 'send' &&
                        m.objectExpression instanceof VariableExpression) {     // k-th send(v) → def ch$k = v
                        List<Expression> a = (m.arguments instanceof ArgumentListExpression) ?
                            ((ArgumentListExpression) m.arguments).expressions : Collections.<Expression>emptyList()
                        if (a.size() == 1) {
                            String name = ((VariableExpression) m.objectExpression).name
                            Expression val = rewriteChExpr(a.get(0), rw)
                            // Phase 242 — send-checked: a constrained channel's send carries its
                            // contract assert (φ over the element), discharged with a counterexample.
                            List<long[]> bs = rw.bounds.get(name)
                            if (bs != null && !bs.isEmpty()) rw.emit(out, boundsAssert(val, bs, m))
                            // The send DECLARES its element (the create-decl below is dropped): the
                            // rewritten body stays single-assignment, so the value-flow pass — and
                            // with it the assert discharge — keeps the whole pipeline in fragment.
                            // Phase 247 — the k-th send declares element k; the k-th receive reads it.
                            String elem = rw.element(name, rw.next(rw.sendIdx, name))
                            rw.registerType(name, elem)
                            VariableExpression lhs = new VariableExpression(elem)
                            DeclarationExpression decl = new DeclarationExpression(
                                lhs, Token.newSymbol(Types.ASSIGN, m.lineNumber, m.columnNumber), val)
                            decl.setSourcePosition(m)
                            rw.emit(out, new ExpressionStatement(decl))
                            continue
                        }
                    }
                }
                if (e instanceof DeclarationExpression && ((DeclarationExpression) e).leftExpression instanceof VariableExpression) {
                    DeclarationExpression de = (DeclarationExpression) e
                    String name = ((VariableExpression) de.leftExpression).name
                    List<Expression> alt = awaitedSelectArgs(de.rightExpression, rw.selectRefs)
                    if (alt != null) {                                       // Phase 249 — def r = await ChannelSelect.from(a, b).select()
                        rewriteSelect(name, alt, de, rw, out)
                        continue
                    }
                    if (rw.selectRefs.containsKey(name)) continue            // Phase 257 — a held select instance: no value of its own
                    if (rw.streams.containsKey(name)) {                           // Phase 251 — the shadow list
                        rw.emit(out, listDecl(name + '$q', de))
                        continue
                    }
                    if (isChannelExpr(de.rightExpression, ch) && rw.streamListOf(name) != null) {   // a map stage of a stream
                        rw.defs.put(name, de.rightExpression)
                        rw.emit(out, listDecl(name + '$q', de))
                        continue
                    }
                    if (isChannelCreate(de.rightExpression) || isBroadcastCreate(de.rightExpression)) {
                        // def src = AsyncChannel.create(n) / def b = BroadcastChannel.create() → dropped:
                        // the sends declare the elements (above). A channel that is never sent to has no
                        // binding at all — a read of it stays unconstrained (a never-sent channel BLOCKS
                        // at runtime; the old `def src = 0` placeholder modelled it as the value 0).
                        continue
                    }
                    if (isChannelExpr(de.rightExpression, ch)) {           // def out = src.map{..} → record pipeline, defer
                        rw.defs.put(name, de.rightExpression)
                        continue
                    }
                }
                rw.emit(out, new ExpressionStatement(rewriteChExpr(e, rw)))
                continue
            }
            if (st instanceof ReturnStatement) {
                Expression r = ((ReturnStatement) st).expression
                rw.emit(out, new ReturnStatement(r == null ? r : rewriteChExpr(r, rw)))
                continue
            }
            if (st instanceof LoopingStatement && !rw.streams.isEmpty()) {     // Phase 251/252 — a producer and/or consumer loop
                List<StreamInfo> infos = new ArrayList<StreamInfo>()
                for (StreamInfo info : rw.streams.values()) if (info.loop.is(st)) infos.add(info)
                if (!infos.isEmpty() || rw.consumers.containsKey(st)) {
                    ConsumerInfo ci0 = rw.consumers.get(st)
                    if (ci0 != null && ci0.altVar != null) {                     // Phase 253 — the branches' ghost cursors
                        for (String c : ci0.altChans) {
                            DeclarationExpression cur = new DeclarationExpression(new VariableExpression(c + '$c', ClassHelper.int_TYPE),
                                Token.newSymbol(Types.ASSIGN, st.lineNumber, st.columnNumber), new ConstantExpression(0, true))
                            cur.setSourcePosition(st)
                            rw.emit(out, new ExpressionStatement(cur))
                        }
                    }
                    if (ci0 != null) {                                           // Phase 258 — taken-ghosts: ALT branches, partner reads
                        for (String v : takenVars(ci0, rw)) {
                            DeclarationExpression tk = new DeclarationExpression(new VariableExpression(v + '$taken'),
                                Token.newSymbol(Types.ASSIGN, st.lineNumber, st.columnNumber), new ListExpression())
                            tk.setSourcePosition(st)
                            rw.emit(out, new ExpressionStatement(tk))
                        }
                    }
                    Statement loop = rewriteStreamLoop((LoopingStatement) st, infos, rw)
                    rw.streamLoops.add(loop)
                    List<String> roots = new ArrayList<String>()
                    for (StreamInfo info : infos) roots.add(info.root)
                    rw.producedBy.put(loop, roots)
                    rw.emit(out, loop)
                    for (StreamInfo info : infos) {                              // the stream is complete: readers may run
                        DeclarationExpression done = new DeclarationExpression(new VariableExpression(info.root + '$produced'),
                            Token.newSymbol(Types.ASSIGN, st.lineNumber, st.columnNumber), new ConstantExpression(true))
                        done.setSourcePosition(st)
                        rw.emit(out, new ExpressionStatement(done))
                    }
                    continue
                }
            }
            if (st instanceof ForStatement && isChannelExpr(stripCasts(((ForStatement) st).collectionExpression), ch)) {
                Expression coll = stripCasts(((ForStatement) st).collectionExpression)
                String q = coll instanceof VariableExpression ? rw.streamListOf(((VariableExpression) coll).name) : null
                if (q != null) {                                                // Phase 251 — a drain of a stream
                    rw.emit(out, streamDrainLoop((ForStatement) st, q, ((VariableExpression) coll).name, rw))
                    continue
                }
                unrollChannelDrain((ForStatement) st, rw, out)                 // Phase 247 — for (v in ch) over the sequence
                continue
            }
            if (st instanceof IfStatement) {                                   // Phase 249 — branches rewritten in place (r.index / r.value)
                IfStatement i = (IfStatement) st
                Statement ib = i.ifBlock, eb = i.elseBlock
                BlockStatement nib = rw.sub(ib instanceof BlockStatement ? ((BlockStatement) ib).statements : Collections.singletonList(ib),
                    ib instanceof BlockStatement ? ((BlockStatement) ib).variableScope : null)
                Statement neb = (eb == null || eb instanceof EmptyStatement) ? eb :
                    rw.sub(eb instanceof BlockStatement ? ((BlockStatement) eb).statements : Collections.singletonList(eb),
                        eb instanceof BlockStatement ? ((BlockStatement) eb).variableScope : null)
                IfStatement ni = new IfStatement(new BooleanExpression(rewriteChExpr(i.booleanExpression.expression, rw)), nib,
                    neb == null ? EmptyStatement.INSTANCE : neb)
                ni.setSourcePosition(st); ni.copyNodeMetaData(st)
                rw.emit(out, ni)
                continue
            }
            rw.emit(out, st)
        }
    }

    /** Phase 249 — an ALT: `def r = await ChannelSelect.from(c0, c1, …).select()` becomes
     *  `def r$index = $channelSelect.index(i…)` over the READY branches (those with an element left —
     *  the k-th receive on that stream would be satisfiable) and `def r$value = $channelSelect.value(
     *  r$index, i, head_i, …)`, each head the branch's next element run through its stages. The
     *  Encoder binds the index as a nondeterministic choice and the value as the matching ite chain.
     *  `r.index` / `r.value` (and the getters) then read the two shadows. One-shot: the guard has
     *  required the ALT to be the last receive on each of its channels, so no cursor advances. */
    static void rewriteSelect(String name, List<Expression> alt, DeclarationExpression de, ChanRewrite rw, List<Statement> out) {
        // Phase 275 — a MASKED select (GROOVY-12324): the branch the runtime commits is one whose flag
        // holds, and that is exactly the fact a guarded loop's invariant turns on ("the PUT arm runs only
        // while there is room"). Emitted over EVERY branch with its flag, not only the branches with an
        // element left: the mask is about enablement, and readiness — where it is statically known at all —
        // is the existing stream machinery's business. Modelling more indices than can really occur is a
        // sound over-approximation for the safety claims this proves.
        List<Expression> mask = awaitedSelectMask(de.rightExpression)
        if (mask != null && mask.size() == alt.size()) {
            List<Expression> gargs = new ArrayList<Expression>()
            for (int i = 0; i < alt.size(); i++) {
                gargs.add(new ConstantExpression(i, true))
                gargs.add(rewriteChExpr(mask.get(i), rw))
            }
            MethodCallExpression guardedCall = new MethodCallExpression(
                new VariableExpression(Encoder.CHANNEL_SELECT_MARKER), 'guarded', new ArgumentListExpression(gargs))
            guardedCall.setSourcePosition(de)
            DeclarationExpression dg = new DeclarationExpression(new VariableExpression(name + '$index'),
                Token.newSymbol(Types.ASSIGN, de.lineNumber, de.columnNumber), guardedCall)
            dg.setSourcePosition(de)
            rw.emit(out, new ExpressionStatement(dg))
            rw.selectVars.add(name)
            return
        }
        List<Expression> idx = new ArrayList<Expression>()
        List<Expression> valueArgs = new ArrayList<Expression>()
        String indexName = name + '$index', valueName = name + '$value'
        valueArgs.add(new VariableExpression(indexName))
        AltInfo info = new AltInfo()
        info.name = name
        for (int i = 0; i < alt.size(); i++) {
            String base = chanBaseVar(alt.get(i), rw)
            if (base == null) continue
            String root = rw.rootOf(base)
            Integer seen = rw.recvIdx.get(rw.streamOf(base))
            int k = (seen == null ? 0 : seen) + 1
            if (k > rw.total(root)) continue                              // nothing left on this branch: never ready
            String elem = rw.element(root, k)
            rw.registerType(root, elem)
            if (!rw.scalarTypes.containsKey(valueName)) rw.registerType(root, valueName)
            Expression head = rw.withElement(root, elem) { rewriteChExpr(alt.get(i), rw) }
            idx.add(new ConstantExpression(i, true))
            valueArgs.add(new ConstantExpression(i, true))
            valueArgs.add(head)
            info.branches.add(i); info.elems.add(elem); info.heads.add(head)
        }
        VariableExpression marker = new VariableExpression(Encoder.CHANNEL_SELECT_MARKER)
        MethodCallExpression indexCall = new MethodCallExpression(marker, 'index', new ArgumentListExpression(idx))
        indexCall.setSourcePosition(de)
        DeclarationExpression d1 = new DeclarationExpression(new VariableExpression(indexName),
            Token.newSymbol(Types.ASSIGN, de.lineNumber, de.columnNumber), indexCall)
        d1.setSourcePosition(de)
        rw.selectInfo.put(out.size(), info)
        rw.emit(out, new ExpressionStatement(d1))
        if (!idx.isEmpty()) {
            MethodCallExpression valueCall = new MethodCallExpression(marker, 'value', new ArgumentListExpression(valueArgs))
            valueCall.setSourcePosition(de)
            DeclarationExpression d2 = new DeclarationExpression(new VariableExpression(valueName),
                Token.newSymbol(Types.ASSIGN, de.lineNumber, de.columnNumber), valueCall)
            d2.setSourcePosition(de)
            rw.selectInfo.put(out.size(), info)
            rw.emit(out, new ExpressionStatement(d2))
        }
        rw.selectVars.add(name)
    }

    /** The channel arguments of a `ChannelSelect.from(c0, c1, …)` call (either post-STC shape), else null. */
    /** Phase 273 — the variable name a select argument names, for the positional-agreement check. */
    static String chanNameOf(Expression e) {
        Expression x = stripCasts(e)
        x instanceof VariableExpression ? ((VariableExpression) x).name : null
    }

    static List<Expression> selectFromArgs(Expression e) {
        Expression x = stripCasts(e)
        Expression args = null
        if (x instanceof StaticMethodCallExpression) {
            StaticMethodCallExpression sm = (StaticMethodCallExpression) x
            if (sm.method == 'from' && sm.ownerType?.nameWithoutPackage == 'ChannelSelect') args = sm.arguments
        } else if (x instanceof MethodCallExpression) {
            MethodCallExpression m = (MethodCallExpression) x
            if (m.methodAsString == 'from' && channelOwnerName(m.objectExpression) == 'ChannelSelect') args = m.arguments
        }
        if (args instanceof TupleExpression) return ((TupleExpression) args).expressions
        null
    }

    /** `await ChannelSelect.from(c…).select()` → the channel arguments; any other expression → null. */
    /** Phase 275 — the precondition flags of an awaited `…select(m0, m1, …)` (GROOVY-12324), else null.
     *  One flag per offer, in offer order; a bare `select()` has none. */
    static List<Expression> awaitedSelectMask(Expression rhs) {
        MethodCallExpression sel = awaitedSelectCall(rhs)     // one matcher, not a parallel one
        if (sel == null) return null
        Expression args = sel.arguments
        if (!(args instanceof TupleExpression)) return null
        List<Expression> flags = ((TupleExpression) args).expressions
        flags.isEmpty() ? null : flags
    }

    static List<Expression> awaitedSelectArgs(Expression rhs) { awaitedSelectArgs(rhs, null) }

    static List<Expression> awaitedSelectArgs(Expression rhs, Map<String, SelectRef> selectVars) {
        SelectRef r = awaitedSelect(rhs, selectVars)
        r == null ? null : r.chans
    }

    /** Phase 247 — `for (v in ch) { body }` over a channel with k known sends becomes k copies of the
     *  body, the i-th with `v` bound to the i-th element (through any map stages) and the body's own
     *  locals renamed apart. Exact for the drain of a closed bounded stream; the drain's blocking
     *  (until close) is certified separately by the Phase 245 wait-for analysis on the original body. */
    static void unrollChannelDrain(ForStatement st, ChanRewrite rw, List<Statement> out) {
        Expression coll = stripCasts(st.collectionExpression)
        String base = chanBaseVar(coll, rw)
        if (base == null) { rw.emit(out, st); return }
        String root = rw.rootOf(base)
        int n = rw.total(root)
        Parameter loopVar = st.variable
        Set<String> bodyLocals = new HashSet<String>()
        collectBodyLocalNames(st.loopBlock instanceof BlockStatement ? (BlockStatement) st.loopBlock :
            new BlockStatement(Collections.singletonList(st.loopBlock), null), bodyLocals)
        for (int i = 1; i <= n; i++) {
            Expression elem = rw.withElement(root, rw.element(root, i)) { rewriteChExpr(coll, rw) }
            String vi = loopVar.name + '$' + i
            if (coll instanceof VariableExpression) rw.registerType(root, vi)
            else if (!ClassHelper.isDynamicTyped(loopVar.type) && isNonIntScalar(loopVar.type) && !rw.scalarTypes.containsKey(vi)) {
                rw.scalarTypes.put(vi, loopVar.type)
            }
            VariableExpression lhs = new VariableExpression(vi, loopVar.type)
            DeclarationExpression decl = new DeclarationExpression(lhs, Token.newSymbol(Types.ASSIGN, st.lineNumber, st.columnNumber), elem)
            decl.setSourcePosition(st)
            rw.emit(out, new ExpressionStatement(decl))
            Map<String, Expression> ren = new HashMap<String, Expression>()
            ren.put(loopVar.name, new VariableExpression(vi))
            for (String l : bodyLocals) ren.put(l, new VariableExpression(l + '$' + i))
            Statement copy = copyRenamed(st.loopBlock, ren)
            if (copy == null) { rw.emit(out, st); return }    // guarded by unrollableLoopBody; defensive
            rewriteChStatements(copy instanceof BlockStatement ? ((BlockStatement) copy).statements : Collections.singletonList(copy), rw, out)
        }
    }

    /** A deep copy of a loop body with variables substituted — a rename (to a fresh `VariableExpression`)
     *  or a frozen literal index (Phase 248) — declarations included; null for a statement kind outside
     *  the unrolling fragment. Source positions are kept for diagnostics. */
    static Statement copyRenamed(Statement s, Map<String, Expression> ren) { copyRenamed(s, ren, false) }

    /** As above; {@code lenient} keeps a statement kind outside the copying fragment SHARED (unrenamed) instead of
     *  failing — for the arm renamer, whose live closures carry groovy-contracts' runtime-check plumbing. */
    static Statement copyRenamed(Statement s, Map<String, Expression> ren, boolean lenient) {
        if (s == null) return null
        ExpressionTransformer sub = new ExpressionTransformer() {
            @Override Expression transform(Expression expr) {
                if (expr instanceof VariableExpression && ren.containsKey(((VariableExpression) expr).name)) {
                    VariableExpression ve = (VariableExpression) expr
                    Expression rep = ren.get(ve.name)
                    Expression r = rep instanceof VariableExpression ?
                        new VariableExpression(((VariableExpression) rep).name, ve.originType) :
                        new ConstantExpression(((ConstantExpression) rep).value, true)
                    r.setSourcePosition(ve)
                    return r
                }
                if (expr == null) return null
                Expression t = expr.transformExpression(this)
                if (!t.is(expr)) t.setSourcePosition(expr)
                t
            }
        }
        Statement out
        if (s instanceof EmptyStatement) return s
        if (s instanceof BlockStatement) {
            List<Statement> o = new ArrayList<Statement>()
            for (Statement st : ((BlockStatement) s).statements) {
                Statement c = copyRenamed(st, ren, lenient)
                if (c == null) return null
                o.add(c)
            }
            out = new BlockStatement(o, ((BlockStatement) s).variableScope)
        } else if (s instanceof ExpressionStatement) {
            out = new ExpressionStatement(sub.transform(((ExpressionStatement) s).expression))
        } else if (s instanceof ReturnStatement) {
            Expression r = ((ReturnStatement) s).expression
            out = new ReturnStatement(r == null ? null : sub.transform(r))
        } else if (s instanceof IfStatement) {
            IfStatement i = (IfStatement) s
            Statement a = copyRenamed(i.ifBlock, ren, lenient)
            Statement b = i.elseBlock == null ? null : copyRenamed(i.elseBlock, ren, lenient)
            if (a == null || (i.elseBlock != null && b == null)) return null
            out = new IfStatement(new BooleanExpression(sub.transform(i.booleanExpression.expression)), a, b == null ? EmptyStatement.INSTANCE : b)
        } else if (s instanceof ForStatement) {                    // Phase 248 — a nested loop travels with its copy
            ForStatement f = (ForStatement) s
            Statement lb = copyRenamed(f.loopBlock, ren, lenient)
            if (lb == null) return null
            out = new ForStatement(f.variable, sub.transform(f.collectionExpression), lb)
        } else if (s instanceof WhileStatement) {                  // Phase 252 — arm loops rename with their spec
            WhileStatement w = (WhileStatement) s
            Statement lb = copyRenamed(w.loopBlock, ren, lenient)
            if (lb == null) return null
            out = new WhileStatement(new BooleanExpression(sub.transform(w.booleanExpression.expression)), lb)
        } else if (s instanceof DoWhileStatement) {
            DoWhileStatement w = (DoWhileStatement) s
            Statement lb = copyRenamed(w.loopBlock, ren, lenient)
            if (lb == null) return null
            out = new DoWhileStatement(new BooleanExpression(sub.transform(w.booleanExpression.expression)), lb)
        } else if (s instanceof AssertStatement) {
            AssertStatement a = (AssertStatement) s
            out = new AssertStatement(new BooleanExpression(sub.transform(a.booleanExpression.expression)), a.messageExpression)
            out.copyNodeMetaData(s)
        } else {
            return lenient ? s : null
        }
        if (s instanceof LoopingStatement) {
            out.copyNodeMetaData(s)
            LoopSpec spec = (LoopSpec) s.getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY)
            if (spec != null) out.putNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY, renameSpec(spec, ren))
        }
        out.setSourcePosition(s)
        out
    }

    /** Phase 252 — a LoopSpec with its expressions and statements renamed (the loop-engine view of a renamed loop). */
    static LoopSpec renameSpec(LoopSpec spec, Map<String, Expression> ren) {
        LoopSpec s2 = new LoopSpec()
        s2.invariants = new ArrayList<Expression>()
        for (Expression inv : spec.invariants) s2.invariants.add(substituteVars(inv, ren))
        s2.variant = spec.variant == null ? null : substituteVars(spec.variant, ren)
        s2.guard = spec.guard == null ? null : substituteVars(spec.guard, ren)
        s2.init = spec.init == null ? null : spec.init.collect { Statement x -> copyRenamed(x, ren) ?: x }
        s2.body = spec.body.collect { Statement x -> copyRenamed(x, ren) ?: x }
        Expression fv = spec.forInVar == null ? null : ren.get(spec.forInVar)
        s2.forInVar = fv instanceof VariableExpression ? ((VariableExpression) fv).name : spec.forInVar
        s2.forInBind = spec.forInBind == null ? null : (copyRenamed(spec.forInBind, ren) ?: spec.forInBind)
        s2.isDoWhile = spec.isDoWhile; s2.autoInvariantOnly = spec.autoInvariantOnly
        s2
    }

    /** The channel VAR an expression's chain bottoms out at, expanding derived vars through their
     *  recorded definitions — the direct var for {@code branch1.first()}, the derived var's own name
     *  for a receive on it (its stream/root are resolved via the parent map). */
    static String chanBaseVar(Expression e, ChanRewrite rw) {
        Expression x = stripCasts(e)
        while (x instanceof MethodCallExpression && ((MethodCallExpression) x).methodAsString in CHANNEL_PIPE_OPS) {
            x = stripCasts(((MethodCallExpression) x).objectExpression)
        }
        (x instanceof VariableExpression && rw.ch.contains(((VariableExpression) x).name)) ? ((VariableExpression) x).name : null
    }

    /** Resolve a channel-valued expression to its scalar value: expand a pipeline-derived var to its recorded
     *  definition, beta-reduce each `map { f }` over its upstream value, and read receives / drains as the
     *  indexed elements (Phase 247). */
    static Expression rewriteChExpr(Expression e, ChanRewrite rw) {
        if (e == null) return e
        Set<String> ch = rw.ch
        ExpressionTransformer t = new ExpressionTransformer() {
            @Override Expression transform(Expression expr) {
                if (expr instanceof PropertyExpression || expr instanceof MethodCallExpression) {   // Phase 259 — `c.taken`
                    Expression g = takenGhostRewrite(expr, rw)
                    if (g instanceof VariableExpression && (((VariableExpression) g).name.endsWith('$taken') || ((VariableExpression) g).name.endsWith('$q'))) return g
                }
                if (expr instanceof PropertyExpression) {                 // Phase 249 — r.index / r.value
                    PropertyExpression pe = (PropertyExpression) expr
                    Expression obj = stripCasts(pe.objectExpression)
                    if (obj instanceof VariableExpression && rw.selectVars.contains(((VariableExpression) obj).name) &&
                        (pe.propertyAsString == 'index' || pe.propertyAsString == 'value')) {
                        VariableExpression ve = new VariableExpression(((VariableExpression) obj).name + '$' + pe.propertyAsString)
                        ve.setSourcePosition(expr)
                        return ve
                    }
                }
                if (expr instanceof MethodCallExpression) {                   // Phase 249 — r.getIndex() / r.getValue()
                    MethodCallExpression gm = (MethodCallExpression) expr
                    Expression obj = stripCasts(gm.objectExpression)
                    if (obj instanceof VariableExpression && rw.selectVars.contains(((VariableExpression) obj).name) && noArgs(gm) &&
                        (gm.methodAsString == 'getIndex' || gm.methodAsString == 'getValue')) {
                        VariableExpression ve = new VariableExpression(((VariableExpression) obj).name + '$' + (gm.methodAsString == 'getIndex' ? 'index' : 'value'))
                        ve.setSourcePosition(expr)
                        return ve
                    }
                }
                if (expr instanceof VariableExpression) {
                    String name = ((VariableExpression) expr).name
                    if (rw.defs.containsKey(name)) return transform(rw.defs.get(name))   // expand derived var lazily
                    if (rw.subRoot != null && name == rw.subRoot) {                    // the element flowing through
                        VariableExpression ve = new VariableExpression(rw.subName)
                        ve.setSourcePosition(expr)
                        return ve
                    }
                    return expr
                }
                if (expr instanceof MethodCallExpression) {
                    MethodCallExpression m = (MethodCallExpression) expr
                    if (m.methodAsString == 'map' && isChannelExpr(m.objectExpression, ch)) {
                        ClosureExpression cl = singleClosureArg(m)
                        if (cl != null) {
                            Expression reduced = betaReduce(cl, transform(m.objectExpression))
                            if (reduced != null) return reduced
                        }
                    }
                    Expression cr = consumerRead(m, rw)                                  // Phase 252 — x$q[i - a]
                    if (cr != null) return cr
                    if (m.methodAsString == 'await' && isAwaitedReceive(m.arguments)) {
                        Expression cr2 = consumerRead((MethodCallExpression) singleArg(m.arguments), rw)
                        if (cr2 != null) return cr2
                    }
                    if ((m.methodAsString == 'first' || m.methodAsString == 'receive') &&
                        isChannelExpr(m.objectExpression, ch) && noArgs(m)) {
                        Expression r = receiveElement(m.objectExpression)                 // the k-th element
                        if (r != null) return r
                    }
                    if (m.methodAsString == 'await' && isAwaitedReceive(m.arguments)) {  // await ch.receive()
                        Expression r = receiveElement(((MethodCallExpression) singleArg(m.arguments)).objectExpression)
                        if (r != null) return r
                    }
                    // Phase 241 — a broadcast `subscribe()` is the identity stage for the element flowing
                    // through: every subscriber's channel carries every sent element. (`subscribe(int)`'s
                    // capacity arg is irrelevant here.)
                    if (m.methodAsString == 'subscribe' && isChannelExpr(m.objectExpression, ch)) {
                        return transform(m.objectExpression)
                    }
                    // Phase 251 — drains of a streaming channel read its shadow list.
                    Expression sobj = stripCasts(m.objectExpression)
                    String sq = sobj instanceof VariableExpression ? rw.streamListOf(((VariableExpression) sobj).name) : null
                    if (sq != null && (m.methodAsString == 'toList' || m.methodAsString == 'collect')) {
                        VariableExpression lv = new VariableExpression(sq, INT_LIST_TYPE)
                        lv.setSourcePosition(m)
                        if (m.methodAsString == 'toList') return lv
                        MethodCallExpression nc = new MethodCallExpression(lv, 'collect', m.arguments)
                        nc.setSourcePosition(m)
                        return nc
                    }
                    // Phase 247 — drains over the whole known sequence.
                    if (m.methodAsString == 'toList' && isChannelExpr(m.objectExpression, ch) && noArgs(m)) {
                        List<Expression> elems = elementsOf(m.objectExpression)
                        if (elems != null) { ListExpression le = new ListExpression(elems); le.setSourcePosition(m); return le }
                    }
                    if (m.methodAsString == 'collect' && isChannelExpr(m.objectExpression, ch)) {
                        ClosureExpression cl = singleClosureArg(m)
                        List<Expression> elems = cl == null ? null : elementsOf(m.objectExpression)
                        if (elems != null) {
                            List<Expression> mapped = new ArrayList<Expression>()
                            for (Expression x : elems) {
                                Expression y = betaReduce(cl, x)
                                if (y == null) { mapped = null; break }
                                mapped.add(y)
                            }
                            if (mapped != null) { ListExpression le = new ListExpression(mapped); le.setSourcePosition(m); return le }
                        }
                    }
                }
                if (expr instanceof StaticMethodCallExpression) {
                    StaticMethodCallExpression sm = (StaticMethodCallExpression) expr
                    if (sm.method == 'await' && isAwaitedReceive(sm.arguments)) {
                        Expression cr = consumerRead((MethodCallExpression) singleArg(sm.arguments), rw)   // Phase 252
                        if (cr != null) return cr
                        Expression r = receiveElement(((MethodCallExpression) singleArg(sm.arguments)).objectExpression)
                        if (r != null) return r
                    }
                }
                expr.transformExpression(this)
            }
            private boolean isAwaitedReceive(Expression args) {
                Expression a = singleArg(args)
                a instanceof MethodCallExpression && ((MethodCallExpression) a).methodAsString == 'receive' &&
                    noArgs((MethodCallExpression) a) && isChannelExpr(((MethodCallExpression) a).objectExpression, ch)
            }
            private Expression singleArg(Expression args) {
                if (!(args instanceof ArgumentListExpression)) return null
                List<Expression> a = ((ArgumentListExpression) args).expressions
                a.size() == 1 ? stripCasts(a.get(0)) : null
            }
            /** The next element of the stream this receiver consumes, run through its stages. */
            private Expression receiveElement(Expression recv) {
                String base = chanBaseVar(recv, rw)
                if (base == null) return null
                String root = rw.rootOf(base)
                String elem = rw.element(root, rw.next(rw.recvIdx, rw.streamOf(base)))
                rw.registerType(root, elem)
                rw.withElement(root, elem) { transform(recv) }
            }
            /** Every element of the (closed, bounded) stream, each through its stages. */
            private List<Expression> elementsOf(Expression recv) {
                String base = chanBaseVar(recv, rw)
                if (base == null) return null
                String root = rw.rootOf(base)
                List<Expression> elems = new ArrayList<Expression>()
                for (int i = 1; i <= rw.total(root); i++) {
                    String elem = rw.element(root, i)
                    rw.registerType(root, elem)
                    elems.add(rw.withElement(root, elem) { transform(recv) })
                }
                elems
            }
        }
        t.transform(e)
    }

    static ClosureExpression singleClosureArg(MethodCallExpression m) {
        if (!(m.arguments instanceof ArgumentListExpression)) return null
        List<Expression> a = ((ArgumentListExpression) m.arguments).expressions
        (a.size() == 1 && a.get(0) instanceof ClosureExpression) ? (ClosureExpression) a.get(0) : null
    }

    /** β-reduce a single-expression closure `{ p -> body }` over {@code arg}: substitute the closure's parameter
     *  (or implicit `it`) with {@code arg} in {@code body}. Returns null for an unsupported (multi-statement) shape. */
    static Expression betaReduce(ClosureExpression cl, Expression arg) {
        Expression bodyE = null
        if (cl.code instanceof BlockStatement) {
            List<Statement> ss = ((BlockStatement) cl.code).statements
            if (ss.size() == 1 && ss.get(0) instanceof ExpressionStatement) bodyE = ((ExpressionStatement) ss.get(0)).expression
            else if (ss.size() == 1 && ss.get(0) instanceof ReturnStatement) bodyE = ((ReturnStatement) ss.get(0)).expression
        }
        if (bodyE == null) return null
        String p = (cl.parameters != null && cl.parameters.length > 0) ? cl.parameters[0].name : 'it'
        ExpressionTransformer sub = new ExpressionTransformer() {
            @Override Expression transform(Expression expr) {
                if (expr instanceof VariableExpression && ((VariableExpression) expr).name == p) return arg
                expr.transformExpression(this)
            }
        }
        sub.transform(bodyE)
    }

    // ── Phase 251 — symbolic streaming: the channel as the sequence its producer loop builds ───
    //
    // The value half of the streaming frontier. A channel whose ONLY send is the one send statement
    // of a unit-counter loop carrying a LoopSpec (the user's @Invariant/@Decreases) is modelled as a
    // LIST the loop builds: `def c = create()` → `List<Integer> c$q = []`, `c.send(E)` → `c$q.add(E)`,
    // a map-derived stage `d = c.map { f }` → `d$q.add(f(E))` in lockstep (stage fusion — exact for a
    // pure per-element transform), `c.toList()` → `c$q`, `c.close()` → the `c$closed` marker the
    // scheduler orders drains behind. The sequence facts are INJECTED into the loop's spec, so the
    // user never names the shadow list: `c$q != null && c$q.size() == i - a` (a the counter's value at
    // entry — a literal or a parameter expression; a prefix ghost would be havoced by the loop VCs)
    // and, when the sent expression depends only on the counter and loop-constant names, the element
    // relation `Forall.range(0, c$q.size(), { k -> c$q[k] == E[i := a + k] })`. Everything else stays
    // the loop engine's own proof: the user's invariant carries `0 <= i <= n`, the loop VCs verify the
    // body (send-side contract asserts included), and the drained list's claims follow.
    // Honest boundaries: int elements; one send per iteration, unconditional, at the loop body's top
    // level; no one-at-a-time receive on a streaming channel (use a drain); a for-in drain of the list
    // is the loop engine's "nested loop writes a collection" skip — `toList()` is the drained-value
    // spelling; a counter-less loop, a second send, a subscribe/filter stage all refuse, named.

    /** A streaming channel and the loop that produces it. */
    static class StreamInfo {
        String root
        LoopingStatement loop
        MethodCallExpression sendCall
        Expression sendExpr
        String counter
        Expression counterInit
        boolean elementRelation
        final List<String> derived = new ArrayList<String>()
        final Map<String, MethodCallExpression> aliases = new HashMap<String, MethodCallExpression>()   // Phase 252 — `def v = in.first()` in the same loop
        boolean infinite                                                     // Phase 254 — produced by a `while (true)`
        int pre                                                              // Phase 255 — priming sends before the loop, same process
        final List<Expression> preValues = new ArrayList<Expression>()       // their sent expressions, in order
        boolean conditional                                                  // Phase 258 — a guarded reply: sent once per choice of one ALT branch
        String condChan                                                      // that branch's stream var (its cursor counts the elements)
        int condBranch
        String valueAlias                                                    // `T q = (cast) r.value` in the same body, if any
    }

    /** Phase 252 — a consumer loop: a specified unit-counter loop reading one element per iteration from
     *  a streaming channel (or its map stage) — the k-th receive reads element k of the shadow list. */
    static class ConsumerInfo {
        LoopingStatement loop
        String counter
        Expression counterInit
        final Map<MethodCallExpression, String> receives = new IdentityHashMap<MethodCallExpression, String>()   // call → stream var
        final Set<String> chans = new HashSet<String>()                  // the stream vars read (one receive each per iteration)
        String altVar                                                    // Phase 253 — the loop's ALT result var (at most one ALT per iteration)
        final Map<String, Integer> guardedSends = new HashMap<String, Integer>()   // Phase 256 — `if (r.index == i) X.send(..)`: channel → branch
        final Map<String, MethodCallExpression> guardedSendCalls = new HashMap<String, MethodCallExpression>()   // Phase 258 — the calls
        final List<String> altChans = new ArrayList<String>()            // its branches (stream vars), in from() order
        Expression altFrom                                               // the select() call (identity, for the walks)
        String altPolicy = 'priority'                                    // Phase 257 — priority | fair | random
        boolean altHeld                                                  // Phase 257 — a held instance (rotation state kept)
        /** The stream var a call receives from — by SHAPE (`x.first()` / `x.receive()`), so a copied body still matches. */
        String readOf(MethodCallExpression m) {
            if (!(m.methodAsString == 'first' || m.methodAsString == 'receive') || !noArgs(m)) return null
            Expression x = stripCasts(m.objectExpression)
            String v = x instanceof VariableExpression ? ((VariableExpression) x).name : null
            (v != null && chans.contains(v)) ? v : null
        }
    }

    /** A loop-send's eligibility verdicts: streaming roots, and the reason each other loop-send channel is out. */
    static class StreamScan {
        final Map<String, StreamInfo> streams = new LinkedHashMap<String, StreamInfo>()
        final Map<String, String> whyNot = new LinkedHashMap<String, String>()
        final Set<Expression> sanctionedSends = Collections.newSetFromMap(new IdentityHashMap<Expression, Boolean>())
        final Map<Statement, ConsumerInfo> consumers = new IdentityHashMap<Statement, ConsumerInfo>()
        final Set<Expression> sanctionedReceives = Collections.newSetFromMap(new IdentityHashMap<Expression, Boolean>())
        final Set<Expression> sanctionedFroms = Collections.newSetFromMap(new IdentityHashMap<Expression, Boolean>())   // Phase 253 — now the select() calls
        Map<String, SelectRef> selectRefs = new HashMap<String, SelectRef>()      // Phase 257
        /** Phase 258 — a consumer loop → the roots it reads from loops in a CYCLE with it (read through rely views). */
        final Map<Statement, Set<String>> partnerStreams = new IdentityHashMap<Statement, Set<String>>()
        /** Phase 258 — a loop → the other loops of its cycle (their invariants are what a rely instantiates). */
        final Map<Statement, List<Statement>> cycleOf = new IdentityHashMap<Statement, List<Statement>>()
        String streamVarRoot(String v, Map<String, String> parent) {
            String r = v; int g = 0
            while (parent.containsKey(r) && g++ < 100) r = parent.get(r)
            StreamInfo info = streams.get(r)
            (info != null && (v == r || info.derived.contains(v))) ? r : null
        }
    }

    /** Top-level statement lists of the body and of each async arm (the flattening puts them all at top level). */
    static List<List<Statement>> topLevelBlocks(BlockStatement body) {
        List<List<Statement>> out = new ArrayList<List<Statement>>()
        out.add(body.statements)
        for (Statement st : body.statements) {
            if (!(st instanceof ExpressionStatement)) continue
            Expression e = ((ExpressionStatement) st).expression
            if (e instanceof DeclarationExpression) e = stripCasts(((DeclarationExpression) e).rightExpression)
            else if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.ASSIGN) e = stripCasts(((BinaryExpression) e).rightExpression)
            ClosureExpression cl = asyncClosure(e)
            if (cl != null && cl.code instanceof BlockStatement) out.add(((BlockStatement) cl.code).statements)
        }
        out
    }

    static MethodCallExpression sendCallOf(Statement st, Set<String> ch) {
        if (!(st instanceof ExpressionStatement)) return null
        Expression e = ((ExpressionStatement) st).expression
        if (!(e instanceof MethodCallExpression) || ((MethodCallExpression) e).methodAsString != 'send') return null
        Expression recv = stripCasts(((MethodCallExpression) e).objectExpression)
        (recv instanceof VariableExpression && ch.contains(((VariableExpression) recv).name)) ? (MethodCallExpression) e : null
    }

    /** The unit counter of a loop — `i` with exactly one `i = i + 1` / `i++` / `i += 1` per iteration — with its
     *  entry value from the enclosing block; `[name, initExpr]`, or null (with a reason in {@code why}). */
    static Object[] unitCounter(LoopingStatement loop, List<Statement> enclosing, Set<String> params, String[] why) {
        String counter = null
        Expression init = null
        Statement body = loop.loopBlock
        List<Statement> top = body instanceof BlockStatement ? ((BlockStatement) body).statements : Collections.singletonList(body)
        if (loop instanceof ForStatement) {
            ForStatement f = (ForStatement) loop
            if (!(f.collectionExpression instanceof ClosureListExpression)) { why[0] = 'is a for-in (the streaming model takes a while / C-style unit-counter loop)'; return null }
            List<Expression> parts = ((ClosureListExpression) f.collectionExpression).expressions
            if (parts.size() != 3) { why[0] = 'is not a three-part C-style loop'; return null }
            Expression initE = stripCasts(parts.get(0)), upd = stripCasts(parts.get(2))
            if (!(initE instanceof DeclarationExpression) || !(((DeclarationExpression) initE).leftExpression instanceof VariableExpression)) { why[0] = 'has no unit counter (int i = a; …; i++)'; return null }
            counter = ((VariableExpression) ((DeclarationExpression) initE).leftExpression).name
            init = ((DeclarationExpression) initE).rightExpression
            if (!isUnitIncrement(upd, counter)) { why[0] = "does not step its counter '${counter}' by one"; return null }
            if (writesVar(body, counter)) { why[0] = "writes its counter '${counter}' in the body"; return null }
        } else if (loop instanceof WhileStatement) {
            Set<String> guardNames = varNames(((WhileStatement) loop).booleanExpression)
            boolean forever = isForever(loop)                                // Phase 254 — `while (true)`: no guard to test
            for (Statement st : top) {
                if (!(st instanceof ExpressionStatement)) continue
                Expression e = ((ExpressionStatement) st).expression
                String v = unitIncrementTarget(e)
                if (v == null || (!forever && !guardNames.contains(v))) continue   // the counter is the stepped var the guard tests
                if (counter != null) { why[0] = forever ? 'steps two counters (a while (true) needs exactly one)' : 'steps two guard counters'; return null }
                counter = v
            }
            if (counter == null) { why[0] = 'has no unit counter (a single i = i + 1 per iteration on a variable the guard tests)'; return null }
            int writes = 0
            for (Statement st : top) if (writesVar(st, counter)) writes++
            if (writes != 1) { why[0] = "writes its counter '${counter}' more than once per iteration"; return null }
            // the counter's value at entry: the last statement writing it before the loop, a plain declaration / assignment
            int at = -1
            for (int i = 0; i < enclosing.size(); i++) if (enclosing.get(i).is(loop)) at = i
            for (int i = at - 1; i >= 0 && init == null; i--) {
                Statement st = enclosing.get(i)
                if (!writesVar(st, counter)) continue
                if (st instanceof ExpressionStatement) {
                    Expression e = ((ExpressionStatement) st).expression
                    if (e instanceof DeclarationExpression && ((DeclarationExpression) e).leftExpression instanceof VariableExpression &&
                        ((VariableExpression) ((DeclarationExpression) e).leftExpression).name == counter) init = ((DeclarationExpression) e).rightExpression
                    else if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.ASSIGN &&
                        ((BinaryExpression) e).leftExpression instanceof VariableExpression &&
                        ((VariableExpression) ((BinaryExpression) e).leftExpression).name == counter) init = ((BinaryExpression) e).rightExpression
                }
                if (init == null) { why[0] = "has a counter '${counter}' whose entry value is not a plain assignment"; return null }
            }
            if (init == null) { why[0] = "has a counter '${counter}' with no entry value in the enclosing block"; return null }
        } else {
            why[0] = 'is a do-while (its body runs before the first check)'
            return null
        }
        if (!(stripCasts(init) instanceof ConstantExpression) && !namesWithin(init, params)) {
            why[0] = "has a counter '${counter}' whose entry value is neither a literal nor a parameter expression"
            return null
        }
        [counter, init] as Object[]
    }

    static boolean isUnitIncrement(Expression e, String v) { unitIncrementTarget(e) == v }

    /** Phase 254 — `while (true)`: the non-terminating process's loop. */
    static boolean isForever(LoopingStatement loop) {
        if (!(loop instanceof WhileStatement)) return false
        Expression g = stripCasts(((WhileStatement) loop).booleanExpression.expression)
        g instanceof ConstantExpression && Boolean.TRUE.equals(((ConstantExpression) g).value)
    }

    /** `i++` / `++i` / `i += 1` / `i = i + 1` → `i`; else null. */
    static String unitIncrementTarget(Expression e) {
        Expression x = stripCasts(e)
        if (x instanceof PostfixExpression && ((PostfixExpression) x).operation.type == Types.PLUS_PLUS && ((PostfixExpression) x).expression instanceof VariableExpression)
            return ((VariableExpression) ((PostfixExpression) x).expression).name
        if (x instanceof PrefixExpression && ((PrefixExpression) x).operation.type == Types.PLUS_PLUS && ((PrefixExpression) x).expression instanceof VariableExpression)
            return ((VariableExpression) ((PrefixExpression) x).expression).name
        if (x instanceof BinaryExpression) {
            BinaryExpression b = (BinaryExpression) x
            if (!(b.leftExpression instanceof VariableExpression)) return null
            String v = ((VariableExpression) b.leftExpression).name
            Integer one = intLiteral(b.rightExpression)
            if (b.operation.type == Types.PLUS_EQUAL && one != null && one == 1) return v
            if (b.operation.type == Types.ASSIGN && b.rightExpression instanceof BinaryExpression) {
                BinaryExpression r = (BinaryExpression) b.rightExpression
                if (r.operation.type == Types.PLUS && r.leftExpression instanceof VariableExpression &&
                    ((VariableExpression) r.leftExpression).name == v && intLiteral(r.rightExpression) != null && intLiteral(r.rightExpression) == 1) return v
            }
        }
        null
    }

    /** True when every variable named in {@code e} is in {@code names}. */
    static boolean namesWithin(Expression e, Set<String> names) {
        boolean[] ok = [true]
        e.visit(new CodeVisitorSupport() {
            @Override void visitVariableExpression(VariableExpression ve) { if (!names.contains(ve.name) && ve.name != 'this') ok[0] = false }
        })
        ok[0]
    }

    static Set<String> varNames(Expression e) {
        final Set<String> out = new HashSet<String>()
        e.visit(new CodeVisitorSupport() { @Override void visitVariableExpression(VariableExpression ve) { out.add(ve.name) } })
        out
    }

    /**
     * Phase 251 — the streaming scan: which channels are produced by one send in one specified
     * unit-counter loop (and are otherwise only drained), and why the other loop-send channels are out.
     */
    /** Phase 258 — the value alias of an ALT loop: `T q = (cast) r.value` at the body's top level, else null. */
    static String valueAliasOf(ConsumerInfo ci) {
        Statement lb = ci.loop.loopBlock
        List<Statement> top = lb instanceof BlockStatement ? ((BlockStatement) lb).statements : Collections.singletonList(lb)
        for (Statement st : top) {
            if (!(st instanceof ExpressionStatement) || !(((ExpressionStatement) st).expression instanceof DeclarationExpression)) continue
            DeclarationExpression de = (DeclarationExpression) ((ExpressionStatement) st).expression
            if (!(de.leftExpression instanceof VariableExpression)) continue
            Expression rhs = stripCasts(de.rightExpression)
            boolean isValue = (rhs instanceof PropertyExpression && ((PropertyExpression) rhs).propertyAsString == 'value' &&
                    stripCasts(((PropertyExpression) rhs).objectExpression) instanceof VariableExpression &&
                    ((VariableExpression) stripCasts(((PropertyExpression) rhs).objectExpression)).name == ci.altVar) ||
                (rhs instanceof MethodCallExpression && ((MethodCallExpression) rhs).methodAsString == 'getValue' && noArgs((MethodCallExpression) rhs) &&
                    stripCasts(((MethodCallExpression) rhs).objectExpression) instanceof VariableExpression &&
                    ((VariableExpression) stripCasts(((MethodCallExpression) rhs).objectExpression)).name == ci.altVar)
            if (isValue) return ((VariableExpression) de.leftExpression).name
        }
        null
    }

    /**
     * Phase 258 — a GUARDED REPLY as a conditional stream: `if (r.index == b) { Y.send(E) }` at the top level
     * of an ALT loop's body, the channel's only send. Y's element count is the chosen branch's cursor (one
     * element per choice of branch b), and its k-th element is E with the ALT's value standing for the k-th
     * element TAKEN from that branch (`X$taken[k]`) — the fair server's reply law, stated over the server's
     * own ghosts so a client can instantiate it (relyBlock) and close it against its own sent list.
     */
    static void guardedReplyStreams(StreamScan scan, Map<String, List<MethodCallExpression>> allSends, Set<String> ch,
                                            Map<String, String> parent, Set<String> subscribers, Map<String, ClassNode> scalarTypes) {
        for (ConsumerInfo ci : new ArrayList<ConsumerInfo>(scan.consumers.values())) {
            if (ci.altVar == null) continue
            String alias = valueAliasOf(ci)
            for (Map.Entry<String, MethodCallExpression> gs : ci.guardedSendCalls.entrySet()) {
                String c = gs.key
                MethodCallExpression call = gs.value
                if (scan.streams.containsKey(c)) continue
                List<MethodCallExpression> all = allSends.get(c)
                Integer branch = ci.guardedSends.get(c)
                List<Expression> a = (call.arguments instanceof TupleExpression) ? ((TupleExpression) call.arguments).expressions : Collections.<Expression>emptyList()
                String why = null
                if (all == null || all.size() != 1) why = "has ${all == null ? 0 : all.size() - 1} send(s) besides the one the ALT at line ${((Statement) ci.loop).lineNumber} guards (a guarded reply is one send per choice of its branch)".toString()
                else if (branch == null || branch < 0 || branch >= ci.altChans.size()) why = 'is guarded by an index outside the ALT\'s branches'
                else if (parent.containsKey(c) || subscribers.contains(c)) why = 'is a derived / subscriber channel (the streaming model is for a created channel)'
                else if (scalarTypes.containsKey(c)) why = 'has a non-int element type (the streaming model is int-element only)'
                else if (a.size() != 1) why = 'has a send that is not single-argument'
                if (why != null) { scan.whyNot.put(c, why); continue }
                StreamInfo info = new StreamInfo()
                info.root = c; info.loop = ci.loop; info.sendCall = call; info.sendExpr = a.get(0)
                info.counter = ci.counter; info.counterInit = ci.counterInit
                info.infinite = isForever(info.loop)
                info.conditional = true; info.condBranch = branch; info.condChan = ci.altChans.get(branch); info.valueAlias = alias
                boolean rel = true
                for (String n : varNames(info.sendExpr)) {
                    if (n == alias || n == ci.altVar) continue
                    if (ch.contains(n) || writesVar(info.loop.loopBlock, n)) rel = false
                }
                info.elementRelation = rel
                for (Map.Entry<String, String> pe : parent.entrySet()) {
                    String d = pe.key, r = d
                    int g = 0
                    while (parent.containsKey(r) && g++ < 100) r = parent.get(r)
                    if (r == c) info.derived.add(d)
                }
                scan.streams.put(c, info)
                scan.sanctionedSends.add(call)
                scan.whyNot.remove(c)
            }
        }
    }

    /**
     * Phase 261 — a FINITE producer loop's total element count as source text, from its guard: `counter < E`
     * gives `E - init`, `counter <= E` gives `E + 1 - init` (priming sends added), with E loop-constant; null when
     * the loop is a `while (true)` or the guard has another shape. What a reader in a cycle with it may assert
     * against: element k of the stream exists eventually iff k < total.
     */
    static String staticTotalText(StreamInfo info, Set<String> ch) {
        if (info.infinite) return null
        LoopSpec spec = (LoopSpec) ((Statement) info.loop).getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY)
        Expression g = spec == null ? null : spec.guard
        while (g instanceof BooleanExpression) g = ((BooleanExpression) g).expression
        g = stripCasts(g)
        if (!(g instanceof BinaryExpression)) return null
        BinaryExpression b = (BinaryExpression) g
        Expression l = stripCasts(b.leftExpression), r = stripCasts(b.rightExpression)
        int op = b.operation.type
        Expression bound = null
        boolean inclusive = false
        if (l instanceof VariableExpression && ((VariableExpression) l).name == info.counter && (op == Types.COMPARE_LESS_THAN || op == Types.COMPARE_LESS_THAN_EQUAL)) {
            bound = r; inclusive = op == Types.COMPARE_LESS_THAN_EQUAL
        } else if (r instanceof VariableExpression && ((VariableExpression) r).name == info.counter && (op == Types.COMPARE_GREATER_THAN || op == Types.COMPARE_GREATER_THAN_EQUAL)) {
            bound = l; inclusive = op == Types.COMPARE_GREATER_THAN_EQUAL
        }
        if (bound == null) return null
        for (String n : varNames(bound)) if (n == info.counter || ch.contains(n) || writesVar(info.loop.loopBlock, n)) return null
        String bt = bound instanceof VariableExpression || bound instanceof ConstantExpression ? bound.text : "(${bound.text})".toString()
        String init = entryText(info.counterInit)
        "${bt}${inclusive ? ' + 1' : ''} - ${init}${info.pre == 0 ? '' : ' + ' + info.pre}".toString()
    }

    /**
     * Phase 258 — CYCLES among the stream loops (a loop reads a stream produced by a loop that, directly or
     * through others, reads a stream it produces): the client–server pair, the ring, the fair server. The
     * flattened model runs each loop atomically in dataflow order, which no order of a cycle respects — so
     * a cycle member reads its partners' streams through RELY VIEWS instead (relyBlock). Every member must
     * be a `while (true)`: a partner that terminates has an exit fact no snapshot can carry.
     */
    static void computeCycles(StreamScan scan, Map<String, String> parent, Set<String> ch) {
        Map<Statement, Set<Statement>> succ = new IdentityHashMap<Statement, Set<Statement>>()
        List<Statement> loops = new ArrayList<Statement>()
        Closure<Object> node = { Statement l -> if (!loops.any { Statement x -> x.is(l) }) { loops.add(l); succ.put(l, Collections.newSetFromMap(new IdentityHashMap<Statement, Boolean>())) }; null }
        for (StreamInfo info : scan.streams.values()) node((Statement) info.loop)
        for (ConsumerInfo ci : scan.consumers.values()) {
            Statement l = (Statement) ci.loop
            node(l)
            List<String> vars = new ArrayList<String>(ci.receives.values()); vars.addAll(ci.altChans)
            for (String v : vars) {
                String root = scan.streamVarRoot(v, parent)
                StreamInfo p = root == null ? null : scan.streams.get(root)
                if (p == null || p.loop.is(l)) continue
                succ.get((Statement) p.loop).add(l)
            }
        }
        Map<Statement, Set<Statement>> reach = new IdentityHashMap<Statement, Set<Statement>>()
        for (Statement l : loops) {
            Set<Statement> r = Collections.newSetFromMap(new IdentityHashMap<Statement, Boolean>())
            List<Statement> todo = new ArrayList<Statement>(succ.get(l))
            while (!todo.isEmpty()) { Statement x = todo.remove(0); if (r.add(x)) todo.addAll(succ.get(x)) }
            reach.put(l, r)
        }
        Set<String> dropped = new HashSet<String>()
        for (ConsumerInfo ci : scan.consumers.values()) {
            Statement l = (Statement) ci.loop
            List<Statement> members = new ArrayList<Statement>()
            for (Statement m : loops) if (!m.is(l) && reach.get(l).contains(m) && reach.get(m).contains(l)) members.add(m)
            if (members.isEmpty()) continue
            List<String> vars = new ArrayList<String>(ci.receives.values()); vars.addAll(ci.altChans)
            Set<String> ps = new LinkedHashSet<String>()
            for (String v : vars) {
                String root = scan.streamVarRoot(v, parent)
                StreamInfo p = root == null ? null : scan.streams.get(root)
                if (p != null && members.any { Statement m -> m.is((Statement) p.loop) }) {
                    // Phase 261 — a FINITE partner is fine (a rely assumes append-stable facts only) provided its
                    // total is static: element k exists eventually iff k < total, which the reader must show.
                    if (!p.infinite && staticTotalText(p, ch) == null) { dropped.add(root); continue }
                    ps.add(root)
                }
            }
            scan.partnerStreams.put(l, ps)
            scan.cycleOf.put(l, members)
        }
        for (String root : dropped) {
            StreamInfo info = scan.streams.remove(root)
            if (info != null) scan.sanctionedSends.remove(info.sendCall)
            scan.whyNot.put(root, 'is read in a cycle from a terminating loop whose element count is not static (the reader must show it reads below the producer\'s total: a guard `counter < bound` with a loop-constant bound)')
        }
        if (!dropped.isEmpty()) {
            for (ConsumerInfo ci : new ArrayList<ConsumerInfo>(scan.consumers.values())) {
                for (Map.Entry<MethodCallExpression, String> e : new ArrayList<Map.Entry<MethodCallExpression, String>>(ci.receives.entrySet())) {
                    if (dropped.contains(scan.streamVarRoot(e.value, parent) ?: e.value) || !scan.streams.containsKey(scan.streamVarRoot(e.value, parent) ?: '')) {
                        scan.sanctionedReceives.remove(e.key); ci.receives.remove(e.key); ci.chans.remove(e.value)
                    }
                }
            }
        }
    }

    static StreamScan scanStreams(BlockStatement body, Set<String> ch, Map<String, String> parent,
                                          Set<String> subscribers, Set<String> params, Map<String, ClassNode> scalarTypes) {
        StreamScan scan = new StreamScan()
        scan.selectRefs = collectSelectVars(body)                             // Phase 257
        // every send, and the ones that sit at the top level of a specified top-level loop
        final Map<String, List<MethodCallExpression>> allSends = new HashMap<String, List<MethodCallExpression>>()
        body.visit(new CodeVisitorSupport() {
            @Override void visitMethodCallExpression(MethodCallExpression m) {
                Expression recv = stripCasts(m.objectExpression)
                if (m.methodAsString == 'send' && recv instanceof VariableExpression && ch.contains(((VariableExpression) recv).name)) {
                    String n = ((VariableExpression) recv).name
                    List<MethodCallExpression> l = allSends.get(n)
                    if (l == null) { l = new ArrayList<MethodCallExpression>(); allSends.put(n, l) }
                    l.add(m)
                }
                super.visitMethodCallExpression(m)
            }
        })
        Map<String, Object[]> loopSend = new HashMap<String, Object[]>()   // channel → [loop, enclosing block, call]
        for (List<Statement> block : topLevelBlocks(body)) {
            for (Statement st : block) {
                if (!(st instanceof LoopingStatement)) continue
                Statement lb = ((LoopingStatement) st).loopBlock
                List<Statement> top = lb instanceof BlockStatement ? ((BlockStatement) lb).statements : Collections.singletonList(lb)
                for (Statement inner : top) {
                    MethodCallExpression call = sendCallOf(inner, ch)
                    if (call != null) loopSend.put(((VariableExpression) stripCasts(call.objectExpression)).name, [st, block, call] as Object[])
                }
            }
        }
        for (Map.Entry<String, List<MethodCallExpression>> e : allSends.entrySet()) {
            String c = e.key
            boolean anyInLoop = false
            for (MethodCallExpression m : e.value) if (insideLoop(body, m)) anyInLoop = true
            if (!anyInLoop) continue                                   // one-shot traffic: Phase 247's model
            Object[] ls = loopSend.get(c)
            String why = null
            int pre = 0
            List<Expression> preValues = new ArrayList<Expression>()
            if (ls != null) {                                                 // Phase 255 — priming sends: one-shot, same process, before the loop
                List<Statement> blk = (List<Statement>) ls[1]
                for (Statement st : blk) {
                    if (st.is((Statement) ls[0])) break
                    MethodCallExpression pc = sendCallOf(st, ch)
                    if (pc != null && ((VariableExpression) stripCasts(pc.objectExpression)).name == c) {
                        pre++
                        List<Expression> pa = (pc.arguments instanceof TupleExpression) ? ((TupleExpression) pc.arguments).expressions : Collections.<Expression>emptyList()
                        preValues.add(pa.size() == 1 ? pa.get(0) : null)
                    }
                }
            }
            if (ls == null) why = 'has a loop send that is not at the top level of a top-level loop'
            else if (e.value.size() != 1 + pre) why = "has ${e.value.size() - 1 - pre} send(s) outside its producer loop and the one-shot priming sends before it (the streaming model takes exactly one send per iteration, plus priming sends in the same process)"
            else if (parent.containsKey(c) || subscribers.contains(c)) why = 'is a derived / subscriber channel (the streaming model is for a created channel)'
            else if (scalarTypes.containsKey(c)) why = 'has a non-int element type (the streaming model is int-element only)'
            if (why == null) {
                String[] w = [null]
                Object[] cnt = unitCounter((LoopingStatement) ls[0], (List<Statement>) ls[1], params, w)
                if (cnt == null) why = 'is produced by a loop that ' + w[0]
                else if (((Statement) ls[0]).getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY) == null) why = 'is produced by a loop without an @Invariant / @Decreases (the streaming model rides the loop specification)'
                else {
                    StreamInfo info = new StreamInfo()
                    info.root = c; info.loop = (LoopingStatement) ls[0]; info.sendCall = (MethodCallExpression) ls[2]
                    info.infinite = isForever(info.loop)
                    info.pre = pre
                    info.preValues.addAll(preValues)
                    List<Expression> a = (info.sendCall.arguments instanceof TupleExpression) ? ((TupleExpression) info.sendCall.arguments).expressions : Collections.<Expression>emptyList()
                    if (a.size() != 1) why = 'has a send that is not single-argument'
                    else {
                        info.sendExpr = a.get(0)
                        info.counter = (String) cnt[0]; info.counterInit = (Expression) cnt[1]
                        boolean rel = true
                        for (String n : varNames(info.sendExpr)) {
                            if (n == info.counter) continue
                            if (ch.contains(n) || writesVar(info.loop.loopBlock, n)) rel = false
                        }
                        info.elementRelation = rel
                        for (Map.Entry<String, String> pe : parent.entrySet()) {
                            String d = pe.key, r = d
                            int g = 0
                            while (parent.containsKey(r) && g++ < 100) r = parent.get(r)
                            if (r == c) info.derived.add(d)
                        }
                        scan.streams.put(c, info)
                        scan.sanctionedSends.add(info.sendCall)
                    }
                }
            }
            if (why != null) scan.whyNot.put(c, why)
        }
        // Phase 252 — consumer loops: a specified unit-counter loop whose body receives (first() / awaited
        // receive()) from a streaming channel or its map stage, at most once per channel per iteration,
        // unconditionally (not under an if / nested loop). Each such receive is sanctioned: the k-th
        // iteration reads element k of the shadow list, the block-forever obligation asserted before it.
        // Phase 258 — two passes: the first finds the ALT loops and their guarded replies, which then become
        // CONDITIONAL streams; the second sanctions the loops that read those replies.
        for (int pass = 0; pass < 2; pass++) {
        if (pass == 1) {
            guardedReplyStreams(scan, allSends, ch, parent, subscribers, scalarTypes)
            scan.consumers.clear(); scan.sanctionedReceives.clear(); scan.sanctionedFroms.clear()
        }
        for (List<Statement> block : topLevelBlocks(body)) {
            for (Statement st : block) {
                if (!(st instanceof LoopingStatement)) continue
                if (((Statement) st).getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY) == null) continue
                String[] w = [null]
                Object[] cnt = unitCounter((LoopingStatement) st, block, params, w)
                if (cnt == null) continue
                final Map<String, List<MethodCallExpression>> perChan = new LinkedHashMap<String, List<MethodCallExpression>>()
                ((LoopingStatement) st).loopBlock.visit(new CodeVisitorSupport() {
                    private int cond
                    private void take(MethodCallExpression m, Expression recv) {
                        Expression x = stripCasts(recv)
                        if (!(x instanceof VariableExpression) || cond > 0) return
                        String v = ((VariableExpression) x).name
                        if (scan.streamVarRoot(v, parent) == null) return
                        List<MethodCallExpression> l = perChan.get(v)
                        if (l == null) { l = new ArrayList<MethodCallExpression>(); perChan.put(v, l) }
                        l.add(m)
                    }
                    private void takeAwait(Expression args) {
                        if (!(args instanceof TupleExpression) || ((TupleExpression) args).expressions.size() != 1) return
                        Expression a = stripCasts(((TupleExpression) args).expressions.get(0))
                        if (a instanceof MethodCallExpression && ((MethodCallExpression) a).methodAsString == 'receive' && noArgs((MethodCallExpression) a)) take((MethodCallExpression) a, ((MethodCallExpression) a).objectExpression)
                    }
                    @Override void visitMethodCallExpression(MethodCallExpression m) {
                        if (m.methodAsString == 'first' && noArgs(m)) take(m, m.objectExpression)
                        if (m.methodAsString == 'await') takeAwait(m.arguments)
                        super.visitMethodCallExpression(m)
                    }
                    @Override void visitStaticMethodCallExpression(StaticMethodCallExpression m) {
                        if (m.method == 'await') takeAwait(m.arguments)
                        super.visitStaticMethodCallExpression(m)
                    }
                    @Override void visitIfElse(IfStatement i) { i.booleanExpression.visit(this); cond++; try { i.ifBlock?.visit(this); i.elseBlock?.visit(this) } finally { cond-- } }
                    @Override void visitForLoop(ForStatement f) { cond++; try { super.visitForLoop(f) } finally { cond-- } }
                    @Override void visitWhileLoop(WhileStatement f) { cond++; try { super.visitWhileLoop(f) } finally { cond-- } }
                    @Override void visitDoWhileLoop(DoWhileStatement f) { cond++; try { super.visitDoWhileLoop(f) } finally { cond-- } }
                    @Override void visitClosureExpression(ClosureExpression c) { cond++; try { super.visitClosureExpression(c) } finally { cond-- } }
                })
                // Phase 253 — the looping ALT: one `Result r = await ChannelSelect.from(a, b).select()` at the
                // body's top level, every branch a stream var not otherwise received in this loop.
                Statement lb0 = ((LoopingStatement) st).loopBlock
                List<Statement> top0 = lb0 instanceof BlockStatement ? ((BlockStatement) lb0).statements : Collections.singletonList(lb0)
                String altVar = null; List<String> altChans = null; Expression altFrom = null; int altCount = 0
                String altPolicy = 'priority'; boolean altHeld = false
                for (Statement inner : top0) {
                    if (!(inner instanceof ExpressionStatement) || !(((ExpressionStatement) inner).expression instanceof DeclarationExpression)) continue
                    DeclarationExpression de = (DeclarationExpression) ((ExpressionStatement) inner).expression
                    SelectRef ref = awaitedSelect(de.rightExpression, scan.selectRefs)
                    List<Expression> alt = ref == null ? null : ref.chans
                    if (alt == null || !(de.leftExpression instanceof VariableExpression)) continue
                    altCount++
                    List<String> chans = new ArrayList<String>()
                    for (Expression a : alt) {
                        Expression x = stripCasts(a)
                        String v = x instanceof VariableExpression ? ((VariableExpression) x).name : null
                        if (v == null || scan.streamVarRoot(v, parent) == null || perChan.containsKey(v)) { chans = null; break }
                        chans.add(v)
                    }
                    if (chans == null || chans.isEmpty()) continue
                    altVar = ((VariableExpression) de.leftExpression).name
                    altChans = chans
                    altFrom = awaitedSelectCall(de.rightExpression)             // the select() call is the anchor
                    altPolicy = ref.policy; altHeld = ref.held
                }
                if (altCount != 1) { altVar = null }
                if (perChan.isEmpty() && altVar == null) continue
                ConsumerInfo ci = new ConsumerInfo()
                ci.loop = (LoopingStatement) st; ci.counter = (String) cnt[0]; ci.counterInit = (Expression) cnt[1]
                for (Map.Entry<String, List<MethodCallExpression>> e : perChan.entrySet()) {
                    if (e.value.size() != 1) continue                       // two receives per iteration: unsanctioned (flagged)
                    ci.receives.put(e.value.get(0), e.key)
                    ci.chans.add(e.key)
                    scan.sanctionedReceives.add(e.value.get(0))
                }
                if (altVar != null) {
                    ci.altVar = altVar; ci.altChans.addAll(altChans); ci.altFrom = altFrom
                    ci.altPolicy = altPolicy; ci.altHeld = altHeld
                    scan.sanctionedFroms.add(altFrom)
                    // Phase 256 — replies guarded by the choice: `if (r.index == i) { X.send(E) }` at the body's top level
                    for (Statement inner : top0) {
                        if (!(inner instanceof IfStatement)) continue
                        IfStatement ifs = (IfStatement) inner
                        Expression g = stripCasts(ifs.booleanExpression.expression)
                        if (!(g instanceof BinaryExpression) || ((BinaryExpression) g).operation.type != Types.COMPARE_EQUAL) continue
                        Expression gl = stripCasts(((BinaryExpression) g).leftExpression)
                        Integer branch = intLiteral(((BinaryExpression) g).rightExpression)
                        boolean onIndex = (gl instanceof PropertyExpression && ((PropertyExpression) gl).propertyAsString == 'index' &&
                            stripCasts(((PropertyExpression) gl).objectExpression) instanceof VariableExpression &&
                            ((VariableExpression) stripCasts(((PropertyExpression) gl).objectExpression)).name == altVar)
                        if (!onIndex || branch == null) continue
                        Statement ib = ifs.ifBlock
                        List<Statement> its = ib instanceof BlockStatement ? ((BlockStatement) ib).statements : Collections.singletonList(ib)
                        for (Statement st2 : its) {
                            MethodCallExpression sc2 = sendCallOf(st2, ch)
                            if (sc2 != null) {
                                ci.guardedSends.put(((VariableExpression) stripCasts(sc2.objectExpression)).name, branch)
                                ci.guardedSendCalls.put(((VariableExpression) stripCasts(sc2.objectExpression)).name, sc2)
                            }
                        }
                    }
                }
                if (!ci.receives.isEmpty() || ci.altVar != null) scan.consumers.put((Statement) st, ci)
            }
        }
        }
        computeCycles(scan, parent, ch)                                            // Phase 258/261
        // Phase 252 — a loop that both receives and sends (a stage as a process): the sent expression may
        // name a local declared from a sanctioned receive in the same body — an alias of the read element,
        // so the element relation still holds through it.
        for (StreamInfo info : scan.streams.values()) {
            ConsumerInfo ci = scan.consumers.get((Statement) info.loop)
            if (ci == null) continue
            Statement lb = info.loop.loopBlock
            List<Statement> top = lb instanceof BlockStatement ? ((BlockStatement) lb).statements : Collections.singletonList(lb)
            for (Statement st : top) {
                if (!(st instanceof ExpressionStatement) || !(((ExpressionStatement) st).expression instanceof DeclarationExpression)) continue
                DeclarationExpression de = (DeclarationExpression) ((ExpressionStatement) st).expression
                if (!(de.leftExpression instanceof VariableExpression)) continue
                MethodCallExpression rc = receiveCallOf(de.rightExpression)
                if (rc != null && ci.readOf(rc) != null) {
                    info.aliases.put(((VariableExpression) de.leftExpression).name, rc)
                }
            }
            boolean rel = true
            for (String n : varNames(info.sendExpr)) {
                if (n == info.counter || info.aliases.containsKey(n)) continue
                if (info.conditional && (n == info.valueAlias || n == ci.altVar)) continue   // Phase 258 — the ALT's value
                if (ch.contains(n) || writesVar(info.loop.loopBlock, n)) rel = false
            }
            info.elementRelation = rel
        }
        scan
    }

    /** The receive call behind `x.first()` or `await x.receive()` (either await shape), else null. */
    static MethodCallExpression receiveCallOf(Expression e) {
        Expression x = stripCasts(e)
        if (x instanceof MethodCallExpression && ((MethodCallExpression) x).methodAsString == 'first') return (MethodCallExpression) x
        Expression args = null
        if (x instanceof MethodCallExpression && ((MethodCallExpression) x).methodAsString == 'await') args = ((MethodCallExpression) x).arguments
        else if (x instanceof StaticMethodCallExpression && ((StaticMethodCallExpression) x).method == 'await') args = ((StaticMethodCallExpression) x).arguments
        if (!(args instanceof TupleExpression) || ((TupleExpression) args).expressions.size() != 1) return null
        Expression a = stripCasts(((TupleExpression) args).expressions.get(0))
        (a instanceof MethodCallExpression && ((MethodCallExpression) a).methodAsString == 'receive') ? (MethodCallExpression) a : null
    }

    /** The entry value of a counter as source text (a literal or a parameter name; anything else parenthesised). */
    static String entryText(Expression counterInit) {
        Expression ci = stripCasts(counterInit)
        ci instanceof ConstantExpression ? String.valueOf(((ConstantExpression) ci).value) :
        ci instanceof VariableExpression ? ((VariableExpression) ci).name : "(${ci.text})".toString()
    }

    /** True when the call sits inside any loop of the body (at any depth, arms included). */
    static boolean insideLoop(BlockStatement body, MethodCallExpression target) {
        boolean[] found = [false]
        body.visit(new CodeVisitorSupport() {
            private int depth
            @Override void visitMethodCallExpression(MethodCallExpression m) { if (m.is(target) && depth > 0) found[0] = true; super.visitMethodCallExpression(m) }
            @Override void visitForLoop(ForStatement s) { depth++; try { super.visitForLoop(s) } finally { depth-- } }
            @Override void visitWhileLoop(WhileStatement s) { depth++; try { super.visitWhileLoop(s) } finally { depth-- } }
            @Override void visitDoWhileLoop(DoWhileStatement s) { depth++; try { super.visitDoWhileLoop(s) } finally { depth-- } }
        })
        found[0]
    }

    static final ClassNode INT_LIST_TYPE = GenericsUtils.makeClassSafeWithGenerics(ClassHelper.LIST_TYPE, new GenericsType(ClassHelper.Integer_TYPE))

    static Statement listDecl(String name, ASTNode at) {
        DeclarationExpression de = new DeclarationExpression(new VariableExpression(name, INT_LIST_TYPE),
            Token.newSymbol(Types.ASSIGN, at.lineNumber, at.columnNumber), new ListExpression())
        de.setSourcePosition(at)
        ExpressionStatement st = new ExpressionStatement(de)
        st.setSourcePosition(at)
        st
    }

    /** The transform `f` a map-derived var applies to its root's element, as an expression over {@code elem}. */
    static Expression derivedValue(String d, Expression elem, ChanRewrite rw) {
        String hole = '$elem$'
        Expression chain = rw.withElement(rw.rootOf(d), hole) { rewriteChExpr(new VariableExpression(d), rw) }
        substituteVar(chain, hole, elem)
    }

    /** {@code e} with every occurrence of the variable {@code name} replaced by {@code by} — closure bodies
     *  included (a `ClosureExpression` does not transform its code by itself, so quantifier closures are rebuilt). */
    static Expression substituteVar(Expression e, String name, Expression by) {
        substituteVars(e, Collections.singletonMap(name, by))
    }

    /** Multi-name substitution; a `VariableExpression` replacement is re-minted per occurrence. */
    static Expression substituteVars(Expression e, Map<String, Expression> ren) {
        ExpressionTransformer t = new ExpressionTransformer() {
            @Override Expression transform(Expression x) {
                if (x == null) return null
                if (x instanceof VariableExpression && ren.containsKey(((VariableExpression) x).name)) {
                    Expression by = ren.get(((VariableExpression) x).name)
                    if (by instanceof VariableExpression) {
                        VariableExpression nv = new VariableExpression(((VariableExpression) by).name, ((VariableExpression) x).originType)
                        nv.setSourcePosition(x)
                        return nv
                    }
                    return by
                }
                if (x instanceof ClosureExpression) {
                    ClosureExpression c = (ClosureExpression) x
                    if (!(c.code instanceof BlockStatement)) return x
                    List<Statement> ss = new ArrayList<Statement>()
                    for (Statement st : ((BlockStatement) c.code).statements) {
                        if (st instanceof ExpressionStatement) { Statement n = new ExpressionStatement(transform(((ExpressionStatement) st).expression)); n.setSourcePosition(st); ss.add(n) }
                        else if (st instanceof ReturnStatement) { Statement n = new ReturnStatement(transform(((ReturnStatement) st).expression)); n.setSourcePosition(st); ss.add(n) }
                        else ss.add(st)
                    }
                    ClosureExpression nc = new ClosureExpression(c.parameters, new BlockStatement(ss, ((BlockStatement) c.code).variableScope))
                    nc.setVariableScope(c.variableScope)
                    nc.setSourcePosition(c)
                    return nc
                }
                x.transformExpression(this)
            }
        }
        t.transform(e)
    }

    /** Phase 251 — the producer loop, rewritten: sends append to the shadow lists, closes drop, and the
     *  LoopSpec is rebuilt over the rewritten body with the sequence invariants appended. */
    static Statement rewriteStreamLoop(LoopingStatement loop, List<StreamInfo> infos, ChanRewrite rw) {
        LoopSpec spec = (LoopSpec) ((Statement) loop).getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY)
        ConsumerInfo consumer = rw.consumers.get((Statement) loop)
        ConsumerInfo savedConsumer = rw.curConsumer
        List<StreamInfo> savedInfos = rw.curInfos
        rw.curConsumer = consumer
        rw.curInfos = infos                                                      // Phase 260 — `c.sent` resolves against these
        try {
        Statement lb = loop.loopBlock
        List<Statement> blockIn = lb instanceof BlockStatement ? ((BlockStatement) lb).statements : Collections.singletonList(lb)
        BlockStatement block = new BlockStatement(rewriteStreamStmts(blockIn, rw), lb instanceof BlockStatement ? ((BlockStatement) lb).variableScope : null)
        block.setSourcePosition(lb)
        Statement out
        // Phase 254 — a `while (true)` process in the flattened model gets a FREE guard (`loop$fuelN > 0`, an
        // unassigned name — havoc-by-default): the process may be observed at any iteration boundary, so
        // what follows it (the OTHER processes) is reasoned about under its invariant alone, never under
        // the vacuous ¬true. Its own safety VCs (establishment, preservation) are unchanged.
        Expression fuelGuard = isForever(loop) ? ContractExpansionTransform.reparse("loop\$fuel${++rw.fuelCounter} > 0") : null
        if (loop instanceof WhileStatement) out = new WhileStatement(fuelGuard != null ? new BooleanExpression(fuelGuard) : ((WhileStatement) loop).booleanExpression, block)
        else if (loop instanceof DoWhileStatement) out = new DoWhileStatement(((DoWhileStatement) loop).booleanExpression, block)
        else { ForStatement f = (ForStatement) loop; out = new ForStatement(f.variable, f.collectionExpression, block) }
        out.setSourcePosition((Statement) loop); out.copyNodeMetaData((Statement) loop)
        if (spec != null) {
            LoopSpec s2 = new LoopSpec()
            s2.invariants = new ArrayList<Expression>()
            for (Expression inv : spec.invariants) s2.invariants.add(takenGhostRewrite(inv, rw))   // Phase 259 — `c.taken`
            s2.variant = spec.variant; s2.guard = fuelGuard != null ? fuelGuard : spec.guard; s2.init = spec.init
            s2.forInVar = spec.forInVar; s2.forInBind = spec.forInBind
            s2.isDoWhile = spec.isDoWhile; s2.autoInvariantOnly = spec.autoInvariantOnly
            s2.body = rewriteStreamStmts(spec.body, rw)
            for (StreamInfo info : infos) s2.invariants.addAll(streamInvariants(info, rw))
            // Phase 252 — a consumer loop knows its producers' post-state as FRAME facts: the producer
            // loop's own invariants, its injected sequence facts and ¬guard hold throughout (nothing here
            // writes the producer's counter or its list) — the element-exists obligations discharge on them.
            if (consumer != null) {
                // Phase 254 — the elements read so far exist: `counter - a <= x$q.size()` per consumed stream.
                // With a finite producer this followed from its exit fact; an infinite producer has none, and
                // a stage's output count must still be bounded by its input count (established at 0, preserved
                // by the read's element-exists fact — asserted or assumed — each iteration).
                s2.invariants.addAll(consumerBoundInvariants(consumer, rw))
                // Phase 253/258 — the looping ALT's cursors and taken-ghosts
                Expression cinv = cursorInvariant(consumer, rw)
                if (cinv != null) s2.invariants.add(cinv)
                // transitively: a stage's facts relate its list to the stream IT consumed, whose facts are needed too
                Set<String> seen = new HashSet<String>()
                List<String> todo = new ArrayList<String>()
                for (String v : consumer.receives.values()) todo.add(rw.rootOf(v))
                for (String v : consumer.altChans) todo.add(rw.rootOf(v))
                while (!todo.isEmpty()) {
                    String root = todo.remove(0)
                    StreamInfo p = rw.streams.get(root)
                    if (p == null || p.loop.is(loop) || !seen.add(root)) continue
                    if (rw.partnerLoop((Statement) loop, (Statement) p.loop)) continue   // Phase 258 — a cycle partner: relied on at the read, not framed
                    LoopSpec ps = (LoopSpec) ((Statement) p.loop).getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY)
                    if (ps != null) {
                        s2.invariants.addAll(specInContext(ps.invariants, (Statement) p.loop, rw))   // Phase 260 — its ghosts, in its context
                        if (!p.infinite) s2.invariants.add(new NotExpression(ps.guard))   // Phase 254 — an infinite producer has no exit fact
                    }
                    s2.invariants.addAll(streamInvariants(p, rw))
                    ConsumerInfo pc = rw.consumers.get((Statement) p.loop)
                    if (pc != null) {
                        s2.invariants.addAll(consumerBoundInvariants(pc, rw))       // Phase 254 — the stage's own read bounds
                        for (String v : pc.receives.values()) todo.add(rw.rootOf(v))
                        for (String v : pc.altChans) todo.add(rw.rootOf(v))
                    }
                }
            }
            out.putNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY, s2)
        }
        out
        } finally { rw.curConsumer = savedConsumer; rw.curInfos = savedInfos }
    }

    /** Phase 253 — the looping ALT, per iteration: the block-forever assert (some branch has an element left),
     *  the choice among the branches with an element left (`$channelSelect.ready`), the value at the chosen
     *  branch's cursor (`valueAt`), and the chosen cursor's step. */
    static List<Statement> loopingAlt(DeclarationExpression de, ChanRewrite rw) {
        ConsumerInfo ci = rw.curConsumer
        List<Statement> out = new ArrayList<Statement>()
        String r = ci.altVar
        List<String> partners = new ArrayList<String>()                        // Phase 258 — branches fed by cycle partners
        for (String c : ci.altChans) if (rw.partner(c)) partners.add(c)
        if (!partners.isEmpty()) out.addAll(relyBlock(partners, rw, de))
        Closure<String> listOf = { String c -> rw.partner(c) ? (rw.relyName.get(c) ?: c + '$q') : c + '$q' }
        List<String> ready = new ArrayList<String>()
        for (String c : ci.altChans) ready.add("${c}\$c < ${listOf(c)}.size()".toString())
        Expression cond = ContractExpansionTransform.reparse(ready.join(' || '))
        if (cond != null) {
            AssertStatement a = new AssertStatement(new BooleanExpression(cond))
            a.setSourcePosition(de)
            a.putNodeMetaData(ASSERT_LABEL_KEY, ("the ALT over ${ci.altChans.collect { "'" + it + "'" }.join(', ')} (line ${de.lineNumber}) may block forever — " +
                "no branch may have an element left (the multiplexer loop reads past what its producers send)").toString())
            boolean anyInfinite = false
            for (String c : ci.altChans) {                                    // Phase 254 — an infinite branch can always serve
                StreamInfo p = rw.streams.get(rw.rootOf(c))
                if (p != null && p.infinite) { a.putNodeMetaData(ASSUME_ONLY_KEY, Boolean.TRUE); anyInfinite = true }
            }
            if (!partners.isEmpty()) a.putNodeMetaData(ASSUME_ONLY_KEY, Boolean.TRUE)   // Phase 261 — a partner's snapshot may be short: liveness
            if (!partners.isEmpty() && !anyInfinite) {
                // Phase 261 — every branch finite: some branch must have an element left in ALL — a partner branch
                // below its total, a non-partner branch below its (exact) list — asserted.
                List<String> left = new ArrayList<String>()
                boolean complete = true
                for (String c : ci.altChans) {
                    StreamInfo p = rw.streams.get(rw.rootOf(c))
                    if (rw.partner(c)) {
                        String total = p == null ? null : staticTotalText(p, rw.ch)
                        if (total == null) { complete = false; break }
                        left.add("${c}\$c < ${total}".toString())
                    } else left.add("${c}\$c < ${c}\$q.size()".toString())
                }
                Expression bound = complete ? ContractExpansionTransform.reparse(left.join(' || ')) : null
                if (bound != null) {
                    AssertStatement b = new AssertStatement(new BooleanExpression(bound))
                    b.setSourcePosition(de)
                    b.putNodeMetaData(ASSERT_LABEL_KEY, ("the ALT over ${ci.altChans.collect { "'" + it + "'" }.join(', ')} (line ${de.lineNumber}) may block forever — " +
                        "every branch's producer terminates, and this loop selects past what they send in all").toString())
                    out.add(b)
                }
            }
            out.add(a)
        }
        VariableExpression marker = new VariableExpression(Encoder.CHANNEL_SELECT_MARKER)
        List<Expression> readyArgs = new ArrayList<Expression>()
        List<Expression> valueArgs = new ArrayList<Expression>()
        valueArgs.add(new VariableExpression(r + '$index'))
        for (int i = 0; i < ci.altChans.size(); i++) {
            String c = ci.altChans.get(i)
            for (List<Expression> l : [readyArgs, valueArgs]) {
                l.add(new ConstantExpression(i, true)); l.add(new VariableExpression(listOf(c))); l.add(new VariableExpression(c + '$c'))
            }
        }
        // Phase 275 — GROOVY-12324's mask, if this select carries one: the chosen branch must be enabled
        // as well as ready, which is the fact a guarded loop's invariant turns on.
        List<Expression> gmask = awaitedSelectMask(de.rightExpression)
        String readyOp = 'ready'
        if (gmask != null && gmask.size() == ci.altChans.size()) {
            readyOp = 'readyGuarded'
            List<Expression> ga = new ArrayList<Expression>()
            for (int i = 0; i < ci.altChans.size(); i++) {
                String c = ci.altChans.get(i)
                ga.add(new ConstantExpression(i, true)); ga.add(new VariableExpression(listOf(c)))
                ga.add(new VariableExpression(c + '$c')); ga.add(rewriteChExpr(gmask.get(i), rw))
            }
            readyArgs = ga
        }
        MethodCallExpression readyCall = new MethodCallExpression(marker, readyOp, new ArgumentListExpression(readyArgs))
        readyCall.setSourcePosition(de)
        DeclarationExpression d1 = new DeclarationExpression(new VariableExpression(r + '$index'), Token.newSymbol(Types.ASSIGN, de.lineNumber, de.columnNumber), readyCall)
        d1.setSourcePosition(de)
        out.add(new ExpressionStatement(d1))
        // Phase 256/257 — under the claim-based select (GROOVY-12320) exactly one branch dequeues and losers are
        // untouched, so the value is the chosen branch's HEAD; under the racing select a loser's element is
        // re-sent to the back, so it is SOME remaining element.
        MethodCallExpression valueCall = new MethodCallExpression(marker, CLAIM_SELECT ? 'valueAt' : 'valueAny', new ArgumentListExpression(valueArgs))
        valueCall.setSourcePosition(de)
        DeclarationExpression d2 = new DeclarationExpression(new VariableExpression(r + '$value'), Token.newSymbol(Types.ASSIGN, de.lineNumber, de.columnNumber), valueCall)
        d2.setSourcePosition(de)
        out.add(new ExpressionStatement(d2))
        for (int i = 0; i < ci.altChans.size(); i++) {                       // the chosen branch's cursor steps
            String c = ci.altChans.get(i)
            Expression guard = ContractExpansionTransform.reparse("${r}\$index == ${i}")
            Expression bump = ContractExpansionTransform.reparse("${c}\$c = ${c}\$c + 1")
            if (guard == null || bump == null) continue
            ExpressionStatement bs = new ExpressionStatement(bump)
            bs.setSourcePosition(de)
            Statement tk = addStmt(c + '$taken', new VariableExpression(r + '$value'), de)      // Phase 258 — the element taken
            IfStatement ifs = new IfStatement(new BooleanExpression(guard), new BlockStatement([bs, tk] as List<Statement>, null), EmptyStatement.INSTANCE)
            ifs.setSourcePosition(de)
            out.add(ifs)
        }
        rw.selectVars.add(r)
        out
    }

    /** Phase 254 — a consumer loop's read bounds: the elements it has read so far exist in each consumed stream. */
    static List<Expression> consumerBoundInvariants(ConsumerInfo ci, ChanRewrite rw) {
        List<Expression> out = new ArrayList<Expression>()
        Set<String> seen = new HashSet<String>()
        ConsumerInfo saved = rw.curConsumer
        rw.curConsumer = ci
        try {
            for (String v : ci.receives.values()) {
                if (!seen.add(v)) continue
                // Phase 258 — a partner stream is read through rely views; what the loop knows is what it has TAKEN
                Expression e = rw.partner(v)
                    ? ContractExpansionTransform.reparse("${v}\$taken != null && ${v}\$taken.size() == ${ci.counter} - ${entryText(ci.counterInit)}")
                    : ContractExpansionTransform.reparse("${ci.counter} - ${entryText(ci.counterInit)} <= ${v}\$q.size()")
                if (e != null) out.add(norm(e, rw))
            }
        } finally { rw.curConsumer = saved }
        out
    }

    /** Phase 253/258 — the looping ALT's cursors: each within its list, together counting the iterations; each
     *  branch's taken-ghost is the prefix its cursor has passed (a partner branch: just the cursor's length). */
    static Expression cursorInvariant(ConsumerInfo consumer, ChanRewrite rw, boolean stableOnly = false) {
        if (consumer.altVar == null) return null
        ConsumerInfo saved = rw.curConsumer
        rw.curConsumer = consumer
        try {
            List<String> parts = new ArrayList<String>()
            List<String> sum = new ArrayList<String>()
            for (String c : consumer.altChans) {
                // Under the racing select (before GROOVY-12320) the element taken is SOME remaining one and losers are
                // re-sent: the taken-ghost is a count, not the prefix — the prefix fact holds only under the claim-based select.
                if (stableOnly) {                                                // Phase 260 — no count equality; the prefix law over the ghost's own size
                    parts.add(("0 <= ${c}\$c && ${c}\$taken != null" + (rw.partner(c) || !CLAIM_SELECT ? '' :
                        " && ${c}\$taken.size() <= ${c}\$q.size() && Forall.range(0, ${c}\$taken.size(), { int k -> ${c}\$taken[k] == ${c}\$q[k] })")).toString())
                    continue
                }
                if (rw.partner(c)) parts.add("0 <= ${c}\$c && ${c}\$taken != null && ${c}\$taken.size() == ${c}\$c".toString())
                else parts.add(("0 <= ${c}\$c && ${c}\$c <= ${c}\$q.size() && ${c}\$taken != null && ${c}\$taken.size() == ${c}\$c" +
                    (CLAIM_SELECT ? " && Forall.range(0, ${c}\$c, { int k -> ${c}\$taken[k] == ${c}\$q[k] })" : '')).toString())
                sum.add(c + '$c')
            }
            if (!stableOnly) parts.add("${sum.join(' + ')} == ${consumer.counter} - ${entryText(consumer.counterInit)}".toString())
            Expression inv = ContractExpansionTransform.reparse(parts.join(' && '))
            inv == null ? null : norm(inv, rw)
        } finally { rw.curConsumer = saved }
    }

    /** Names a statement assigns (declares, assigns, or steps). */
    static Set<String> assignedNames(Statement s) {
        final Set<String> names = new LinkedHashSet<String>()
        s.visit(new CodeVisitorSupport() {
            @Override void visitVariableExpression(VariableExpression ve) { names.add(ve.name); super.visitVariableExpression(ve) }
        })
        Set<String> out = new LinkedHashSet<String>()
        for (String n : names) if (writesVar(s, n)) out.add(n)
        out
    }

    /**
     * Phase 258 — the RELY at a read from a cycle partner: the reader's view of the partner's stream is a fresh
     * list (`X$rely<n>`, unassigned: havoc-by-default), constrained by the whole cycle's invariants instantiated
     * over fresh names — every other member's locals, produced lists, cursors and taken-ghosts — plus the FIFO
     * law for each taken-ghost: what a consumer has taken is a prefix of what its producer sent (the reader's
     * OWN list where the reader is that producer — the link that closes a request–reply claim). Sound because
     * the conjunction of the loops' invariants is a global invariant (each mentions its own counter and lists
     * exactly and others' only through append-stable facts) and the partners' states are existentially
     * quantified; that the element exists is liveness, assumed as Phase 254 does.
     */
    static List<Statement> relyBlock(Collection<String> vars, ChanRewrite rw, ASTNode at) {
        List<Statement> out = new ArrayList<Statement>()
        ConsumerInfo me = rw.curConsumer
        if (me == null) return out
        int n = ++rw.relyCounter
        String sfx = '$r' + n
        for (String v : vars) rw.relyName.put(v, "${v}\$rely${n}".toString())
        Statement L = (Statement) me.loop
        List<Statement> members = rw.cycleOf.get(L)
        if (members == null) return out
        List<Expression> facts = new ArrayList<Expression>()
        for (Statement P : members) {
            ConsumerInfo pc = rw.consumers.get(P)
            List<StreamInfo> pinfos = new ArrayList<StreamInfo>()
            for (StreamInfo pi : rw.streams.values()) if (pi.loop.is(P)) pinfos.add(pi)
            Map<String, Expression> ren = new HashMap<String, Expression>()
            Set<String> locals = new LinkedHashSet<String>()
            if (pc != null) { locals.add(pc.counter); for (String c : pc.altChans) locals.add(c + '$c') }
            for (StreamInfo pi : pinfos) locals.add(pi.counter)
            locals.addAll(assignedNames(((LoopingStatement) P).loopBlock))
            for (String nm : locals) ren.put(nm, new VariableExpression(nm + sfx))
            for (StreamInfo pi : pinfos) {
                List<String> lvs = new ArrayList<String>(); lvs.add(pi.root); lvs.addAll(pi.derived)
                for (String lv : lvs) ren.put(lv + '$q', new VariableExpression(vars.contains(lv) ? rw.relyName.get(lv) : lv + '$q' + sfx))
            }
            Set<String> pTaken = new LinkedHashSet<String>()
            if (pc != null) {
                pTaken.addAll(pc.altChans)
                Set<String> pps = rw.partnerStreams.get(P)
                for (String v : pc.receives.values()) if (pps != null && pps.contains(rw.rootOf(v))) pTaken.add(v)
            }
            for (String tv : pTaken) ren.put(tv + '$taken', new VariableExpression(tv + '$taken' + sfx))
            // Phase 260 — a partner is observed at ANY point of its body: only its append-STABLE facts may be assumed —
            // elementwise laws bounded by their own list, priming values, "sends follow takes", the prefix law of an
            // ALT branch, and the user's conjuncts that mention no ghost count (stableUserConjuncts). Never a count
            // equality: Phase 258 assumed the loop-head invariants whole, which a partner mid-iteration violates, and
            // the partner's own preservation VC in a cycle was vacuous (a wrong `c.sent` law went unrefuted).
            List<Expression> pf = new ArrayList<Expression>()
            LoopSpec ps = (LoopSpec) P.getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY)
            if (ps != null) pf.addAll(stableUserConjuncts(specInContext(ps.invariants, P, rw)))   // Phase 259/260 — its ghosts, in its context
            ConsumerInfo saved = rw.curConsumer
            rw.curConsumer = pc; rw.readsAsTaken = true
            try {
                for (StreamInfo pi : pinfos) {
                    pf.addAll(streamInvariants(pi, rw, true)); pf.addAll(sendsFollowTakes(pi, rw))
                    String total = staticTotalText(pi, rw.ch)                     // Phase 261 — never more than its total: stable
                    Expression tb = total == null ? null : ContractExpansionTransform.reparse("${pi.root}\$q.size() <= ${total}")
                    if (tb != null) pf.add(norm(tb, rw))
                }
                if (pc != null) { Expression cv = cursorInvariant(pc, rw, true); if (cv != null) pf.add(cv) }
            } finally { rw.curConsumer = saved; rw.readsAsTaken = false }
            for (Expression f : pf) facts.add(substituteVars(f, ren))
            for (String tv : pTaken) {                                          // the FIFO law
                StreamInfo prod = rw.streams.get(rw.rootOf(tv))
                if (prod == null) continue
                String list = prod.loop.is(L) ? tv + '$q' : (vars.contains(tv) ? rw.relyName.get(tv) : tv + '$q' + sfx)
                String tk = tv + '$taken' + sfx
                // An ALT branch under the racing select is dequeued out of order (losers re-sent): count only.
                boolean inOrder = CLAIM_SELECT || pc == null || !pc.altChans.contains(tv)
                Expression law = ContractExpansionTransform.reparse(
                    "${tk} != null && ${list} != null && ${tk}.size() <= ${list}.size()" +
                    (inOrder ? " && Forall.range(0, ${tk}.size(), { int k -> ${tk}[k] == ${list}[k] })" : ''))
                if (law != null) facts.add(norm(law, rw))
            }
        }
        if (System.getenv('VERIFY_DEBUG_RELY') != null) for (Expression f : facts) System.err.println("rely@${at.lineNumber}: ${f.text}")
        for (Expression f : facts) {
            AssertStatement a = new AssertStatement(new BooleanExpression(f))
            a.setSourcePosition(at)
            a.putNodeMetaData(ASSERT_LABEL_KEY, 'rely: a cycle partner\'s invariant (assumed)')
            a.putNodeMetaData(ASSUME_ONLY_KEY, Boolean.TRUE)
            out.add(a)
        }
        out
    }

    /** Phase 258/259 — the stream vars a consumer loop keeps a taken-ghost for: partner reads and ALT branches. */
    static Set<String> takenVars(ConsumerInfo ci, ChanRewrite rw) {
        Set<String> tv = new LinkedHashSet<String>()
        if (ci == null) return tv
        tv.addAll(ci.altChans)
        Set<String> pps = rw.partnerStreams.get((Statement) ci.loop)
        for (String v : ci.receives.values()) if (pps != null && pps.contains(rw.rootOf(v))) tv.add(v)
        tv
    }

    /**
     * Phase 259 — `c.taken` (or `c.getTaken()`) in a spec or body of the current consumer loop → the loop's
     * taken-ghost `c$taken`. Anywhere else it names nothing: recorded, reported once the rewrite is done.
     */
    static Expression takenGhostRewrite(Expression e, ChanRewrite rw) {
        if (e == null) return null
        ExpressionTransformer t = new ExpressionTransformer() {
            @Override Expression transform(Expression x) {
                if (x == null) return null
                String c = null
                if (x instanceof PropertyExpression && ((PropertyExpression) x).propertyAsString == 'taken' &&
                    stripCasts(((PropertyExpression) x).objectExpression) instanceof VariableExpression) {
                    c = ((VariableExpression) stripCasts(((PropertyExpression) x).objectExpression)).name
                } else if (x instanceof MethodCallExpression && ((MethodCallExpression) x).methodAsString == 'getTaken' && noArgs((MethodCallExpression) x) &&
                    stripCasts(((MethodCallExpression) x).objectExpression) instanceof VariableExpression) {
                    c = ((VariableExpression) stripCasts(((MethodCallExpression) x).objectExpression)).name
                }
                String sc = null                                                  // Phase 260 — `c.sent` / `c.getSent()`
                if (x instanceof PropertyExpression && ((PropertyExpression) x).propertyAsString == 'sent' &&
                    stripCasts(((PropertyExpression) x).objectExpression) instanceof VariableExpression) {
                    sc = ((VariableExpression) stripCasts(((PropertyExpression) x).objectExpression)).name
                } else if (x instanceof MethodCallExpression && ((MethodCallExpression) x).methodAsString == 'getSent' && noArgs((MethodCallExpression) x) &&
                    stripCasts(((MethodCallExpression) x).objectExpression) instanceof VariableExpression) {
                    sc = ((VariableExpression) stripCasts(((MethodCallExpression) x).objectExpression)).name
                }
                if (c != null && rw.ch.contains(c)) {
                    Set<String> tv = takenVars(rw.curConsumer, rw)
                    if (tv.contains(c)) {
                        VariableExpression g = new VariableExpression(c + '$taken')
                        g.setSourcePosition(x)
                        return g
                    }
                    if (!rw.relyMode) {
                        String why = rw.curConsumer == null
                            ? 'it is outside a specified loop that receives from a stream'
                            : "the loop at line ${((Statement) rw.curConsumer.loop).lineNumber} takes nothing from '${c}' (it is not a stream this loop receives from a cycle partner, nor a branch of its ALT)".toString()
                        ASTNode at = x.lineNumber > 0 ? x : (rw.curConsumer != null ? (ASTNode) rw.curConsumer.loop : x)   // a reparsed spec has no position
                        rw.ghostErrors.add([c + '.taken', why, at] as Object[])
                    }
                    return x
                }
                if (sc != null && rw.ch.contains(sc)) {
                    StreamInfo own = rw.curInfos.find { StreamInfo si -> si.root == sc }
                    if (own != null) {
                        VariableExpression g = new VariableExpression(sc + '$q')          // the producer's own exact list (priming sends included)
                        g.setSourcePosition(x)
                        return g
                    }
                    if (!rw.relyMode) {
                        Statement here = rw.curInfos.isEmpty() ? (rw.curConsumer == null ? null : (Statement) rw.curConsumer.loop) : (Statement) rw.curInfos.get(0).loop
                        String why = here == null
                            ? 'it is outside a specified loop that produces a stream'
                            : "the loop at line ${here.lineNumber} produces no stream on '${sc}' (one send per iteration, at the body's top level or guarded by its ALT)".toString()
                        ASTNode at = x.lineNumber > 0 ? x : (here != null ? (ASTNode) here : x)
                        rw.ghostErrors.add([sc + '.sent', why, at] as Object[])
                    }
                    return x
                }
                if (x instanceof ClosureExpression) {
                    ClosureExpression cl = (ClosureExpression) x
                    if (!(cl.code instanceof BlockStatement)) return x
                    List<Statement> ss = new ArrayList<Statement>()
                    for (Statement st : ((BlockStatement) cl.code).statements) {
                        if (st instanceof ExpressionStatement) { Statement n = new ExpressionStatement(transform(((ExpressionStatement) st).expression)); n.setSourcePosition(st); ss.add(n) }
                        else if (st instanceof ReturnStatement) { Statement n = new ReturnStatement(transform(((ReturnStatement) st).expression)); n.setSourcePosition(st); ss.add(n) }
                        else ss.add(st)
                    }
                    ClosureExpression nc = new ClosureExpression(cl.parameters, new BlockStatement(ss, ((BlockStatement) cl.code).variableScope))
                    nc.setVariableScope(cl.variableScope)
                    nc.setSourcePosition(cl)
                    return nc
                }
                x.transformExpression(this)
            }
        }
        t.transform(e)
    }

    /** Phase 259/260 — another loop's spec with ITS ghosts (`c.taken`, `c.sent`) resolved in its own context. */
    static List<Expression> specInContext(List<Expression> invs, Statement loop, ChanRewrite rw) {
        ConsumerInfo savedC = rw.curConsumer
        List<StreamInfo> savedI = rw.curInfos
        boolean savedMode = rw.relyMode
        rw.curConsumer = rw.consumers.get(loop)
        List<StreamInfo> infos = new ArrayList<StreamInfo>()
        for (StreamInfo si : rw.streams.values()) if (si.loop.is(loop)) infos.add(si)
        rw.curInfos = infos
        rw.relyMode = true
        try {
            List<Expression> out = new ArrayList<Expression>()
            for (Expression inv : invs) out.add(takenGhostRewrite(inv, rw))
            out
        } finally { rw.curConsumer = savedC; rw.curInfos = savedI; rw.relyMode = savedMode }
    }

    /** Phase 258 — after a partner read: the element read joins the reader's taken-ghost. */
    static Statement takenAppend(String v, ChanRewrite rw, ASTNode at) {
        ConsumerInfo ci = rw.curConsumer
        Expression val = ContractExpansionTransform.reparse("${rw.relyName.get(v)}[${ci.counter} - ${entryText(ci.counterInit)}]")
        val == null ? null : addStmt(v + '$taken', val, at)
    }

    /** Phase 252 — the shadow-list read a sanctioned receive becomes inside its consumer loop: `x$q[i - a]`. */
    static Expression consumerRead(MethodCallExpression recv, ChanRewrite rw) {
        ConsumerInfo ci = rw.curConsumer
        String v = ci == null ? null : ci.readOf(recv)
        if (v == null) return null
        // Phase 258 — a partner stream: the rely view in the body, the taken-ghost in an invariant
        String list = rw.partner(v) ? (rw.readsAsTaken ? v + '$taken' : (rw.relyName.get(v) ?: v + '$q')) : v + '$q'
        Expression e = ContractExpansionTransform.reparse("${list}[${ci.counter} - ${entryText(ci.counterInit)}]")
        if (e != null) e.setSourcePosition(recv)
        e
    }

    /** Phase 252 — the block-forever obligation of a sanctioned receive: the element it reads must exist. */
    static List<Statement> consumerAssert(MethodCallExpression recv, ChanRewrite rw) {
        List<Statement> out = new ArrayList<Statement>()
        ConsumerInfo ci = rw.curConsumer
        String v = ci.readOf(recv)
        if (v == null) return out
        String list = rw.partner(v) ? (rw.relyName.get(v) ?: v + '$q') : v + '$q'          // Phase 258
        Expression cond = ContractExpansionTransform.reparse("${ci.counter} - ${entryText(ci.counterInit)} < ${list}.size()")
        if (cond == null) return out
        AssertStatement a = new AssertStatement(new BooleanExpression(cond))
        a.setSourcePosition(recv)
        a.putNodeMetaData(ASSERT_LABEL_KEY, ("the receive on '${v}' (line ${recv.lineNumber}) may block forever — " +
            "the element it reads may never be sent (the consumer loop reads past what the producer loop sends)").toString())
        StreamInfo p = rw.streams.get(rw.rootOf(v))
        if (p != null && p.infinite) a.putNodeMetaData(ASSUME_ONLY_KEY, Boolean.TRUE)   // Phase 254 — liveness: assumed, reported
        if (p != null && !p.infinite && rw.partner(v)) {
            // Phase 261 — a FINITE partner: the snapshot may be short of the element (liveness: assumed, as for an
            // infinite one), but the element exists eventually only if it is below the partner's total — asserted.
            a.putNodeMetaData(ASSUME_ONLY_KEY, Boolean.TRUE)
            String total = staticTotalText(p, rw.ch)
            Expression bound = total == null ? null : ContractExpansionTransform.reparse("${ci.counter} - ${entryText(ci.counterInit)} < ${total}")
            if (bound != null) {
                AssertStatement b = new AssertStatement(new BooleanExpression(bound))
                b.setSourcePosition(recv)
                b.putNodeMetaData(ASSERT_LABEL_KEY, ("the receive on '${v}' (line ${recv.lineNumber}) may block forever — " +
                    "the producer loop at line ${((Statement) p.loop).lineNumber} sends ${total} element(s) in all, and this loop reads past them").toString())
                out.add(b)
            }
        }
        out.add(a)
        out
    }

    /** The sanctioned receives inside an expression, in evaluation order. */
    static List<MethodCallExpression> sanctionedReceivesIn(Expression e, ChanRewrite rw) {
        final List<MethodCallExpression> out = new ArrayList<MethodCallExpression>()
        if (e == null || rw.curConsumer == null) return out
        e.visit(new CodeVisitorSupport() {
            @Override void visitMethodCallExpression(MethodCallExpression m) {
                if (rw.curConsumer.readOf(m) != null) out.add(m)
                super.visitMethodCallExpression(m)
            }
        })
        out
    }

    /** The injected sequence facts for one stream: size == counter − entry, and (when the sent expression
     *  is a function of the counter and loop constants) the k-th element's value; likewise per map stage. */
    /**
     * The stream's laws. {@code stableOnly} (Phase 260 — what a RELY may assume of a partner observed at ANY point
     * of its body, not only at its loop head): the elementwise laws, each bounded by its own list's size, and the
     * priming values — never a count equality (`q.size() == counter`, `dq.size() == q.size()`), which a partner
     * mid-iteration violates and which made the partner's own preservation VC vacuous.
     */
    static List<Expression> streamInvariants(StreamInfo info, ChanRewrite rw, boolean stableOnly = false) {
        List<Expression> out = new ArrayList<Expression>()
        String q = info.root + '$q'
        Expression nn = ContractExpansionTransform.reparse("${q} != null")
        if (info.conditional) {                                                // Phase 258 — a guarded reply
            String k = 'k'
            Expression size = ContractExpansionTransform.reparse("${q} != null && ${q}.size() == ${info.condChan}\$c")
            Expression rel = null
            if (info.elementRelation) {
                Expression takenK = ContractExpansionTransform.reparse("${info.condChan}\$taken[${k}]")
                Map<String, Expression> ren = new HashMap<String, Expression>()
                if (info.valueAlias != null) ren.put(info.valueAlias, takenK)
                ConsumerInfo ci = rw.consumers.get((Statement) info.loop)
                if (ci != null) ren.put(ci.altVar + '$value', takenK)
                Expression elem = takenK == null ? null : substituteVars(rewriteChExpr(info.sendExpr, rw), ren)
                Expression shape = ContractExpansionTransform.reparse("Forall.range(0, ${q}.size(), { int ${k} -> ${q}[${k}] == __E__ })")
                if (elem != null && shape != null) rel = substituteVar(shape, '__E__', elem)
            }
            if (stableOnly) size = nn
            if (size != null && rel != null) out.add(norm(new BinaryExpression(size, Token.newSymbol(Types.LOGICAL_AND, -1, -1), rel), rw))
            else if (size != null) out.add(norm(size, rw))
            return out
        }
        // The entry value as source text. NB: never `(name) + k` — Groovy parses a parenthesised bare
        // identifier before an operand as a CAST (`(lo) +k`); the counter offset is spelled `k + entry`.
        String initText = entryText(info.counterInit)
        String preText = info.pre == 0 ? '' : " + ${info.pre}"
        Expression size = ContractExpansionTransform.reparse("${q} != null && ${q}.size() == ${info.counter} - ${initText}${preText}")
        String k = info.counter == 'k' ? 'kk' : 'k'
        Expression rel = null
        Expression sendE = aliasedSend(info, k, initText, rw)
        if (info.elementRelation) {
            // E[i := a + (k - pre)], a receive alias `v = in.first()` in the same loop standing for in$q[(k + a) - a_c]
            Expression atK = ContractExpansionTransform.reparse(info.pre == 0 ? "(${k} + ${initText})" : "(${k} - ${info.pre} + ${initText})")
            Expression elem = atK == null ? null : substituteVar(sendE, info.counter, atK)
            Expression shape = ContractExpansionTransform.reparse("Forall.range(${info.pre}, ${q}.size(), { int ${k} -> ${q}[${k}] == __E__ })")
            if (elem != null && shape != null) rel = substituteVar(shape, '__E__', elem)
        }
        if (stableOnly) size = nn
        if (size != null && rel != null) out.add(norm(new BinaryExpression(size, Token.newSymbol(Types.LOGICAL_AND, -1, -1), rel), rw))
        else if (size != null) out.add(norm(size, rw))
        // Phase 255 — the priming elements' values survive the loop's summary only through its invariant
        for (int j = 0; j < info.preValues.size(); j++) {
            Expression pv = info.preValues.get(j)
            if (pv == null || !loopConstant(pv, info, rw)) continue
            Expression at = ContractExpansionTransform.reparse("${q}[${j}]")
            if (at != null) out.add(norm(new BinaryExpression(at, Token.newSymbol(Types.COMPARE_EQUAL, -1, -1), rewriteChExpr(pv, rw)), rw))
            for (String d : info.derived) {
                Expression dat = ContractExpansionTransform.reparse("${d}\$q[${j}]")
                if (dat != null) out.add(norm(new BinaryExpression(dat, Token.newSymbol(Types.COMPARE_EQUAL, -1, -1), derivedValue(d, rewriteChExpr(pv, rw), rw)), rw))
            }
        }
        for (String d : info.derived) {
            String dq = d + '$q'
            Expression ds = ContractExpansionTransform.reparse("${dq} != null && ${dq}.size() == ${q}.size()")
            Expression drel = null
            if (info.elementRelation) {
                Expression atK = ContractExpansionTransform.reparse(info.pre == 0 ? "(${k} + ${initText})" : "(${k} - ${info.pre} + ${initText})")
                Expression elem = atK == null ? null : substituteVar(sendE, info.counter, atK)
                Expression shape = ContractExpansionTransform.reparse("Forall.range(${info.pre}, ${dq}.size(), { int ${k} -> ${dq}[${k}] == __E__ })")
                if (elem != null && shape != null) drel = substituteVar(shape, '__E__', derivedValue(d, elem, rw))
            }
            if (stableOnly) { if (drel != null) out.add(norm(drel, rw)); continue }
            if (ds != null && drel != null) out.add(norm(new BinaryExpression(ds, Token.newSymbol(Types.LOGICAL_AND, -1, -1), drel), rw))
            else if (ds != null) out.add(norm(ds, rw))
        }
        out
    }

    /**
     * Phase 260 — a stage's sends never outrun its takes: `own.size() <= taken.size()` for each stream its law is
     * built from, provided the read precedes the send in the body (else it is not stable). A conditional stream's
     * take is the ALT step that guards it. Stable under every partner step, and what a reader needs to carry the
     * FIFO law through: `i < reply.size()` gives `i < request$taken.size()`.
     */
    static List<Expression> sendsFollowTakes(StreamInfo info, ChanRewrite rw) {
        List<Expression> out = new ArrayList<Expression>()
        String q = info.root + '$q'
        ConsumerInfo ci = rw.consumers.get((Statement) info.loop)
        if (ci == null) return out
        Statement lb = info.loop.loopBlock
        List<Statement> top = lb instanceof BlockStatement ? ((BlockStatement) lb).statements : Collections.singletonList(lb)
        int sendAt = topIndexOf(top, info.sendCall)
        Set<String> partners = rw.partnerStreams.get((Statement) info.loop)
        if (info.conditional) {
            int altAt = topIndexOf(top, ci.altFrom)
            if (altAt >= 0 && sendAt >= 0 && altAt < sendAt) {
                Expression e = ContractExpansionTransform.reparse("${q}.size() <= ${info.condChan}\$taken.size()")
                if (e != null) out.add(norm(e, rw))
            }
            return out
        }
        for (Map.Entry<String, MethodCallExpression> al : info.aliases.entrySet()) {
            String v = ci.readOf(al.value)
            if (v == null) continue
            int readAt = topIndexOf(top, al.value)
            if (readAt < 0 || sendAt < 0 || readAt >= sendAt) continue
            String list = (partners != null && partners.contains(rw.rootOf(v))) ? v + '$taken' : v + '$q'
            Expression e = ContractExpansionTransform.reparse("${q}.size() <= ${list}.size()")
            if (e != null) out.add(norm(e, rw))
        }
        out
    }

    /** The index of the top-level statement whose subtree contains {@code node}, or -1. */
    static int topIndexOf(List<Statement> top, final ASTNode node) {
        if (node == null) return -1
        for (int i = 0; i < top.size(); i++) {
            final boolean[] hit = [false]
            top.get(i).visit(new CodeVisitorSupport() {
                @Override void visitMethodCallExpression(MethodCallExpression m) { if (m.is(node)) hit[0] = true; super.visitMethodCallExpression(m) }
                @Override void visitStaticMethodCallExpression(StaticMethodCallExpression m) { if (m.is(node)) hit[0] = true; super.visitStaticMethodCallExpression(m) }
            })
            if (hit[0]) return i
        }
        -1
    }

    /**
     * Phase 260 — the conjuncts of a user invariant a RELY may assume: those that mention no ghost list, and
     * those whose every ghost-list `.size()` / `isEmpty()` is a quantifier bound (`Forall.range(0, c.sent.size(), …)`,
     * `(0..<c.taken.size()).every { … }`) — a count equality over a ghost list holds at the loop head only.
     */
    static List<Expression> stableUserConjuncts(List<Expression> invs) {
        List<Expression> out = new ArrayList<Expression>()
        List<Expression> conj = new ArrayList<Expression>()
        for (Expression inv : invs) splitAnd(inv, conj)
        for (Expression c : conj) if (ghostSizeOnlyInBounds(c)) out.add(c)
        out
    }

    static void splitAnd(Expression e, List<Expression> out) {
        if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.LOGICAL_AND) {
            splitAnd(((BinaryExpression) e).leftExpression, out); splitAnd(((BinaryExpression) e).rightExpression, out)
        } else out.add(e)
    }

    static boolean isGhostList(Expression e) {
        Expression x = stripCasts(e)
        x instanceof VariableExpression && (((VariableExpression) x).name.endsWith('$taken') || ((VariableExpression) x).name.endsWith('$q'))
    }

    static boolean ghostSizeOnlyInBounds(Expression c) {
        final boolean[] bad = [false]
        final int[] boundDepth = [0]
        c.visit(new CodeVisitorSupport() {
            @Override void visitMethodCallExpression(MethodCallExpression m) {
                if ((m.methodAsString == 'size' || m.methodAsString == 'isEmpty') && isGhostList(m.objectExpression) && boundDepth[0] == 0) bad[0] = true
                String recvText = m.objectExpression instanceof ClassExpression ? ((ClassExpression) m.objectExpression).type.nameWithoutPackage : m.objectExpression?.text
                boolean isForall = recvText == 'Forall' || (recvText != null && recvText.endsWith('.Forall'))
                if (isForall) {
                    List<Expression> args = m.arguments instanceof TupleExpression ? ((TupleExpression) m.arguments).expressions : Collections.<Expression>emptyList()
                    for (Expression a : args) { if (a instanceof ClosureExpression) a.visit(this) else { boundDepth[0]++; try { a.visit(this) } finally { boundDepth[0]-- } } }
                    return
                }
                super.visitMethodCallExpression(m)
            }
            @Override void visitStaticMethodCallExpression(StaticMethodCallExpression m) {
                if (m.ownerType?.nameWithoutPackage == 'Forall') {
                    List<Expression> args = m.arguments instanceof TupleExpression ? ((TupleExpression) m.arguments).expressions : Collections.<Expression>emptyList()
                    for (Expression a : args) { if (a instanceof ClosureExpression) a.visit(this) else { boundDepth[0]++; try { a.visit(this) } finally { boundDepth[0]-- } } }
                    return
                }
                super.visitStaticMethodCallExpression(m)
            }
            @Override void visitRangeExpression(RangeExpression r) { boundDepth[0]++; try { super.visitRangeExpression(r) } finally { boundDepth[0]-- } }
        })
        !bad[0]
    }

    /** True when the expression's names are not written by the producer loop (nor channel vars) — a loop constant. */
    static boolean loopConstant(Expression e, StreamInfo info, ChanRewrite rw) {
        for (String n : varNames(e)) if (rw.ch.contains(n) || writesVar(info.loop.loopBlock, n)) return false
        true
    }

    /** Phase 252 — the sent expression with each receive alias (`def v = in.first()` in the same loop) replaced
     *  by the element it read, `in$q[(k + a) - a_c]` — spelled over the relation's index {@code k}. */
    static Expression aliasedSend(StreamInfo info, String k, String initText, ChanRewrite rw) {
        Expression sendE = rewriteChExpr(info.sendExpr, rw)
        ConsumerInfo ci = rw.consumers.get((Statement) info.loop)
        Set<String> partners = rw.partnerStreams.get((Statement) info.loop)
        for (Map.Entry<String, MethodCallExpression> al : info.aliases.entrySet()) {
            String v = ci == null ? null : ci.readOf(al.value)
            if (v == null) continue
            String list = (partners != null && partners.contains(rw.rootOf(v))) ? v + '$taken' : v + '$q'   // Phase 258 — a partner: what was taken
            Expression read = ContractExpansionTransform.reparse(info.pre == 0 ?
                "${list}[(${k} + ${initText}) - ${entryText(ci.counterInit)}]" :
                "${list}[(${k} - ${info.pre} + ${initText}) - ${entryText(ci.counterInit)}]")
            if (read != null) sendE = substituteVar(sendE, al.key, read)
        }
        sendE
    }

    /** The same normalisation the user's captured invariants get (ContractNormalizer against the method). */
    static Expression norm(Expression e, ChanRewrite rw) {
        if (rw.method == null) return e
        Expression n = ContractNormalizer.normalize(e, rw.method)
        n != null ? n : e
    }

    /** Statements of a producer loop body with the stream's sends / closes rewritten (nested blocks and ifs walked). */
    static List<Statement> rewriteStreamStmts(List<Statement> stmts, ChanRewrite rw) {
        boolean savedMode = rw.readsAsTaken
        rw.readsAsTaken = false                                                  // Phase 258 — body reads go through rely views
        try { rewriteStreamStmts0(stmts, rw) } finally { rw.readsAsTaken = savedMode }
    }

    static List<Statement> rewriteStreamStmts0(List<Statement> stmts, ChanRewrite rw) {
        List<Statement> out = new ArrayList<Statement>()
        for (Statement st : stmts) {
            if (st instanceof BlockStatement) {
                BlockStatement b = new BlockStatement(rewriteStreamStmts(((BlockStatement) st).statements, rw), ((BlockStatement) st).variableScope)
                b.setSourcePosition(st); out.add(b); continue
            }
            if (st instanceof IfStatement) {
                IfStatement i = (IfStatement) st
                Statement ib = i.ifBlock, eb = i.elseBlock
                BlockStatement nib = new BlockStatement(rewriteStreamStmts(ib instanceof BlockStatement ? ((BlockStatement) ib).statements : Collections.singletonList(ib), rw), null)
                Statement neb = (eb == null || eb instanceof EmptyStatement) ? EmptyStatement.INSTANCE :
                    new BlockStatement(rewriteStreamStmts(eb instanceof BlockStatement ? ((BlockStatement) eb).statements : Collections.singletonList(eb), rw), null)
                IfStatement ni = new IfStatement(new BooleanExpression(rewriteChExpr(i.booleanExpression.expression, rw)), nib, neb)
                ni.setSourcePosition(st); ni.copyNodeMetaData(st); out.add(ni); continue
            }
            if (st instanceof ExpressionStatement) {
                Expression e = ((ExpressionStatement) st).expression
                if (rw.curConsumer != null && rw.curConsumer.altVar != null && e instanceof DeclarationExpression &&
                    ((DeclarationExpression) e).leftExpression instanceof VariableExpression &&
                    ((VariableExpression) ((DeclarationExpression) e).leftExpression).name == rw.curConsumer.altVar &&
                    awaitedSelectArgs(((DeclarationExpression) e).rightExpression, rw.selectRefs) != null) {
                    out.addAll(loopingAlt((DeclarationExpression) e, rw))       // Phase 253
                    continue
                }
                List<Statement> after = new ArrayList<Statement>()
                for (MethodCallExpression r : sanctionedReceivesIn(e, rw)) {   // Phase 252 — the element must exist
                    String v = rw.curConsumer == null ? null : rw.curConsumer.readOf(r)
                    if (v != null && rw.partner(v)) {                            // Phase 258 — read through a rely view
                        out.addAll(relyBlock(Collections.singletonList(v), rw, r))
                        Statement t = takenAppend(v, rw, r)
                        if (t != null) after.add(t)
                    }
                    out.addAll(consumerAssert(r, rw))
                }
                if (e instanceof MethodCallExpression) {
                    MethodCallExpression m = (MethodCallExpression) e
                    Expression recv = stripCasts(m.objectExpression)
                    String c = recv instanceof VariableExpression ? ((VariableExpression) recv).name : null
                    StreamInfo info = c == null ? null : rw.streams.get(c)
                    if (info != null && m.methodAsString == 'close') continue
                    if (info != null && m.methodAsString == 'send') {
                        Expression val = rewriteChExpr(info.sendExpr, rw)
                        List<long[]> bs = rw.bounds.get(c)
                        if (bs != null && !bs.isEmpty()) out.add(boundsAssert(val, bs, m))
                        out.add(addStmt(c + '$q', val, m))
                        for (String d : info.derived) out.add(addStmt(d + '$q', derivedValue(d, val, rw), m))
                        out.addAll(after)
                        continue
                    }
                }
                ExpressionStatement ns = new ExpressionStatement(rewriteChExpr(e, rw))
                ns.setSourcePosition(st); ns.copyNodeMetaData(st); out.add(ns); out.addAll(after); continue
            }
            if (st instanceof ReturnStatement) {
                Expression r = ((ReturnStatement) st).expression
                ReturnStatement nr = new ReturnStatement(r == null ? null : rewriteChExpr(r, rw))
                nr.setSourcePosition(st); out.add(nr); continue
            }
            if (st instanceof AssertStatement) {                                  // Phase 259 — a body assert may name `c.taken`
                AssertStatement as0 = (AssertStatement) st
                AssertStatement na = new AssertStatement(new BooleanExpression(rewriteChExpr(as0.booleanExpression.expression, rw)), as0.messageExpression)
                na.setSourcePosition(st); na.copyNodeMetaData(st); out.add(na); continue
            }
            out.add(st)
        }
        out
    }

    static Statement addStmt(String list, Expression val, ASTNode at) {
        MethodCallExpression add = new MethodCallExpression(new VariableExpression(list), 'add', new ArgumentListExpression(val))
        add.setSourcePosition(at)
        ExpressionStatement st = new ExpressionStatement(add)
        st.setSourcePosition(at)
        st
    }

    /** Phase 251 — a `for (v in c)` drain of a streaming channel: the same loop over the shadow list, its
     *  LoopSpec renamed to match (the loop engine then decides — a per-element body proves, an accumulating
     *  one is its loud skip). */
    static Statement streamDrainLoop(ForStatement st, String q, String c, ChanRewrite rw) {
        VariableExpression coll = new VariableExpression(q)
        coll.setSourcePosition(st.collectionExpression)
        ForStatement out = new ForStatement(st.variable, coll, st.loopBlock)
        out.setSourcePosition(st); out.copyNodeMetaData(st)
        LoopSpec spec = (LoopSpec) st.getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY)
        if (spec != null) {
            Map<String, Expression> ren = new HashMap<String, Expression>()
            ren.put(c, new VariableExpression(q))
            out.putNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY, renameSpec(spec, ren))
        }
        out
    }

    /**
     * Phase 262 — the DRAIN of a cycle partner's stream, `for (v in c) { … reply.send(f(v)) … }`, where c is
     * produced by a unit-counter loop in another process that receives what the drain sends and closes c after
     * its loop (or never terminates — then the drain never ends either). Rebuilt — arms are rebuilt, never
     * mutated — as the counter loop the cycle model reads directly:
     * <pre>
     *   int c$d = 0
     *   while (c$d < TOTAL) { T v = c.first(); …; c$d = c$d + 1 }     // TOTAL from the producer's guard
     * </pre>
     * with a synthesized LoopSpec (`0 <= c$d && c$d <= TOTAL`, variant `TOTAL - c$d`; `while (true)` for a
     * non-terminating producer). The drain's reads are then partner reads (rely views, taken-ghost, the
     * read-below-total obligation — trivially met, the drain reads exactly what is sent), its sends a stream
     * of TOTAL elements, and the client's reads of the replies carry their own obligation against that.
     */
    static BlockStatement desugarPartnerDrains(BlockStatement body, Set<String> ch, Set<String> params) {
        List<List<Statement>> blocks = topLevelBlocks(body)
        Map<String, Object[]> loopSend = new HashMap<String, Object[]>()           // channel → [producer loop, its block]
        for (List<Statement> block : blocks) {
            for (Statement st : block) {
                if (!(st instanceof LoopingStatement)) continue
                Statement lb = ((LoopingStatement) st).loopBlock
                List<Statement> top = lb instanceof BlockStatement ? ((BlockStatement) lb).statements : Collections.singletonList(lb)
                for (Statement inner : top) {
                    MethodCallExpression call = sendCallOf(inner, ch)
                    if (call != null) loopSend.put(((VariableExpression) stripCasts(call.objectExpression)).name, [st, block] as Object[])
                }
            }
        }
        Map<Statement, List<Statement>> replace = new IdentityHashMap<Statement, List<Statement>>()
        for (List<Statement> block : blocks) {
            for (Statement st : block) {
                if (!(st instanceof ForStatement)) continue
                ForStatement f = (ForStatement) st
                Expression coll = stripCasts(f.collectionExpression)
                if (!(coll instanceof VariableExpression) || !ch.contains(((VariableExpression) coll).name)) continue
                String c = ((VariableExpression) coll).name
                Object[] ls = loopSend.get(c)
                if (ls == null) continue
                LoopingStatement pl = (LoopingStatement) ls[0]
                List<Statement> pb = (List<Statement>) ls[1]
                if (pb.is(block)) continue                                       // the same process: not a partner's
                Set<String> drainSends = channelOps(f.loopBlock, ch, true)
                Set<String> prodReads = channelOps(pl.loopBlock, ch, false)
                if (drainSends.intersect(prodReads).isEmpty()) continue           // no cycle: Phase 251's drain
                String[] w = [null]
                Object[] cnt = unitCounter(pl, pb, params, w)
                if (cnt == null) continue
                boolean infinite = isForever(pl)
                String total = null
                if (!infinite) {
                    StreamInfo tmp = new StreamInfo()
                    tmp.root = c; tmp.loop = pl; tmp.counter = (String) cnt[0]; tmp.counterInit = (Expression) cnt[1]; tmp.infinite = false
                    boolean after = false, closed = false
                    for (Statement s0 : pb) {
                        if (s0.is((Statement) pl)) { after = true; continue }
                        MethodCallExpression pc = sendCallOf(s0, ch)
                        if (!after && pc != null && ((VariableExpression) stripCasts(pc.objectExpression)).name == c) tmp.pre++
                        if (after && s0 instanceof ExpressionStatement && ((ExpressionStatement) s0).expression instanceof MethodCallExpression) {
                            MethodCallExpression m = (MethodCallExpression) ((ExpressionStatement) s0).expression
                            Expression r = stripCasts(m.objectExpression)
                            if (m.methodAsString == 'close' && r instanceof VariableExpression && ((VariableExpression) r).name == c) closed = true
                        }
                    }
                    total = staticTotalText(tmp, ch)
                    if (total == null || !closed) continue                       // no static total / never closed: Phase 251 decides
                }
                String d = c + '$d'
                ClassNode vt = f.variable.isDynamicTyped() ? ClassHelper.int_TYPE : f.variable.type
                MethodCallExpression first = new MethodCallExpression(new VariableExpression(c), 'first', ArgumentListExpression.EMPTY_ARGUMENTS)
                first.setSourcePosition(f.collectionExpression)
                DeclarationExpression vd = new DeclarationExpression(new VariableExpression(f.variable.name, vt), Token.newSymbol(Types.ASSIGN, f.lineNumber, f.columnNumber), first)
                vd.setSourcePosition(f)
                ExpressionStatement vds = new ExpressionStatement(vd); vds.setSourcePosition(f)
                Expression step = ContractExpansionTransform.reparse("${d} = ${d} + 1")
                Expression guard = infinite ? new ConstantExpression(true) : ContractExpansionTransform.reparse("${d} < ${total}")
                Expression inv = ContractExpansionTransform.reparse(infinite ? "${d} >= 0" : "0 <= ${d} && ${d} <= ${total}")
                Expression variant = infinite ? null : ContractExpansionTransform.reparse("${total} - ${d}")
                if (step == null || guard == null || inv == null) continue
                ExpressionStatement steps = new ExpressionStatement(step); steps.setSourcePosition(f)
                List<Statement> bodyStmts = new ArrayList<Statement>()
                bodyStmts.add(vds)
                bodyStmts.addAll(f.loopBlock instanceof BlockStatement ? ((BlockStatement) f.loopBlock).statements : Collections.singletonList(f.loopBlock))
                bodyStmts.add(steps)
                BlockStatement nb = new BlockStatement(bodyStmts, f.loopBlock instanceof BlockStatement ? ((BlockStatement) f.loopBlock).variableScope : null)
                nb.setSourcePosition(f.loopBlock)
                WhileStatement ws = new WhileStatement(new BooleanExpression(guard), nb)
                ws.setSourcePosition(f)
                LoopSpec spec = new LoopSpec()
                spec.invariants = [inv] as List<Expression>
                spec.variant = variant
                spec.guard = guard
                spec.body = bodyStmts
                ws.putNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY, spec)
                DeclarationExpression dd = new DeclarationExpression(new VariableExpression(d, ClassHelper.int_TYPE), Token.newSymbol(Types.ASSIGN, f.lineNumber, f.columnNumber), new ConstantExpression(0, true))
                dd.setSourcePosition(f)
                ExpressionStatement dds = new ExpressionStatement(dd); dds.setSourcePosition(f)
                replace.put(st, [dds, ws] as List<Statement>)
            }
        }
        if (replace.isEmpty()) return body
        List<Statement> out = new ArrayList<Statement>()
        for (Statement st : body.statements) {
            if (replace.containsKey(st)) { out.addAll(replace.get(st)); continue }
            Expression call = null, e = null
            if (st instanceof ExpressionStatement) {
                e = ((ExpressionStatement) st).expression
                call = e
                if (e instanceof DeclarationExpression) call = stripCasts(((DeclarationExpression) e).rightExpression)
                else if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.ASSIGN) call = stripCasts(((BinaryExpression) e).rightExpression)
            }
            ClosureExpression cl = call == null ? null : asyncClosure(call)
            if (cl == null || !(cl.code instanceof BlockStatement) || !((BlockStatement) cl.code).statements.any { Statement x -> replace.containsKey(x) }) { out.add(st); continue }
            List<Statement> ns = new ArrayList<Statement>()
            for (Statement x : ((BlockStatement) cl.code).statements) { if (replace.containsKey(x)) ns.addAll(replace.get(x)) else ns.add(x) }
            BlockStatement copy = new BlockStatement(ns, ((BlockStatement) cl.code).variableScope)
            copy.setSourcePosition(cl.code); copy.copyNodeMetaData(cl.code)
            Expression rebuilt = rebuildAsyncCall(call, cl, copy)
            Expression ne
            if (e instanceof DeclarationExpression) ne = new DeclarationExpression(((DeclarationExpression) e).leftExpression, ((DeclarationExpression) e).operation, rebuilt)
            else if (e instanceof BinaryExpression) ne = new BinaryExpression(((BinaryExpression) e).leftExpression, ((BinaryExpression) e).operation, rebuilt)
            else ne = rebuilt
            ne.setSourcePosition(e); ne.copyNodeMetaData(e)
            ExpressionStatement nst = new ExpressionStatement(ne)
            nst.setSourcePosition(st); nst.copyNodeMetaData(st)
            out.add(nst)
        }
        BlockStatement nb = new BlockStatement(out, body.variableScope)
        nb.setSourcePosition(body); nb.copyNodeMetaData(body)
        nb
    }

    /** The channel vars a statement sends on ({@code sends}) or receives from (first / awaited receive). */
    static Set<String> channelOps(Statement st, Set<String> ch, boolean sends) {
        final Set<String> out = new LinkedHashSet<String>()
        if (st == null) return out
        st.visit(new CodeVisitorSupport() {
            @Override void visitMethodCallExpression(MethodCallExpression m) {
                Expression r = stripCasts(m.objectExpression)
                if (r instanceof VariableExpression && ch.contains(((VariableExpression) r).name)) {
                    String mm = m.methodAsString
                    if (sends ? mm == 'send' : (mm == 'first' || mm == 'receive')) out.add(((VariableExpression) r).name)
                }
                super.visitMethodCallExpression(m)
            }
        })
        out
    }

    /** Phase 252 — arm locals renamed apart from the body's (and earlier arms') locals before the flattening:
     *  two loops naturally both count with `i`, and the flattened single-assignment model would conflate them.
     *  Arms are rebuilt, never mutated; an arm whose body the renamer cannot copy is left as is. */
    static BlockStatement alphaRenameArms(BlockStatement body) {
        Set<String> taken = new HashSet<String>()
        collectBodyLocalNames(body, taken)
        List<Statement> out = new ArrayList<Statement>()
        boolean changed = false
        int armNo = 0
        for (Statement st : body.statements) {
            Expression call = null, e = null
            if (st instanceof ExpressionStatement) {
                e = ((ExpressionStatement) st).expression
                call = e
                if (e instanceof DeclarationExpression) call = stripCasts(((DeclarationExpression) e).rightExpression)
                else if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.ASSIGN) call = stripCasts(((BinaryExpression) e).rightExpression)
            }
            ClosureExpression cl = call == null ? null : asyncClosure(call)
            if (cl == null || !(cl.code instanceof BlockStatement)) { out.add(st); continue }
            armNo++
            Set<String> locals = new HashSet<String>()
            collectBodyLocalNames((BlockStatement) cl.code, locals)
            Map<String, Expression> ren = new HashMap<String, Expression>()
            for (String l : locals) if (taken.contains(l)) ren.put(l, new VariableExpression(l + '$a' + armNo))
            for (String l : locals) taken.add(ren.containsKey(l) ? ((VariableExpression) ren.get(l)).name : l)
            if (ren.isEmpty()) { out.add(st); continue }
            Statement copy = copyRenamed(cl.code, ren, true)
            if (!(copy instanceof BlockStatement)) { out.add(st); continue }
            Expression rebuilt = rebuildAsyncCall(call, cl, (BlockStatement) copy)
            Expression ne
            if (e instanceof DeclarationExpression) ne = new DeclarationExpression(((DeclarationExpression) e).leftExpression, ((DeclarationExpression) e).operation, rebuilt)
            else if (e instanceof BinaryExpression) ne = new BinaryExpression(((BinaryExpression) e).leftExpression, ((BinaryExpression) e).operation, rebuilt)
            else ne = rebuilt
            ne.setSourcePosition(e); ne.copyNodeMetaData(e)
            ExpressionStatement ns = new ExpressionStatement(ne)
            ns.setSourcePosition(st); ns.copyNodeMetaData(st)
            out.add(ns)
            changed = true
        }
        if (!changed) return body
        BlockStatement nb = new BlockStatement(out, body.variableScope)
        nb.setSourcePosition(body); nb.copyNodeMetaData(body)
        nb
    }

    // ── Phase 248 — bounded streaming: literal-bounded channel loops unroll ────────────────────
    //
    // A loop that carries channel traffic is "not one-shot" to the ladder: its ops are conditional
    // to the structural walk (Phase 243) and beyond the bounded FIFO (Phase 247). When the loop's
    // bound is a LITERAL — `for (i in 0..<3)`, `for (i in 1..3)`, `for (int i = 0; i < 3; i++)` —
    // the trip count is static, and unrolling it (body copied per iteration, the index a constant,
    // the body's locals renamed apart) turns the stream into straight-line one-shot traffic that
    // every later pass certifies exactly: the sends are indexed, the receives paired, the drains
    // unrolled, the wait-for order well-founded. Runs BEFORE the structural walk on a fresh copy of
    // the body (async arms rebuilt, never mutated — their nodes are shared with the live AST).
    // Honest boundary: literal bounds only, up to CHANNEL_UNROLL_LIMIT — a symbolic bound (`0..<n`)
    // is the streaming frontier proper (symbolic counts carried by loop invariants), not unrolled.

    /** The unrolling ceiling — bounded model checking, kept small enough to stay a compile-time proof. */
    static final int CHANNEL_UNROLL_LIMIT = 32

    /** Phase 257 — a `ChannelSelect` chain: its channel args, its policy, and whether it is a held instance. */
    static class SelectRef {
        List<Expression> chans
        String policy = 'priority'       // priority | fair | random
        boolean held                     // `val alt = ChannelSelect.from(..)[.fair()]` before the loop, `alt.select()` inside
        boolean guarded                  // Phase 273 — built by a condition (JCSP's precondition mask), so a branch may not be offered
        boolean indexUnstable            // Phase 273 — …and its arms disagree on WHICH channel is branch i
        Expression fromCall              // the from(..) call (identity)
        List<Expression> fromCalls = new ArrayList<Expression>()   // Phase 273 — every arm's from() (one, or both of a guarded ternary)
        String varName                   // the held var, when held
    }

    /** `ChannelSelect.from(c…)[.fair()|.random()]` → its SelectRef; anything else → null. */
    static SelectRef selectChainInfo(Expression e) {
        Expression x = stripCasts(e)
        // Phase 273 — a GUARDED ALT: `counter == 0 ? from(put) : from(put, get)`, the varargs spelling of
        // JCSP's precondition mask (`select(preCon)` with preCon[GET] = counter > 0). Both arms must be
        // select chains of the same policy, and — the condition that makes `r.index` mean anything — the
        // channel lists must AGREE POSITIONALLY as far as they go, so a branch keeps its index whether or
        // not it is offered. (JCSP's mask keeps indices stable by construction; a positional `from(…)`
        // does not, so the checker has to demand it.) The union is the ALT's branch list.
        if (x instanceof TernaryExpression) {
            TernaryExpression t = (TernaryExpression) x
            SelectRef a = selectChainInfo(t.trueExpression), b = selectChainInfo(t.falseExpression)
            if (a == null || b == null || a.policy != b.policy) return null
            List<Expression> wide = a.chans.size() >= b.chans.size() ? a.chans : b.chans
            List<Expression> narrow = a.chans.size() >= b.chans.size() ? b.chans : a.chans
            boolean unstable = a.indexUnstable || b.indexUnstable
            for (int i = 0; i < narrow.size(); i++) {
                String n = chanNameOf(narrow.get(i))
                if (n == null || n != chanNameOf(wide.get(i))) { unstable = true; break }
            }
            // Still a ChannelSelect either way — recognising the SHAPE is what keeps a bogus "select() on
            // null object" off a perfectly good guarded ALT. Whether its indices mean anything is a separate
            // verdict, carried by indexUnstable and reported on its own.
            SelectRef r = new SelectRef(); r.chans = wide; r.policy = a.policy; r.fromCall = a.fromCall
            r.fromCalls.addAll(a.fromCalls); r.fromCalls.addAll(b.fromCalls)
            r.guarded = true; r.indexUnstable = unstable
            return r
        }
        String policy = 'priority'
        while (x instanceof MethodCallExpression && (((MethodCallExpression) x).methodAsString == 'fair' || ((MethodCallExpression) x).methodAsString == 'random') && noArgs((MethodCallExpression) x)) {
            policy = ((MethodCallExpression) x).methodAsString
            x = stripCasts(((MethodCallExpression) x).objectExpression)
        }
        List<Expression> args = selectFromArgs(x)
        if (args == null) {
            // Phase 280 — `ChannelSelect.offers(receive(a), send(b, v), …)`, GROOVY-12323's spelling. Before
            // this it was not recognised as a select at all, so a HELD one raised an undischargeable
            // "select() on null object" — the same false positive the conditional select had in Phase 273
            // and a `new`-bound local in Phase 277, in a third place.
            List<Expression> offers = selectOffersArgs(x)
            if (offers == null) return null
            List<Expression> chans = new ArrayList<Expression>()
            for (Expression o : offers) {
                Expression c = offerChannelOf(o)
                if (c == null) return null              // an offer shape we do not model: not a select we claim
                chans.add(c)
            }
            SelectRef ro = new SelectRef(); ro.chans = chans; ro.policy = policy; ro.fromCall = x
            ro.fromCalls.add(x)
            return ro
        }
        SelectRef r = new SelectRef(); r.chans = args; r.policy = policy; r.fromCall = x
        r.fromCalls.add(x)
        r
    }

    /** Held select instances: `X = ChannelSelect.from(..)[.policy()]` declarations anywhere in the body. */
    static Map<String, SelectRef> collectSelectVars(Statement body) {
        final Map<String, SelectRef> out = new HashMap<String, SelectRef>()
        if (body == null) return out
        body.visit(new CodeVisitorSupport() {
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (de.leftExpression instanceof VariableExpression) {
                    SelectRef r = selectChainInfo(de.rightExpression)
                    if (r != null) { r.held = true; r.varName = ((VariableExpression) de.leftExpression).name; out.put(r.varName, r) }
                }
                super.visitDeclarationExpression(de)
            }
        })
        out
    }

    /** `await X.select()` (either await shape): X an inline chain or a held var → its SelectRef (plus the select call). */
    static SelectRef awaitedSelect(Expression rhs, Map<String, SelectRef> selectVars) {
        MethodCallExpression sel = awaitedSelectCall(rhs)
        if (sel == null) return null
        selectRefOf(sel.objectExpression, selectVars)
    }

    static SelectRef selectRefOf(Expression receiver, Map<String, SelectRef> selectVars) {
        Expression x = stripCasts(receiver)
        if (x instanceof VariableExpression && selectVars != null && selectVars.containsKey(((VariableExpression) x).name)) return selectVars.get(((VariableExpression) x).name)
        selectChainInfo(x)
    }

    /** The `select()` call inside `await …`, else null. Phase 275 — arguments are admitted, because
     *  GROOVY-12324's `select(boolean... enabled)` carries one precondition flag per offer; before it,
     *  any argument meant "not the shape we model" and the ALT was invisible to every pass. */
    static MethodCallExpression awaitedSelectCall(Expression rhs) {
        Expression x = stripCasts(rhs)
        Expression inner = null
        if (x instanceof MethodCallExpression && ((MethodCallExpression) x).methodAsString == 'await') inner = ((MethodCallExpression) x).arguments
        else if (x instanceof StaticMethodCallExpression && ((StaticMethodCallExpression) x).method == 'await') inner = ((StaticMethodCallExpression) x).arguments
        if (!(inner instanceof TupleExpression) || ((TupleExpression) inner).expressions.size() != 1) return null
        Expression sel = stripCasts(((TupleExpression) inner).expressions.get(0))
        (sel instanceof MethodCallExpression && ((MethodCallExpression) sel).methodAsString == 'select') ? (MethodCallExpression) sel : null
    }

    /** Phase 252 — node metadata on a synthesized {@code assert}: the sentence the diagnostic reports instead of the condition text. */
    static final String ASSERT_LABEL_KEY = 'verification.assertLabel'
    /** Phase 254 — node metadata on a synthesized {@code assert} that is ASSUMED, not discharged: a liveness fact
     *  (an element of a non-terminating producer's stream exists) that the network check reports as not claimed. */
    static final String ASSUME_ONLY_KEY = 'verification.assumeOnly'

    /** A new body with every literal-bounded channel loop unrolled; the SAME body when there is none. */
    static Statement unrollLiteralChannelLoops(Statement body, Set<String> ch) {
        if (!(body instanceof BlockStatement) || ch.isEmpty()) return body
        boolean[] changed = [false]
        BlockStatement out = unrollBlock((BlockStatement) body, ch, changed, 0)
        changed[0] ? out : body
    }

    static BlockStatement unrollBlock(BlockStatement b, Set<String> ch, boolean[] changed, int depth) {
        List<Statement> out = new ArrayList<Statement>()
        for (Statement st : b.statements) unrollInto(st, ch, changed, out, depth)
        BlockStatement nb = new BlockStatement(out, b.variableScope)
        nb.setSourcePosition(b); nb.copyNodeMetaData(b)
        nb
    }

    static void unrollInto(Statement st, Set<String> ch, boolean[] changed, List<Statement> out, int depth) {
        if (depth <= 8 && st instanceof ForStatement && mentionsChannelOp(st, ch)) {
            List<Statement> copies = unrollLiteralLoop((ForStatement) st, ch)
            if (copies != null) {
                changed[0] = true
                for (Statement c : copies) unrollInto(c, ch, changed, out, depth + 1)   // nested literal loops
                return
            }
        }
        if (st instanceof ExpressionStatement) {
            Expression e = ((ExpressionStatement) st).expression
            Expression call = e
            if (e instanceof DeclarationExpression) call = stripCasts(((DeclarationExpression) e).rightExpression)
            else if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.ASSIGN) call = stripCasts(((BinaryExpression) e).rightExpression)
            ClosureExpression cl = asyncClosure(call)
            if (cl != null && cl.code instanceof BlockStatement && mentionsChannelOp(cl.code, ch)) {
                boolean[] inner = [false]
                BlockStatement nb = unrollBlock((BlockStatement) cl.code, ch, inner, depth)
                if (inner[0]) {
                    changed[0] = true
                    Expression rebuilt = rebuildAsyncCall(call, cl, nb)
                    Expression ne
                    if (e instanceof DeclarationExpression) {
                        DeclarationExpression de = (DeclarationExpression) e
                        ne = new DeclarationExpression(de.leftExpression, de.operation, rebuilt)
                    } else if (e instanceof BinaryExpression) {
                        BinaryExpression be = (BinaryExpression) e
                        ne = new BinaryExpression(be.leftExpression, be.operation, rebuilt)
                    } else {
                        ne = rebuilt
                    }
                    ne.setSourcePosition(e); ne.copyNodeMetaData(e)
                    ExpressionStatement ns = new ExpressionStatement(ne)
                    ns.setSourcePosition(st); ns.copyNodeMetaData(st)
                    out.add(ns)
                    return
                }
            }
        }
        out.add(st)
    }

    /** The `async { … }` call with its closure's code replaced — both post-STC shapes. */
    static Expression rebuildAsyncCall(Expression call, ClosureExpression cl, BlockStatement code) {
        ClosureExpression ncl = new ClosureExpression(cl.parameters, code)
        ncl.setVariableScope(cl.variableScope)
        ncl.setSourcePosition(cl); ncl.copyNodeMetaData(cl)
        ArgumentListExpression args = new ArgumentListExpression(ncl)
        Expression out
        if (call instanceof StaticMethodCallExpression) {
            StaticMethodCallExpression sm = (StaticMethodCallExpression) call
            out = new StaticMethodCallExpression(sm.ownerType, sm.method, args)
        } else {
            MethodCallExpression m = (MethodCallExpression) call
            MethodCallExpression nm = new MethodCallExpression(m.objectExpression, m.method, args)
            nm.setImplicitThis(m.implicitThis)
            out = nm
        }
        out.setSourcePosition(call); out.copyNodeMetaData(call)
        out
    }

    /** True when the statement performs any channel end-use: a call on a channel var, or a for-in over one. */
    static boolean mentionsChannelOp(Statement s, Set<String> ch) {
        if (s == null) return false
        boolean[] found = [false]
        s.visit(new CodeVisitorSupport() {
            @Override void visitMethodCallExpression(MethodCallExpression m) {
                Expression recv = stripCasts(m.objectExpression)
                if (recv instanceof VariableExpression && ch.contains(((VariableExpression) recv).name)) found[0] = true
                super.visitMethodCallExpression(m)
            }
            @Override void visitForLoop(ForStatement f) {
                Expression coll = stripCasts(f.collectionExpression)
                if (coll instanceof VariableExpression && ch.contains(((VariableExpression) coll).name)) found[0] = true
                super.visitForLoop(f)
            }
        })
        found[0]
    }

    /** The unrolled copies of a literal-bounded loop, or null when it is not one (symbolic bound,
     *  descending / non-integer range, over the limit, a body that writes the index, or a body shape
     *  outside the copying fragment). */
    static List<Statement> unrollLiteralLoop(ForStatement f, Set<String> ch) {
        Object[] lit = literalLoopRange(f)
        if (lit == null) return null
        String index = (String) lit[0]
        int from = (Integer) lit[1], to = (Integer) lit[2]
        if (to < from - 1) return null                            // a descending range iterates backwards — out
        int n = to - from + 1
        if (n > CHANNEL_UNROLL_LIMIT) return null
        Statement body = f.loopBlock
        if (!unrollableStreamBody(body) || writesVar(body, index)) return null
        BlockStatement block = body instanceof BlockStatement ? (BlockStatement) body :
            new BlockStatement(Collections.singletonList(body), null)
        Set<String> locals = new HashSet<String>()
        collectBodyLocalNames(block, locals)
        List<Statement> out = new ArrayList<Statement>()
        for (int k = 0; k < n; k++) {
            Map<String, Expression> ren = new HashMap<String, Expression>()
            ren.put(index, new ConstantExpression(from + k, true))
            for (String l : locals) ren.put(l, new VariableExpression(l + '$' + (k + 1)))
            Statement copy = copyRenamed(block, ren)
            if (copy == null) return null
            out.addAll(((BlockStatement) copy).statements)
        }
        out
    }

    /** `[indexName, from, to]` (inclusive) for `for (i in a..b)`, `for (i in a..<b)` and
     *  `for (int i = a; i < b; i++)` / `i <= b` with literal int bounds; null otherwise. */
    static Object[] literalLoopRange(ForStatement f) {
        Expression coll = stripCasts(f.collectionExpression)
        if (coll instanceof RangeExpression) {
            RangeExpression r = (RangeExpression) coll
            Integer a = intLiteral(r.from), b = intLiteral(r.to)
            if (a == null || b == null || f.variable == null) return null
            return [f.variable.name, a, r.inclusive ? b : b - 1] as Object[]
        }
        if (coll instanceof ClosureListExpression) {
            List<Expression> parts = ((ClosureListExpression) coll).expressions
            if (parts.size() != 3) return null
            Expression init = stripCasts(parts.get(0)), cond = stripCasts(parts.get(1)), upd = stripCasts(parts.get(2))
            if (!(init instanceof DeclarationExpression) || !(((DeclarationExpression) init).leftExpression instanceof VariableExpression)) return null
            String i = ((VariableExpression) ((DeclarationExpression) init).leftExpression).name
            Integer a = intLiteral(((DeclarationExpression) init).rightExpression)
            if (a == null || !(cond instanceof BinaryExpression)) return null
            BinaryExpression c = (BinaryExpression) cond
            if (!(stripCasts(c.leftExpression) instanceof VariableExpression) || ((VariableExpression) stripCasts(c.leftExpression)).name != i) return null
            Integer b = intLiteral(c.rightExpression)
            if (b == null) return null
            int t = c.operation.type
            int to = t == Types.COMPARE_LESS_THAN ? b - 1 : (t == Types.COMPARE_LESS_THAN_EQUAL ? b : Integer.MIN_VALUE)
            if (to == Integer.MIN_VALUE) return null
            Expression target = upd instanceof PostfixExpression ? ((PostfixExpression) upd).expression :
                                upd instanceof PrefixExpression ? ((PrefixExpression) upd).expression : null
            int op = upd instanceof PostfixExpression ? ((PostfixExpression) upd).operation.type :
                     upd instanceof PrefixExpression ? ((PrefixExpression) upd).operation.type : -1
            if (op != Types.PLUS_PLUS || !(stripCasts(target) instanceof VariableExpression) ||
                ((VariableExpression) stripCasts(target)).name != i) return null
            return [i, a, to] as Object[]
        }
        null
    }

    static Integer intLiteral(Expression e) {
        Expression x = stripCasts(e)
        if (x instanceof ConstantExpression && ((ConstantExpression) x).value instanceof Integer) return (Integer) ((ConstantExpression) x).value
        null
    }

    /** The loop-body shapes the stream unroller copies: blocks, expressions, returns, if/else — and
     *  nested `for` loops (a literal inner loop unrolls in turn; any other stays a loop, and its
     *  channel ops stay conditional — a loud skip, never a wrong count). */
    static boolean unrollableStreamBody(Statement s) {
        if (s == null || s instanceof EmptyStatement) return true
        if (s instanceof BlockStatement) {
            for (Statement st : ((BlockStatement) s).statements) if (!unrollableStreamBody(st)) return false
            return true
        }
        if (s instanceof IfStatement) {
            IfStatement i = (IfStatement) s
            return unrollableStreamBody(i.ifBlock) && unrollableStreamBody(i.elseBlock)
        }
        if (s instanceof ForStatement) return unrollableStreamBody(((ForStatement) s).loopBlock)
        s instanceof ExpressionStatement || s instanceof ReturnStatement
    }

    /** True when the body assigns / increments the named variable (an index the copies could not freeze). */
    static boolean writesVar(Statement s, String name) {
        boolean[] w = [false]
        s.visit(new CodeVisitorSupport() {
            @Override void visitBinaryExpression(BinaryExpression be) {
                int t = be.operation.type
                if ((t == Types.ASSIGN || Types.ofType(t, Types.ASSIGNMENT_OPERATOR)) &&
                    be.leftExpression instanceof VariableExpression && ((VariableExpression) be.leftExpression).name == name) w[0] = true
                super.visitBinaryExpression(be)
            }
            @Override void visitPostfixExpression(PostfixExpression e) {
                if (e.expression instanceof VariableExpression && ((VariableExpression) e.expression).name == name) w[0] = true
                super.visitPostfixExpression(e)
            }
            @Override void visitPrefixExpression(PrefixExpression e) {
                if (e.expression instanceof VariableExpression && ((VariableExpression) e.expression).name == name) w[0] = true
                super.visitPrefixExpression(e)
            }
        })
        w[0]
    }
}
