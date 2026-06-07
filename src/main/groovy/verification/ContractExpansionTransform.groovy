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
import org.codehaus.groovy.ast.builder.AstBuilder
import org.codehaus.groovy.ast.AnnotationNode
import org.codehaus.groovy.ast.ClassHelper
import org.codehaus.groovy.ast.ClassNode
import org.codehaus.groovy.ast.ConstructorNode
import org.codehaus.groovy.ast.ImportNode
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.ModuleNode
import org.codehaus.groovy.ast.VariableScope
import org.codehaus.groovy.ast.expr.AnnotationConstantExpression
import org.codehaus.groovy.ast.expr.BooleanExpression
import org.codehaus.groovy.ast.expr.BinaryExpression
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.expr.ClosureListExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.EmptyExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.ListExpression
import org.codehaus.groovy.ast.expr.PostfixExpression
import org.codehaus.groovy.ast.expr.PrefixExpression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.ast.stmt.AssertStatement
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.DoWhileStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.ForStatement
import org.codehaus.groovy.ast.stmt.LoopingStatement
import org.codehaus.groovy.ast.stmt.Statement
import org.codehaus.groovy.ast.stmt.WhileStatement
import org.codehaus.groovy.syntax.Types
import org.codehaus.groovy.control.CompilePhase
import org.codehaus.groovy.control.Janitor
import org.codehaus.groovy.control.SourceUnit
import org.codehaus.groovy.runtime.powerassert.SourceText
import org.codehaus.groovy.transform.ASTTransformation
import org.codehaus.groovy.transform.GroovyASTTransformation

/**
 * Global transform, {@code CONVERSION} phase. Augments every method carrying a
 * {@code groovy.contracts.Requires}/{@code Ensures} with a {@link ContractSource}
 * holding the verbatim source text of its contract closures.
 *
 * Purely additive: it neither rewrites nor removes the contracts annotations, so
 * groovy-contracts proceeds untouched and generates the runtime checks.
 *
 * Why {@code CONVERSION} and why global: the contract closure must be read while
 * it is still a {@link ClosureExpression}. groovy-contracts erases it into a
 * generated closure class during its own {@code SEMANTIC_ANALYSIS} global pass,
 * and global transforms in that phase run before any collector expansion or
 * local transform — so the only place guaranteed to see the intact closure
 * ahead of groovy-contracts is the earlier {@code CONVERSION} phase, which only
 * global transforms can occupy.
 *
 * Verbatim text comes from power-assert's {@link SourceText} (rather than
 * {@code Expression.getText()}) so the captured string is byte-for-byte the
 * author's source.
 */
@CompileStatic
@GroovyASTTransformation(phase = CompilePhase.CONVERSION)
class ContractExpansionTransform implements ASTTransformation {

    private static final String CONTRACTS_PKG = 'groovy.contracts.'

    /**
     * Node-metadata key under which a clean snapshot of a postcondition method's
     * body is stashed. {@link VerifyChecker} enumerates return paths over this
     * rather than {@code method.getCode()}, because groovy-contracts mutates the
     * real body in place at INSTRUCTION_SELECTION (prepending {@code old = ...},
     * wrapping in try/catch, appending the postcondition assert) before the
     * checker runs.
     */
    static final String ORIGINAL_BODY_KEY = 'verification.originalBody'

    /**
     * Node-metadata key under which a {@link LoopSpec} is stashed on an annotated
     * loop statement. Captured at CONVERSION before groovy-contracts' loop
     * transforms inject invariant asserts into the live loop body.
     */
    static final String LOOP_SPEC_KEY = 'verification.loopSpec'

    @Override
    void visit(ASTNode[] nodes, SourceUnit source) {
        ModuleNode module = source.AST
        if (module == null) return
        for (ClassNode cn : module.classes) {
            augmentClass(cn, module, source)
            for (MethodNode mn : cn.methods) {
                augment(mn, module, source)
            }
            // Phase 15b — constructors get the same contract-text capture + clean-body snapshot as
            // methods. ConstructorNode extends MethodNode so the same augment() runs over both;
            // the constructor's verification path (no entry-assume of class invariants, prove
            // them at exit) lives in VerifyChecker.
            for (ConstructorNode cn2 : cn.declaredConstructors) {
                augment(cn2, module, source)
            }
        }
    }

    /**
     * Capture any class-level {@code groovy.contracts.@Invariant} closures into a
     * {@link ClassInvariantSource} on the class (Phase 15a). Each invariant's
     * verbatim text is harvested the same way as a method's pre/postcondition;
     * the conjunction of all captured texts is the class invariant.
     *
     * groovy-contracts' {@code @Invariant} is {@code @Repeatable}, so the parser
     * may produce either a sequence of {@code @Invariant} annotations or a single
     * {@code @Invariants} container holding them. Both shapes are handled.
     */
    private static void augmentClass(ClassNode cn, ModuleNode module, SourceUnit source) {
        List<String> texts = new ArrayList<String>()
        for (AnnotationNode an : cn.annotations) {
            if (isClassInvariantAnnotation(an, module)) {
                String text = captureInvariantText(an, source)
                if (text) texts.add(text)
            } else if (isClassInvariantsContainer(an, module)) {
                Expression value = an.getMember('value')
                if (value instanceof ListExpression) {
                    for (Expression child : ((ListExpression) value).expressions) {
                        if (child instanceof AnnotationConstantExpression) {
                            Object inner = ((AnnotationConstantExpression) child).value
                            if (inner instanceof AnnotationNode) {
                                String text = captureInvariantText((AnnotationNode) inner, source)
                                if (text) texts.add(text)
                            }
                        }
                    }
                }
            }
        }
        if (texts.isEmpty()) return
        AnnotationNode holder = new AnnotationNode(ClassHelper.make(ClassInvariantSource))
        ListExpression list = new ListExpression()
        for (String t : texts) list.addExpression(new ConstantExpression(t))
        holder.addMember('invariants', list)
        cn.addAnnotation(holder)
    }

    /** Verbatim text of an {@code @Invariant}'s closure, or null if absent/unparseable. */
    private static String captureInvariantText(AnnotationNode an, SourceUnit source) {
        Expression value = an.getMember('value')
        if (!(value instanceof ClosureExpression)) return null
        captureSource((ClosureExpression) value, source)
    }

    /**
     * True if {@code an} is {@code groovy.contracts.@Invariant}. The same annotation
     * class is used for loop invariants (via {@code @ExtendedTarget(LOOP)}); the
     * caller restricts to the class-annotations list, so a loop-position usage is
     * never seen here.
     */
    private static boolean isClassInvariantAnnotation(AnnotationNode an, ModuleNode module) {
        String name = an.classNode?.name
        if (name == null) return false
        if (name == CONTRACTS_PKG + 'Invariant') return true
        if (name == 'Invariant' && importedFromContracts('Invariant', module)) return true
        false
    }

    /** True if {@code an} is the {@code groovy.contracts.@Invariants} repeatable container. */
    private static boolean isClassInvariantsContainer(AnnotationNode an, ModuleNode module) {
        String name = an.classNode?.name
        if (name == null) return false
        if (name == CONTRACTS_PKG + 'Invariants') return true
        if (name == 'Invariants' && importedFromContracts('Invariants', module)) return true
        false
    }

    private static void augment(MethodNode mn, ModuleNode module, SourceUnit source) {
        String requires = null
        String ensures = null
        String decreases = null
        String modifies = null
        for (AnnotationNode an : mn.annotations) {
            String kind = contractKind(an, module)
            if (kind == null) continue
            Expression value = an.getMember('value')
            if (!(value instanceof ClosureExpression)) continue
            String text = captureSource((ClosureExpression) value, source)
            if (!text) continue
            if (kind == 'requires') requires = text
            else if (kind == 'ensures') ensures = text
            else if (kind == 'modifies') modifies = text
            else decreases = text   // method-level @Decreases (recursion termination measure)
        }
        if (requires != null || ensures != null || decreases != null || modifies != null) {
            AnnotationNode holder = new AnnotationNode(ClassHelper.make(ContractSource))
            if (requires != null) holder.addMember('requires', new ConstantExpression(requires))
            if (ensures != null) holder.addMember('ensures', new ConstantExpression(ensures))
            if (decreases != null) holder.addMember('decreases', new ConstantExpression(decreases))
            if (modifies != null) holder.addMember('modifies', new ConstantExpression(modifies))
            mn.addAnnotation(holder)
        }

        boolean loopsFound = captureLoops(mn, source)

        // Snapshot the clean body before groovy-contracts instruments it, so the
        // body analysis (postcondition paths, loop regions, AND the implicit
        // array-bounds/division/null-deref checks) sees the author's code, not
        // the injected old-map/try-catch/assert. A shallow copy of the statement
        // list suffices: groovy-contracts mutates the original block's list (and a
        // loop's inner block), not the statement nodes we keep references to — and
        // loop bodies are copied separately into the LoopSpec. Taken for EVERY
        // method (not just @Ensures/loop ones), because the implicit safety checks
        // run on every method in the @TypeChecked scope, including ones whose only
        // contract is a @Requires (which groovy-contracts also instruments).
        if (mn.code instanceof BlockStatement) {
            BlockStatement orig = (BlockStatement) mn.code
            BlockStatement snapshot = new BlockStatement(
                new ArrayList<Statement>(orig.statements),
                orig.variableScope ?: new VariableScope())
            snapshot.setSourcePosition(orig)
            mn.setNodeMetaData(ORIGINAL_BODY_KEY, snapshot)
        }
    }

    /**
     * Capture {@code @Invariant}/{@code @Decreases} on top-level loop statements
     * into a {@link LoopSpec} stashed on the loop node, before groovy-contracts'
     * loop transforms rewrite the loop body. Returns true if any was captured.
     */
    private static boolean captureLoops(MethodNode mn, SourceUnit source) {
        if (!(mn.code instanceof BlockStatement)) return false
        boolean found = false
        for (Statement st : ((BlockStatement) mn.code).statements) {
            if (st instanceof LoopingStatement) {
                LoopSpec spec = buildLoopSpec((LoopingStatement) st, source)
                if (spec != null) {
                    st.setNodeMetaData(LOOP_SPEC_KEY, spec)
                    found = true
                }
            }
        }
        return found
    }

    private static LoopSpec buildLoopSpec(LoopingStatement loop, SourceUnit source) {
        // Phase 59 — a classic for-loop is desugared to while-shape: its condition is
        // the guard, its init becomes a prefix statement, and its update is normalised
        // to a plain assignment and appended to the loop body. A for-in loop (no
        // ClosureListExpression) or any non-standard for shape returns null → loud skip.
        List<Statement> initStmts = null
        Statement updateStmt = null
        Expression guard
        if (loop instanceof ForStatement) {
            ForStatement f = (ForStatement) loop
            if (!(f.collectionExpression instanceof ClosureListExpression)) return null
            List<Expression> parts = ((ClosureListExpression) f.collectionExpression).expressions
            if (parts.size() != 3 || parts.get(1) instanceof EmptyExpression) return null
            guard = parts.get(1)
            Expression initE = parts.get(0)
            Expression updE = parts.get(2)
            if (!(initE instanceof EmptyExpression)) {
                initStmts = [(Statement) new ExpressionStatement(initE)]
            }
            if (!(updE instanceof EmptyExpression)) {
                updateStmt = normalizeUpdate(updE)
                if (updateStmt == null) return null   // unsupported update shape → loud skip
            }
        } else {
            guard = loopGuard(loop)
        }
        if (guard == null) return null   // only while/do-while/for guards are modelled
        List<Expression> invariants = new ArrayList<Expression>()
        Expression variant = null
        for (AnnotationNode an : ((Statement) loop).getStatementAnnotations()) {
            String simple = simpleName(an.classNode?.name)
            if (simple != 'Invariant' && simple != 'Decreases') continue
            Expression value = an.getMember('value')
            if (!(value instanceof ClosureExpression)) continue
            // Re-parse from the verbatim source so the captured expression is a
            // clean CONVERSION AST, immune to the resolution/rewrites later phases
            // apply to the live node — the same reason @Requires/@Ensures are
            // captured as text. Without this, a `Forall.range(...)` / `a[i]` in the
            // invariant reaches the verifier already resolved (static call / getAt),
            // outside the encoder's fragment. Fall back to the live AST if re-parse
            // fails (e.g. a multi-statement invariant closure).
            Expression reparsed = reparse(captureSource((ClosureExpression) value, source))
            List<Expression> exprs = reparsed != null ? [reparsed] :
                                     closureBoolExprs((ClosureExpression) value)
            if (simple == 'Invariant') invariants.addAll(exprs)
            else if (!exprs.isEmpty()) variant = exprs.get(0)
            // Capture only — leave the closure intact. groovy-contracts generates
            // the runtime invariant/variant checks from it; we add the compile-time
            // Z3 proof on top.
        }
        if (invariants.isEmpty()) return null
        LoopSpec spec = new LoopSpec()
        spec.invariants = invariants
        spec.variant = variant
        spec.guard = guard
        spec.body = loopBodyCopy(loop)
        if (updateStmt != null) spec.body.add(updateStmt)   // for-loop: body; update
        spec.init = initStmts
        return spec
    }

    private static Expression loopGuard(LoopingStatement loop) {
        if (loop instanceof WhileStatement) return ((WhileStatement) loop).booleanExpression
        if (loop instanceof DoWhileStatement) return ((DoWhileStatement) loop).booleanExpression
        return null
    }

    /**
     * Phase 59 — normalise a for-loop update expression to a plain assignment statement so
     * the loop machinery sees the same shape it already handles for while loops:
     * {@code i++}/{@code ++i} → {@code i = i + 1}, {@code i--}/{@code --i} → {@code i = i - 1},
     * {@code i += k} → {@code i = i + (k)}, {@code i -= k} → {@code i = i - (k)}, and a plain
     * {@code i = ...} is kept as-is. Anything else (a non-variable target, an unusual operator)
     * returns null so the whole loop is honestly skipped rather than mis-modelled.
     */
    private static Statement normalizeUpdate(Expression upd) {
        String name
        int op
        Expression operand
        if (upd instanceof PostfixExpression) {
            operand = ((PostfixExpression) upd).expression; op = ((PostfixExpression) upd).operation.type
        } else if (upd instanceof PrefixExpression) {
            operand = ((PrefixExpression) upd).expression; op = ((PrefixExpression) upd).operation.type
        } else if (upd instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) upd
            if (!(be.leftExpression instanceof VariableExpression)) return null
            if (be.operation.type == Types.ASSIGN) return new ExpressionStatement(upd)
            name = ((VariableExpression) be.leftExpression).name
            String rhs = be.rightExpression.text
            if (be.operation.type == Types.PLUS_EQUAL) return assignStmt("${name} = ${name} + (${rhs})")
            if (be.operation.type == Types.MINUS_EQUAL) return assignStmt("${name} = ${name} - (${rhs})")
            return null
        } else {
            return null
        }
        if (!(operand instanceof VariableExpression)) return null
        name = ((VariableExpression) operand).name
        if (op == Types.PLUS_PLUS) return assignStmt("${name} = ${name} + 1")
        if (op == Types.MINUS_MINUS) return assignStmt("${name} = ${name} - 1")
        return null
    }

    private static Statement assignStmt(String text) {
        Expression e = reparse(text)
        return e != null ? new ExpressionStatement(e) : null
    }

    private static List<Statement> loopBodyCopy(LoopingStatement loop) {
        Statement b = loop.loopBlock
        if (b instanceof BlockStatement) {
            return new ArrayList<Statement>(((BlockStatement) b).statements)
        }
        return b != null ? ([b] as List<Statement>) : Collections.<Statement> emptyList()
    }

    /** Re-parse a captured contract expression's text into a fresh CONVERSION AST. */
    private static Expression reparse(String text) {
        if (text == null) return null
        try {
            List<ASTNode> nodes = new AstBuilder().buildFromString(CompilePhase.CONVERSION, true, text)
            if (nodes.isEmpty()) return null
            ASTNode top = nodes.get(0)
            if (top instanceof BlockStatement) {
                BlockStatement bs = (BlockStatement) top
                if (bs.statements.size() == 1 && bs.statements.get(0) instanceof ExpressionStatement) {
                    return ((ExpressionStatement) bs.statements.get(0)).expression
                }
            }
            return null
        } catch (Throwable t) {
            return null
        }
    }

    private static List<Expression> closureBoolExprs(ClosureExpression closure) {
        List<Expression> out = new ArrayList<Expression>()
        Statement code = closure.code
        if (code instanceof BlockStatement) {
            for (Statement st : ((BlockStatement) code).statements) {
                if (st instanceof ExpressionStatement) out.add(((ExpressionStatement) st).expression)
            }
        }
        return out
    }

    private static String simpleName(String name) {
        if (name == null) return null
        int dot = name.lastIndexOf('.')
        return dot >= 0 ? name.substring(dot + 1) : name
    }

    /**
     * Returns "requires"/"ensures" if the annotation is a groovy-contracts
     * pre/postcondition, else null. At CONVERSION annotation types are usually
     * unresolved (short name as written), so resolve the simple name against the
     * module's imports rather than trusting a bare name match.
     */
    private static String contractKind(AnnotationNode an, ModuleNode module) {
        String name = an.classNode?.name
        if (name == null) return null
        if (name == CONTRACTS_PKG + 'Requires') return 'requires'
        if (name == CONTRACTS_PKG + 'Ensures') return 'ensures'
        if (name == CONTRACTS_PKG + 'Decreases') return 'decreases'
        if (name == CONTRACTS_PKG + 'Modifies') return 'modifies'
        if ((name == 'Requires' || name == 'Ensures' || name == 'Decreases' || name == 'Modifies') &&
            importedFromContracts(name, module)) {
            switch (name) {
                case 'Requires': return 'requires'
                case 'Ensures':  return 'ensures'
                case 'Modifies': return 'modifies'
                default:         return 'decreases'
            }
        }
        return null
    }

    private static boolean importedFromContracts(String simpleName, ModuleNode module) {
        for (ImportNode imp : module.imports) {
            if (imp.alias == simpleName && imp.className == CONTRACTS_PKG + simpleName) return true
        }
        for (ImportNode imp : module.starImports) {
            if (imp.packageName == CONTRACTS_PKG) return true
        }
        return false
    }

    private static String captureSource(ClosureExpression closure, SourceUnit source) {
        Statement code = closure.code
        Expression expr = null
        if (code instanceof BlockStatement) {
            List<Statement> stmts = ((BlockStatement) code).statements
            if (stmts && stmts[0] instanceof ExpressionStatement) {
                expr = ((ExpressionStatement) stmts[0]).expression
            }
        }
        if (expr == null) return null

        // Reuse power-assert's verbatim slicing by wrapping the boolean in a
        // synthetic AssertStatement that carries the original source position.
        BooleanExpression be = new BooleanExpression(expr)
        be.setSourcePosition(expr)
        AssertStatement assertStmt = new AssertStatement(be)
        assertStmt.setSourcePosition(expr)

        Janitor janitor = new Janitor()
        try {
            return new SourceText(assertStmt, source, janitor).normalizedText
        } catch (Throwable ignored) {
            return expr.text   // fall back to AST reconstruction
        } finally {
            janitor.cleanup()
        }
    }
}
