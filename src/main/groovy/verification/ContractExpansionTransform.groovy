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
import org.codehaus.groovy.ast.AnnotationNode
import org.codehaus.groovy.ast.ClassHelper
import org.codehaus.groovy.ast.ClassNode
import org.codehaus.groovy.ast.ImportNode
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.ModuleNode
import org.codehaus.groovy.ast.VariableScope
import org.codehaus.groovy.ast.expr.BooleanExpression
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.stmt.AssertStatement
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.DoWhileStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.LoopingStatement
import org.codehaus.groovy.ast.stmt.Statement
import org.codehaus.groovy.ast.stmt.WhileStatement
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
            for (MethodNode mn : cn.methods) {
                augment(mn, module, source)
            }
        }
    }

    private static void augment(MethodNode mn, ModuleNode module, SourceUnit source) {
        String requires = null
        String ensures = null
        for (AnnotationNode an : mn.annotations) {
            String kind = contractKind(an, module)
            if (kind == null) continue
            Expression value = an.getMember('value')
            if (!(value instanceof ClosureExpression)) continue
            String text = captureSource((ClosureExpression) value, source)
            if (!text) continue
            if (kind == 'requires') requires = text
            else ensures = text
        }
        if (requires != null || ensures != null) {
            AnnotationNode holder = new AnnotationNode(ClassHelper.make(ContractSource))
            if (requires != null) holder.addMember('requires', new ConstantExpression(requires))
            if (ensures != null) holder.addMember('ensures', new ConstantExpression(ensures))
            mn.addAnnotation(holder)
        }

        boolean loopsFound = captureLoops(mn)

        // Snapshot the clean body before groovy-contracts instruments it, so the
        // body analysis (postcondition paths, loop regions) sees the author's
        // code, not the injected old-map/try-catch/assert. A shallow copy of the
        // statement list suffices: groovy-contracts mutates the original block's
        // list (and a loop's inner block), not the statement nodes we keep
        // references to — and loop bodies are copied separately into the LoopSpec.
        if ((ensures != null || loopsFound) && mn.code instanceof BlockStatement) {
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
    private static boolean captureLoops(MethodNode mn) {
        if (!(mn.code instanceof BlockStatement)) return false
        boolean found = false
        for (Statement st : ((BlockStatement) mn.code).statements) {
            if (st instanceof LoopingStatement) {
                LoopSpec spec = buildLoopSpec((LoopingStatement) st)
                if (spec != null) {
                    st.setNodeMetaData(LOOP_SPEC_KEY, spec)
                    found = true
                }
            }
        }
        return found
    }

    private static LoopSpec buildLoopSpec(LoopingStatement loop) {
        Expression guard = loopGuard(loop)
        if (guard == null) return null   // only while/do-while guards are modelled
        List<Expression> invariants = new ArrayList<Expression>()
        Expression variant = null
        for (AnnotationNode an : ((Statement) loop).getStatementAnnotations()) {
            String simple = simpleName(an.classNode?.name)
            if (simple != 'Invariant' && simple != 'Decreases') continue
            Expression value = an.getMember('value')
            if (!(value instanceof ClosureExpression)) continue
            List<Expression> exprs = closureBoolExprs((ClosureExpression) value)
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
        return spec
    }

    private static Expression loopGuard(LoopingStatement loop) {
        if (loop instanceof WhileStatement) return ((WhileStatement) loop).booleanExpression
        if (loop instanceof DoWhileStatement) return ((DoWhileStatement) loop).booleanExpression
        return null
    }

    private static List<Statement> loopBodyCopy(LoopingStatement loop) {
        Statement b = loop.loopBlock
        if (b instanceof BlockStatement) {
            return new ArrayList<Statement>(((BlockStatement) b).statements)
        }
        return b != null ? ([b] as List<Statement>) : Collections.<Statement> emptyList()
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
        if ((name == 'Requires' || name == 'Ensures') && importedFromContracts(name, module)) {
            return name == 'Requires' ? 'requires' : 'ensures'
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
