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
import org.codehaus.groovy.ast.Parameter
import org.codehaus.groovy.ast.stmt.AssertStatement
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.DoWhileStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.ForStatement
import org.codehaus.groovy.ast.stmt.IfStatement
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

    /**
     * Phase 63 — name of the synthetic index a {@code for (x in xs)} desugar introduces. Hidden from
     * counterexamples (filtered by {@code VerifyChecker.shown}); distinctive enough not to collide
     * with a real local.
     */
    static final String FOR_IN_INDEX = '__gvForInIdx'

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
        // {@code @Requires}/{@code @Ensures} are {@code @Repeatable}: groovy-contracts enforces *each*
        // at runtime, so multiple of them mean the *conjunction* of their conditions. Collect them all
        // (whether the parser left a sequence of annotations or collapsed them into a
        // {@code @RequiresConditions}/{@code @EnsuresConditions} container) and AND the captured texts —
        // a single annotation passes through unchanged. (Previously only the last was kept.)
        List<String> requiresTexts = new ArrayList<String>()
        List<String> ensuresTexts = new ArrayList<String>()
        List<String> modifiesTexts = new ArrayList<String>()
        String decreases = null
        for (AnnotationNode an : mn.annotations) {
            String kind = contractKind(an, module)
            if (kind == null) continue
            if (kind == 'requires') addClosureText(an, source, requiresTexts)
            else if (kind == 'ensures') addClosureText(an, source, ensuresTexts)
            else if (kind == 'modifies') addClosureText(an, source, modifiesTexts)
            else if (kind == 'requiresContainer') addContainerTexts(an, source, requiresTexts)
            else if (kind == 'ensuresContainer') addContainerTexts(an, source, ensuresTexts)
            else if (kind == 'modifiesContainer') addContainerTexts(an, source, modifiesTexts)
            else { String t = closureText(an, source); if (t) decreases = t }  // method-level @Decreases
        }
        String requires = conjoinTexts(requiresTexts)
        String ensures = conjoinTexts(ensuresTexts)
        String modifies = combineModifies(modifiesTexts)
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
        return captureLoopsIn(((BlockStatement) mn.code).statements, source)
    }

    /** Phase 91 — capture loop specs recursively, so a *nested* loop's @Invariant/@Decreases is stashed
     *  on the inner loop node too (the verifier reads it when summarising the inner loop). Since the outer
     *  body is copied shallowly ({@link #loopBodyCopy}), the inner node is shared and the metadata is seen. */
    private static boolean captureLoopsIn(List<Statement> stmts, SourceUnit source) {
        boolean found = false
        if (stmts != null) for (Statement st : stmts) found |= captureLoopsStmt(st, source)
        found
    }

    private static boolean captureLoopsStmt(Statement st, SourceUnit source) {
        if (st == null) return false
        boolean found = false
        if (st instanceof LoopingStatement) {
            LoopSpec spec = buildLoopSpec((LoopingStatement) st, source)
            if (spec != null) { st.setNodeMetaData(LOOP_SPEC_KEY, spec); found = true }
            found |= captureLoopsStmt(((LoopingStatement) st).loopBlock, source)
        } else if (st instanceof BlockStatement) {
            found = captureLoopsIn(((BlockStatement) st).statements, source)
        } else if (st instanceof IfStatement) {
            found |= captureLoopsStmt(((IfStatement) st).ifBlock, source)
            found |= captureLoopsStmt(((IfStatement) st).elseBlock, source)
        }
        found
    }

    private static LoopSpec buildLoopSpec(LoopingStatement loop, SourceUnit source) {
        // Phase 59 — a classic for-loop is desugared to while-shape: its condition is the guard, its
        // init becomes a prefix statement, and its update is normalised to a plain assignment and
        // appended to the loop body. Phase 63 — a for-in loop `for (x in xs)` desugars to an *indexed*
        // while over xs's elements: a hidden synthetic index drives the guard/update, the loop variable
        // keeps its source name (bound to `xs[idx]` at the top of each iteration) so contracts and
        // counterexamples read in terms of `x`, and an index-bounds invariant + a `size - idx` variant
        // are auto-injected (the index isn't user-nameable). Other for shapes return null → loud skip.
        List<Statement> initStmts = null
        Statement updateStmt = null
        List<Statement> bodyPrefix = null
        Expression autoInvariant = null
        Expression autoVariant = null
        String forInVarName = null
        Statement forInBindStmt = null
        Expression guard
        if (loop instanceof ForStatement) {
            ForStatement f = (ForStatement) loop
            if (f.collectionExpression instanceof ClosureListExpression) {
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
            } else if (f.collectionExpression instanceof VariableExpression) {
                // for-in over a named collection. The element type is left to the encoder (Int list/
                // array is the modelled case); a non-Int element simply doesn't translate and skips.
                String xs = ((VariableExpression) f.collectionExpression).name
                String x = f.variable?.name
                if (x == null) return null
                String idx = FOR_IN_INDEX
                guard       = reparse("${idx} < ${xs}.size()")
                Statement initS = assignStmt("int ${idx} = 0")
                Statement bindX = assignStmt("${x} = ${xs}[${idx}]")
                updateStmt  = assignStmt("${idx} = ${idx} + 1")
                autoInvariant = reparse("0 <= ${idx} && ${idx} <= ${xs}.size()")
                autoVariant   = reparse("${xs}.size() - ${idx}")
                if (guard == null || initS == null || bindX == null || updateStmt == null
                        || autoInvariant == null || autoVariant == null) return null
                initStmts  = [initS]
                bodyPrefix = [bindX]
                forInVarName = x
                forInBindStmt = bindX
            } else {
                return null   // for-in over a literal / method-call collection → loud skip
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
        if (invariants.isEmpty()) return null   // a loop needs a user @Invariant to be verified
        // Phase 63 — the for-in index-bounds invariant is added *after* the user's (so its synthetic
        // name trails the user-facing clauses in any diagnostic), and `size - idx` is the variant
        // unless the user supplied a @Decreases (they have no index to write a better one).
        if (autoInvariant != null) invariants.add(autoInvariant)
        LoopSpec spec = new LoopSpec()
        spec.invariants = invariants
        spec.variant = (variant != null) ? variant : autoVariant
        spec.guard = guard
        List<Statement> body = new ArrayList<Statement>()
        if (bodyPrefix != null) body.addAll(bodyPrefix)             // for-in: x = xs[idx]; …
        body.addAll(loopBodyCopy(loop))
        if (updateStmt != null) body.add(updateStmt)                // for/for-in: …; update
        spec.body = body
        spec.init = initStmts
        spec.forInVar = forInVarName
        spec.forInBind = forInBindStmt
        spec.isDoWhile = loop instanceof DoWhileStatement   // Phase 88 — body runs once before the first guard
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
        // Repeatable-annotation containers (synthetic, never user-written, so matched by simple name too).
        if (name == 'RequiresConditions' || name == CONTRACTS_PKG + 'RequiresConditions') return 'requiresContainer'
        if (name == 'EnsuresConditions'  || name == CONTRACTS_PKG + 'EnsuresConditions')  return 'ensuresContainer'
        if (name == 'ModifiesConditions' || name == CONTRACTS_PKG + 'ModifiesConditions') return 'modifiesContainer'
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

    /** Capture one annotation's closure-condition text into {@code out} (if it has one). */
    private static void addClosureText(AnnotationNode an, SourceUnit source, List<String> out) {
        String t = closureText(an, source)
        if (t) out.add(t)
    }

    /** The verbatim source of an annotation's {@code value} closure condition, or null. */
    private static String closureText(AnnotationNode an, SourceUnit source) {
        Expression value = an.getMember('value')
        if (!(value instanceof ClosureExpression)) return null
        captureSource((ClosureExpression) value, source)
    }

    /** Capture every inner condition of a repeatable container ({@code @RequiresConditions} etc.). */
    private static void addContainerTexts(AnnotationNode an, SourceUnit source, List<String> out) {
        Expression value = an.getMember('value')
        if (!(value instanceof ListExpression)) return
        for (Expression child : ((ListExpression) value).expressions) {
            if (child instanceof AnnotationConstantExpression) {
                Object inner = ((AnnotationConstantExpression) child).value
                if (inner instanceof AnnotationNode) addClosureText((AnnotationNode) inner, source, out)
            }
        }
    }

    /**
     * Merge repeated {@code @Modifies} frames into one list of locations. Unlike a predicate, a frame
     * is a *union* of locations, so the texts are wrapped in a single {@code [ … ]} (the consumer's
     * {@code addModifiedLocation} recursively flattens, so an already-list frame nests harmlessly). A
     * lone {@code @Modifies} passes through unchanged.
     */
    private static String combineModifies(List<String> texts) {
        if (texts.isEmpty()) return null
        if (texts.size() == 1) return texts.get(0)
        StringBuilder sb = new StringBuilder('[')
        for (int i = 0; i < texts.size(); i++) {
            if (i > 0) sb.append(', ')
            sb.append(texts.get(i))
        }
        sb.append(']').toString()
    }

    /** AND a list of condition texts into one (each parenthesised); a single text passes through. */
    private static String conjoinTexts(List<String> texts) {
        if (texts.isEmpty()) return null
        if (texts.size() == 1) return texts.get(0)
        StringBuilder sb = new StringBuilder()
        for (int i = 0; i < texts.size(); i++) {
            if (i > 0) sb.append(' && ')
            sb.append('(').append(texts.get(i)).append(')')
        }
        sb.toString()
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
