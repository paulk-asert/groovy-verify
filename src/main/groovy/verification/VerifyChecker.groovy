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
import org.codehaus.groovy.ast.AnnotationNode
import org.codehaus.groovy.ast.ASTNode
import org.codehaus.groovy.ast.ConstructorNode
import org.codehaus.groovy.ast.ClassCodeVisitorSupport
import org.codehaus.groovy.ast.ClassHelper
import org.codehaus.groovy.ast.GenericsType
import org.codehaus.groovy.ast.ClassNode
import org.codehaus.groovy.transform.stc.StaticTypesMarker
import org.codehaus.groovy.ast.FieldNode
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.Parameter
import org.codehaus.groovy.ast.CodeVisitorSupport
import org.codehaus.groovy.ast.Variable
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
import org.codehaus.groovy.control.CompilePhase
import org.codehaus.groovy.control.SourceUnit
import org.codehaus.groovy.syntax.Token
import org.codehaus.groovy.syntax.Types
import org.codehaus.groovy.transform.stc.StaticTypeCheckingVisitor
import org.codehaus.groovy.transform.stc.TypeCheckingExtension

/**
 * SMT-backed precondition verifier — the spike entry point.
 *
 * Usage from consumer code:
 *   {@code @TypeChecked(extensions = 'verification.VerifyChecker')}
 *
 * Contracts are authored as stock {@code groovy.contracts.@Requires}/
 * {@code @Ensures}; {@link ContractExpansionTransform} captures each closure's
 * verbatim source into a {@code @ContractSource} that this checker reads back
 * (it survives into bytecode, so a callee compiled in another module still
 * carries its contract).
 *
 * What this does on every method call inside the annotated scope:
 *   1. Look up the called method's {@code @Requires} precondition and read
 *      its captured text from {@code @ContractSource}.
 *   2. Bind the contract's formal parameters to the actual-argument
 *      expressions at this call site.
 *   3. Harvest the path condition from enclosing {@code if}
 *      statements (precomputed by {@link PathFacts}).
 *   4. Ask Z3 whether {@code path ∧ ¬precond} is satisfiable.
 *        - UNSAT  → verified, no diagnostic.
 *        - SAT    → refuted, emit error with counterexample.
 *        - UNKNOWN → emit warning ("could not decide").
 *
 * Beyond explicit contracts, every method body in scope is also checked for the
 * implicit preconditions every program carries — array index in bounds, divisor
 * non-zero, dereferenced receiver non-null ({@link #verifyImplicitObligations}) —
 * discharged with the same assume-facts / refute-negation machinery.
 *
 * Anything outside the supported fragment becomes a "skipped"
 * warning rather than a silent pass — borrowed from OpenJML's ESC
 * mode discipline.
 */
@CompileStatic
class VerifyChecker extends TypeCheckingExtension implements CheckerApi {

    // ─── CheckerApi — the curated surface pack checker-passes (EncodingPack.checkMethod) run against ───

    /** {@link CheckerApi#reportError} — the pack pass's diagnostic channel. */
    @Override
    void reportError(String message, org.codehaus.groovy.ast.ASTNode at) { addStaticTypeError(message, at) }

    /** {@link CheckerApi#cleanBody} — the CONVERSION snapshot when present, else the live code. */
    @Override
    Statement cleanBody(MethodNode node) {
        Statement body = (Statement) node.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        body != null ? body : node.code
    }

    /** {@link CheckerApi#inferredTypeOf} — STC's inferred (or declared) type for an expression. */
    @Override
    ClassNode inferredTypeOf(Expression e) { getType(e) }

    private static final ClassNode REQUIRES_TYPE = ClassHelper.make(Requires)
    private static final ClassNode ENSURES_TYPE = ClassHelper.make(Ensures)
    // This project's String-valued twins (the Java-friendly form). Their condition text is captured into the
    // same @ContractSource as a closure's, so only the find* presence-gates need to recognise them too.
    private static final ClassNode VERIFY_REQUIRES_TYPE = ClassHelper.make(verification.Requires)
    private static final ClassNode VERIFY_ENSURES_TYPE = ClassHelper.make(verification.Ensures)
    private static final ClassNode LABEL_TYPE = ClassHelper.make(Label)   // Phase L1 — security classification
    private static final ClassNode RELY_TYPE = ClassHelper.make(Rely)         // Phase L1 — rely/guarantee well-formedness
    private static final ClassNode GUARANTEE_TYPE = ClassHelper.make(Guarantee)
    private static final String RG_LAW_KEY = 'verification.relyGuaranteeLaw'
    private static final ClassNode CONTRACT_SOURCE_TYPE = ClassHelper.make(ContractSource)
    private static final ClassNode CLASS_INVARIANT_SOURCE_TYPE = ClassHelper.make(ClassInvariantSource)
    /** Phase 130 — metadata on a synthesized @Reducer/@Associative law lemma: {@code [combinerName, lawName]}. */
    private static final String REDUCER_LAW_KEY = 'verification.reducerLaw'
    /** Phase 136 — metadata on a synthesized @Monadic law lemma: {@code [carrierName, lawName]}. */
    private static final String MONADIC_LAW_KEY = 'verification.monadicLaw'

    private SmtBackend backend
    private PathFacts currentFacts
    /** The method currently being type-checked; its own @Requires is a given at any call site in its body. */
    private MethodNode currentMethod
    /** Closed pure-function evaluator over the current class (Phase 8a); null when no class context. */
    private PureEvaluator currentEvaluator
    /**
     * Per-method map from a size-oracle receiver name to the accessor the developer actually wrote
     * for it ({@code .length} / {@code .size()}), harvested from the method's contracts and body
     * (Phase 9 diagnostics). The encoder keeps its internal {@code recv.size} symbol; this is purely
     * how it is *displayed*. Receivers with no written size accessor (e.g. a plain {@code a[i]}) fall
     * back to {@code .size()} — Groovy's universal size idiom, valid for arrays too.
     */
    private Map<String, String> sizeAccessors = [:]
    /** Mints unique names for havoced locations at call sites (Phase 13 caller-side framing). */
    private int havocCounter = 0
    /**
     * Phase 15a — the class-level {@code @Invariant} clauses on the current method's declaring
     * class, pre-filtered to the encoder fragment. Empty for static methods. Assumed at method
     * entry across postcondition, implicit-obligation, and loop-obligation discharge sites; also
     * conjoined into the exit goal in {@link #checkPath}. Populated once in {@link #beforeVisitMethod}
     * to avoid emitting a "skipped" diagnostic per discharge path for the same outside-fragment clause.
     */
    private List<Expression> currentClassInvariants = Collections.<Expression> emptyList()
    /**
     * Phase 15b — true while {@link #afterVisitMethod} is processing a constructor. The class
     * invariant is *not* assumed at constructor entry (the invariant hasn't been established yet —
     * it's the goal, not a precondition), but it IS conjoined into the exit obligation just as for
     * an instance method. Set in {@link #beforeVisitMethod}, cleared in the afterVisitMethod finally.
     */
    private boolean currentIsConstructor = false
    /**
     * Phase 44 — true if the current method (or its declaring class) carries {@code @CheckOverflow}.
     * When set, the {@code ObligationCollector} emits an {@link OverflowSite} for each binary
     * {@code +}/{@code -}/{@code *} on an Int-sorted operand, and the dispatch chain discharges
     * the resulting obligation alongside the existing bounds/null/divide-by-zero checks.
     */
    private boolean currentOverflowChecking = false
    /**
     * Phase 8b (step 3) — true once the value-flow pass has discharged every {@code assert} in the body (proven
     * or loudly refuted). Only then is it sound for the postcondition replay to *assume* a user assertion
     * downstream (so an {@code @Ensures} can use it): assume/enforce, the assert being enforced by that pass. If
     * the value-flow pass bailed (loop / re-assignment), the asserts weren't all discharged, so the postcondition
     * treats them as pass-through (checked without them) rather than assuming an undischarged fact.
     */
    private boolean currentAssertsTrusted = false
    /**
     * Phase 45 — class-typed parameter names visible to the current method (each value is the
     * parameter's declared {@link ClassNode}). Used by the cross-class reasoning machinery: a
     * read {@code b.field} translates to a receiver-qualified entity {@code b$field}; the
     * receiver's class invariants are assumed at method entry and re-assumed after a
     * {@code b.method()} call. Only non-primitive, non-collection types end up here — sets, maps,
     * lists, and the primitive wrappers have their own dispatch (collectSetElementTypes etc.).
     */
    private Map<String, ClassNode> currentObjectParams = new LinkedHashMap<String, ClassNode>()
    private Map<String, ClassNode> currentTupleParams = new LinkedHashMap<String, ClassNode>()

    /**
     * Source-level names of {@code java.util.Set}-typed parameters and fields visible to the current
     * method — the type hint the otherwise shape-based encoder needs to tell a set from a list
     * (membership/size/{@code contains} share syntax). Recomputed per method in {@link #beforeVisitMethod}.
     */
    private Map<String, ClassNode> currentSetElementTypes = new HashMap<String, ClassNode>()
    /** Names of {@code java.util.Map}-typed params/fields visible to the current method (see {@link #currentSetElementTypes}). */
    private Map<String, ClassNode[]> currentMapTypes = new HashMap<String, ClassNode[]>()
    /**
     * Phase 36 — for each {@code Map<K, Set<V>>} param/field visible to the current method, the inner
     * {@code Set}'s element type {@code V}. The value sort of such a map becomes the characteristic-array
     * sort {@code Array<V, Int>}, so {@code m[k]} reads as a transient set handle the encoder can lower
     * {@code .contains}/{@code .containsAll} through.
     */
    private Map<String, ClassNode> currentNestedSetValueTypes = new HashMap<String, ClassNode>()
    /**
     * Phase 37 — names of {@code List<X>} / {@code X[]} containers whose element generic (or array
     * component) carries a {@code @NonNull}-like annotation (the {@code NullChecker}-style simple
     * names — see {@link #NON_NULL_ANNOTATION_NAMES}). The implicit per-element NPE obligation on
     * {@code xs[i].method()} is skipped for these.
     */
    private Set<String> currentNonNullElementContainers = new HashSet<String>()
    /**
     * Phase 41 — names of every {@code java.util.List}-typed param/field, regardless of element type.
     * Distinct from {@link #currentListElementTypes} (which only tracks non-Int element lists).
     * The encoder routes {@code xs.count(v)} for any of these through {@code bcount(arr, v, 0, sizeOf)}
     * so the count tracks the bounded {@code [0, size)} range faithfully across size-changing
     * mutations. Arrays ({@code int[]}) keep using the unbounded {@code count}.
     */
    private Set<String> currentListNames = new HashSet<String>()
    /** Names of {@code java.util.List}-typed params/fields with non-Int element types (Phase 27). */
    private Map<String, ClassNode> currentListElementTypes = new HashMap<String, ClassNode>()
    /**
     * Non-Int scalar parameter and field names (Phase 27): a {@code String s} or {@code Color c}
     * parameter that appears in a contract needs to translate to a sort-typed constant rather than
     * the default Int. Without this, `s == "admin"` would mismatch (Int s vs String!Sort literal).
     */
    private Map<String, ClassNode> currentScalarTypes = new HashMap<String, ClassNode>()
    /** Names of {@code AtomicInteger}/{@code AtomicLong} fields/params/locals — modelled as int cells
     *  ({@code a.get()} reads, {@code a.incrementAndGet()}/{@code set}/{@code compareAndSet} write). */
    private Set<String> currentAtomicNames = new HashSet<String>()
    /** Phase 113 — tuple-typed locals (`Tuple2<…> r = callee(…)`), name → the {@code TupleN} type. */
    private Map<String, ClassNode> currentTupleTypes = new HashMap<String, ClassNode>()
    /** Phase 116 — equational combiners in scope: `name/arity` → `[formalNames, ensuresRhs]` (see Encoder). */
    private Map<String, Object[]> currentCombiners = new HashMap<String, Object[]>()
    /** Phase B — wrapper-carrier types in scope: simple name → resolved ClassNode (see {@link Encoder#wrapperContentField}). */
    private Map<String, ClassNode> currentCarrierTypes = new HashMap<String, ClassNode>()
    /** Phase C — {@code Function}-typed params, name → declared return type (its 2nd generic), for f.apply's range. */
    private Map<String, ClassNode> currentFunctionReturnTypes = new HashMap<String, ClassNode>()
    /** Phase 61 — decimal-typed (BigDecimal/Double/Float) param/field/local/result names. */
    private Set<String> currentDecimalNames = new HashSet<String>()
    /** Phase 72 — double/float names; references skip (IEEE-754 is the FP non-goal). */
    private Map<String, Boolean> currentFpNames = new HashMap<String, Boolean>()
    /**
     * Phase 48b — body-local {@code boolean} variable names. Tracked so the SSA-fresh handle
     * in {@code checkPath}'s {@code Assign} step mints a {@code boolVar} rather than an
     * {@code intVar}, avoiding the {@code eq(intFresh, boolRhs)} sort-mismatch crash.
     */
    private Set<String> currentBooleanLocals = new HashSet<String>()
    /**
     * Phase 28 — enum classes in the same module, mapped from source-level simple name to value
     * count. Lets the encoder fold {@code Color.values().length} (and {@code .size()}) to the
     * literal enum-constant count even in re-parsed contracts where {@code Color} is just a
     * {@link VariableExpression} (no resolved type information).
     */
    private Map<String, Integer> currentEnumDomainSizes = new HashMap<String, Integer>()
    /**
     * The {@code k} bound expressions of every {@code Sets.boundedCount(_, k)} in the postcondition/measure being
     * discharged — the bcount per-add law (Phase 21) is asserted for each of these {@code k}s at every set
     * mutation, mirroring how {@link #countValueArgs} drives the per-store {@code count} law. Set per
     * discharge in {@link #checkPath}/{@link #dischargeTermination}, reset after.
     */
    private List<Expression> currentBcountKExprs = Collections.<Expression> emptyList()

    /** New Encoder wired with the current class's pure-function evaluator and set/map/list-typed names with element types. */
    private Encoder mkEncoder(SmtSession session) {
        // Phase 113 — tuple *locals* (bound to a tuple-returning call) join the tuple *params* so `r.vN`
        // resolves in every verification context (the body VC, a call-precondition discharge, an array-bounds
        // check), each of which builds its own encoder. The slot entities `r$vN` are constrained wherever the
        // preceding `r = callee(...)` assignment is replayed (it asserts the callee's @Ensures).
        Map<String, ClassNode> tuples = new LinkedHashMap<String, ClassNode>(currentTupleParams)
        tuples.putAll(currentTupleTypes)
        new Encoder(session, currentEvaluator, new TypeEnvironment(
            setElementTypes    : currentSetElementTypes,
            mapTypes           : currentMapTypes,
            listElementTypes   : currentListElementTypes,
            scalarTypes        : currentScalarTypes,
            enumDomainSizes    : currentEnumDomainSizes,
            nestedSetValueTypes: currentNestedSetValueTypes,
            listNames          : currentListNames,
            objectParams       : currentObjectParams,
            booleanLocals      : currentBooleanLocals,
            decimalNames       : currentDecimalNames,
            fpNames            : currentFpNames,
            tupleParams        : tuples,
            combiners          : currentCombiners,
            carrierTypes       : currentCarrierTypes,
            functionReturnTypes: currentFunctionReturnTypes,
            biFunctionReturnTypes: currentBiFunctionReturnTypes,
            atomicNames        : currentAtomicNames,
            method             : currentMethod))
    }

    /**
     * Phase 116 — equational combiners visible to {@code node} (its declaring class's methods): a method
     * `f(formals)` with no `@Requires` and an `@Ensures({ result == E })` where {@code E} is pure over the
     * formals (no calls, no `old`/`result`, no captured fields). Keyed {@code name/arity} → {@code [formalNames, E]}.
     * Such a call `f(x, y)` is inlined as {@code E[formals:=args]} (Encoder), so a reduction `acc = f(acc, x)`
     * matches the inline sum/extremum patterns. Sound: the combiner's `@Ensures` is verified when it is checked,
     * and there is no `@Requires` to discharge.
     */
    private static Map<String, Object[]> collectCombiners(MethodNode node) {
        Map<String, Object[]> out = new LinkedHashMap<String, Object[]>()
        ClassNode dc = node.declaringClass
        if (dc == null) return out
        for (MethodNode mn : dc.methods) {
            if (findRequires(mn) != null) continue
            Expression ens = contractAstFor(mn, 'ensures')
            if (ens instanceof BooleanExpression && !(ens instanceof NotExpression)) ens = ((BooleanExpression) ens).expression
            Expression e = equationalEnsuresRhs(ens)
            if (e == null) continue
            List<String> formals = new ArrayList<String>()
            for (Parameter p : mn.parameters) formals.add(p.name)
            if (!isPureOver(e, formals)) continue
            out.put(mn.name + '/' + mn.parameters.length, [formals, e] as Object[])
        }
        out
    }

    /** Phase B — wrapper-carrier types visible to {@code node} (its declaring class and the types of its
     *  parameters / return), keyed by simple name. A re-parsed contract's {@code new Res(a)} is unresolved, so
     *  the encoder recovers the resolved carrier ClassNode from this map. */
    private static Map<String, ClassNode> collectCarrierTypes(MethodNode node) {
        Map<String, ClassNode> out = new HashMap<String, ClassNode>()
        ClassNode dc = node.declaringClass
        if (dc != null && Encoder.isCarrier(dc)) out.put(dc.nameWithoutPackage, dc)
        for (Parameter p : node.parameters) {
            ClassNode t = p.type
            if (t != null && Encoder.isCarrier(t)) out.put(t.nameWithoutPackage, t)
        }
        ClassNode rt = node.returnType
        if (rt != null && Encoder.isCarrier(rt)) out.put(rt.nameWithoutPackage, rt)
        // Phase 133 — carrier types that appear only in the BODY: a `Length a = …` local or a `new Length(…)`
        // construction (e.g. `Area s = a * b`, where `Area` is the multiply result and `Length` only a local).
        // Without these, carrierByName misses them and the `new` can't translate. Mirrors the scalar-local scan.
        Statement cbody = (Statement) node.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (cbody == null) cbody = node.code
        if (cbody != null) try {
            cbody.visit(new ClassCodeVisitorSupport() {
                protected SourceUnit getSourceUnit() { null }
                @Override void visitClosureExpression(ClosureExpression ce) { /* skip contract closures */ }
                @Override void visitDeclarationExpression(DeclarationExpression de) {
                    for (VariableExpression v : declaredTargets(de)) {
                        ClassNode t = v.originType ?: v.type
                        if (t != null && Encoder.isCarrier(t)) out.put(t.nameWithoutPackage, t)
                    }
                    super.visitDeclarationExpression(de)
                }
                @Override void visitConstructorCallExpression(ConstructorCallExpression cce) {
                    if (cce.type != null && Encoder.isCarrier(cce.type)) out.put(cce.type.nameWithoutPackage, cce.type)
                    super.visitConstructorCallExpression(cce)
                }
            })
        } catch (Throwable ignored) {}
        out
    }

    /** Phase C — {@code Function}-typed parameters → their declared return type (the 2nd generic of
     *  {@code Function<A, R>}), so the encoder can sort {@code f.apply(x)}'s result (a bind function returns
     *  the carrier). Raw {@code Function} (no generics) is omitted → default value sort. The derivation
     *  lives in {@link ContractNormalizer} (it is also the normaliser's rewrite scope). */
    private static Map<String, ClassNode> collectFunctionReturnTypes(MethodNode node) {
        ContractNormalizer.functionReturnTypes(node)
    }

    private Map<String, ClassNode> currentBiFunctionReturnTypes = new HashMap<String, ClassNode>()

    /** {@code E} from an `@Ensures` of the shape `result == E` (either order), else null. */
    private static Expression equationalEnsuresRhs(Expression ens) {
        if (!(ens instanceof BinaryExpression)) return null
        BinaryExpression be = (BinaryExpression) ens
        if (be.operation.type != Types.COMPARE_EQUAL) return null
        if (isResultVar(be.leftExpression)) return be.rightExpression
        if (isResultVar(be.rightExpression)) return be.leftExpression
        null
    }

    private static boolean isResultVar(Expression e) {
        e instanceof VariableExpression && ((VariableExpression) e).name == 'result'
    }

    /** True if {@code e} references only the given formal names (plus literals/operators) and no method calls
     *  beyond the recognised deterministic int→String conversions (`String.valueOf(x)` / `Integer.toString(x)` /
     *  `x.toString()`) — so inlining it for any actuals is a faithful, side-effect-free substitution. */
    private static boolean isPureOver(Expression e, List<String> formals) {
        boolean[] ok = [true] as boolean[]
        e.visit(new CodeVisitorSupport() {
            @Override void visitMethodCallExpression(MethodCallExpression call) {
                Expression val = pureConversionValueExpr(call)
                if (val != null) val.visit(this)   // a recognised conversion: only its value need be pure
                else ok[0] = false                 // (its class-ref receiver is intentionally not visited)
            }
            @Override void visitStaticMethodCallExpression(StaticMethodCallExpression call) { ok[0] = false }
            @Override void visitVariableExpression(VariableExpression ve) {
                if (!formals.contains(ve.name)) ok[0] = false
            }
        })
        ok[0]
    }

    // ---- Phase 130: discharge the monoid/semigroup laws a @Reducer/@Associative combiner asserts ----

    /**
     * A {@code @Reducer}/{@code @Associative}-annotated combiner *asserts* it is a monoid/semigroup but the
     * annotation checks nothing (its own javadoc: "this annotation <em>asserts</em> the laws"). When {@code node}
     * carries one of those annotations and is an equational binary combiner (the Phase-116 shape: no
     * {@code @Requires}, {@code @Ensures({ result == E })}, {@code E} pure over the two formals), we synthesise and
     * discharge the laws it claims:
     * <ul>
     *   <li><b>associativity</b> ({@code @Associative} and {@code @Reducer}): {@code op(op(a,b),c) == op(a,op(b,c))}
     *   <li><b>identity</b> ({@code @Reducer} with a declared {@code zero}): {@code op(a,Z) == a && op(Z,a) == a}
     * </ul>
     * Each law is a synthetic void lemma whose {@code @Ensures} calls the combiner; the Phase-116 inliner unfolds
     * those calls to {@code E}, so the law reduces to the same closed goal the user would write by hand
     * (e.g. {@code (a+b)+c == a+(b+c)}). The lemma rides the normal postcondition machinery — proves silently,
     * refutes with a counterexample. Sound: the combiner's own {@code @Ensures} is verified where it is declared,
     * and there is no {@code @Requires} to discharge.
     */
    private void verifyReducerLaws(MethodNode node) {
        AnnotationNode reducer = annotationByName(node, 'Reducer')
        AnnotationNode associative = annotationByName(node, 'Associative')
        if (reducer == null && associative == null) return
        if (node.parameters.length != 2) return
        ClassNode t = node.parameters[0].type
        if (t == null || node.parameters[1].type == null || t.name != node.parameters[1].type.name) return
        if (findRequires(node) != null) return
        Expression ens = contractAstFor(node, 'ensures')
        if (ens instanceof BooleanExpression && !(ens instanceof NotExpression)) ens = ((BooleanExpression) ens).expression
        Expression e = equationalEnsuresRhs(ens)
        List<String> formals = new ArrayList<String>()
        for (Parameter p : node.parameters) formals.add(p.name)
        if (e == null || !isPureOver(e, formals)) {
            // The annotation asserts laws we can't model (non-equational / impure combiner). Say so, loudly.
            addStaticTypeError(Reporter.formatPostconditionSkipped(node.name,
                "@Reducer/@Associative combiner is not an equational combiner the verifier can model"), node)
            return
        }
        String op = node.name
        // associativity — asserted by both @Associative and @Reducer
        runReducerLaw(node, t, 'associativity', ['a', 'b', 'c'],
            "${op}(${op}(a, b), c) == ${op}(a, ${op}(b, c))")
        // identity — only @Reducer, and only when a zero is declared (an empty zero ⇒ @Associative semantics)
        if (reducer != null) {
            String zero = reducerZeroSource(reducer)
            if (zero != null && !zero.trim().isEmpty()) {
                runReducerLaw(node, t, 'identity', ['a'],
                    "${op}(a, ${zero}) == a && ${op}(${zero}, a) == a")
            }
        }
    }

    /** Synthesise a void lemma method whose {@code @Ensures} is {@code lawText} over fresh params of type
     *  {@code t}, and run it through the normal per-method verification. */
    private void runReducerLaw(MethodNode combiner, ClassNode t, String law, List<String> paramNames, String lawText) {
        List<Parameter> ps = new ArrayList<Parameter>()
        for (String n : paramNames) ps.add(new Parameter(t, n))
        MethodNode m = new MethodNode(combiner.name + '$' + law,
            Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, ClassHelper.VOID_TYPE,
            ps.toArray(new Parameter[0]), ClassNode.EMPTY_ARRAY, new BlockStatement())
        m.declaringClass = combiner.declaringClass
        m.addAnnotation(new AnnotationNode(ENSURES_TYPE))   // marker so findEnsures sees a postcondition
        AnnotationNode cs = new AnnotationNode(CONTRACT_SOURCE_TYPE)
        cs.addMember('ensures', new ConstantExpression(lawText))
        m.addAnnotation(cs)
        // Anchor on the combiner's real declaration so the (void-lemma) diagnostic actually surfaces (Phase 94).
        m.setSourcePosition(combiner)
        m.putNodeMetaData(REDUCER_LAW_KEY, [combiner.name, law] as String[])
        beforeVisitMethod(m)
        afterVisitMethod(m)
    }

    /** The {@code zero} member of a {@code @Reducer} as constant-expression source text (e.g. {@code ""},
     *  {@code 0}), or null when absent/blank (which the javadoc gives @Associative semantics — associativity only). */
    private static String reducerZeroSource(AnnotationNode reducer) {
        Expression z = reducer.getMember('zero')
        if (z instanceof ConstantExpression && ((ConstantExpression) z).value instanceof String) {
            return (String) ((ConstantExpression) z).value
        }
        null
    }

    /** First annotation on {@code m} whose type name is {@code name} or ends with {@code .name} (so a simple
     *  name matches the fully-qualified {@code groovy.transform.*}); avoids a hard compile dependency. */
    private static AnnotationNode annotationByName(MethodNode m, String name) {
        List<AnnotationNode> anns = m.getAnnotations()
        if (anns == null) return null
        for (AnnotationNode a : anns) {
            String cn = a.classNode?.name
            if (cn != null && (cn == name || cn.endsWith('.' + name))) return a
        }
        null
    }

    // ---- Phase 136: discharge the identity laws a @Monadic carrier asserts (auto-synthesis, à la @Reducer) ----

    /**
     * A {@code @Monadic} carrier *asserts* the monad/functor laws but the annotation checks nothing (its javadoc:
     * "asserts that the carrier is lawful"). When {@code carrier} is the modellable shape (a single-field immutable
     * wrapper whose bind/map are Identity-shaped — see {@link Encoder#wrapperContentField}), synthesise and discharge
     * the **Tier-1 identity laws** it claims, reading the bind/map (and the constructor as unit) off the annotation:
     * <ul>
     *   <li><b>left identity</b>: {@code new C(a).bind(f) == f.apply(a)}
     *   <li><b>right identity</b>: {@code m.bind(x -> new C(x)) == m}
     *   <li><b>functor identity</b>: {@code m.map(x -> x) == m}
     * </ul>
     * Each is a synthetic void lemma whose {@code @Ensures} the normal machinery discharges (Phases A–C). Carriers
     * outside the modellable shape are left alone (their laws simply skip loudly when referenced).
     */
    private void verifyMonadicLaws(ClassNode carrier) {
        if (carrier == null) return
        AnnotationNode monadic = null
        List<AnnotationNode> anns = carrier.annotations
        if (anns != null) for (AnnotationNode a : anns) {
            String cn = a.classNode?.name
            if (cn != null && (cn == 'Monadic' || cn.endsWith('.Monadic'))) { monadic = a; break }
        }
        if (monadic == null) return
        // Two modellable shapes: a single-value Identity wrapper (Phase 136) and a two-case carrier (M-E). Other
        // @Monadic carriers (effectful Stream, non-canonical shapes) are out of scope — no synthesis, no noise.
        boolean identity = Encoder.isIdentityWrapperCarrier(carrier)
        boolean twoCase = Encoder.isModellableTwoCaseCarrier(carrier)
        if (!identity && !twoCase) return
        String bind = monadicMember(monadic, 'bind', 'flatMap')
        String map = monadicMember(monadic, 'map', 'map')
        String cn = carrier.nameWithoutPackage
        // unit(arg): `new C(arg)` for a wrapper, `some(arg)` for a two-case carrier.
        String someF = twoCase ? Encoder.someFactoryName(carrier) : null
        Closure<String> unit = { String arg -> (twoCase ? "${someF}(${arg})" : "new ${cn}(${arg})").toString() }
        ClassNode fnCarrier = functionType(carrier)                    // Function<Object, C> — a bind function
        ClassNode fnValue = functionType(ClassHelper.OBJECT_TYPE)      // Function<Object, Object> — a map function
        runMonadicLaw(carrier, 'left identity',
            [new Parameter(ClassHelper.OBJECT_TYPE, 'a'), new Parameter(fnCarrier, 'f')] as Parameter[],
            "${unit('a')}.${bind}(f) == f.apply(a)")
        runMonadicLaw(carrier, 'right identity', [new Parameter(carrier, 'm')] as Parameter[],
            "m.${bind}({ x -> ${unit('x')} }) == m")
        runMonadicLaw(carrier, 'functor identity', [new Parameter(carrier, 'm')] as Parameter[],
            "m.${map}({ x -> x }) == m")
        runMonadicLaw(carrier, 'functor composition',
            [new Parameter(carrier, 'm'), new Parameter(fnValue, 'p'), new Parameter(fnValue, 'q')] as Parameter[],
            "m.${map}(p).${map}(q) == m.${map}({ x -> q.apply(p.apply(x)) })")
        runMonadicLaw(carrier, 'associativity',
            [new Parameter(carrier, 'm'), new Parameter(fnCarrier, 'f'), new Parameter(fnCarrier, 'g')] as Parameter[],
            "m.${bind}(f).${bind}(g) == m.${bind}({ x -> f.apply(x).${bind}(g) })")
    }

    /** A {@code Function<Object, R>} ClassNode (so {@code f.apply}'s range is known). */
    private static ClassNode functionType(ClassNode r) {
        ClassNode fn = ClassHelper.make(java.util.function.Function).getPlainNodeReference()
        fn.setGenericsTypes([new GenericsType(ClassHelper.OBJECT_TYPE.getPlainNodeReference()),
                             new GenericsType(r.getPlainNodeReference())] as GenericsType[])
        fn
    }

    /** {@code @Monadic}'s named bind/map member, or the structural default. */
    private static String monadicMember(AnnotationNode monadic, String member, String dflt) {
        Expression e = monadic.getMember(member)
        (e instanceof ConstantExpression && ((ConstantExpression) e).value instanceof String &&
            !((String) ((ConstantExpression) e).value).isEmpty()) ? (String) ((ConstantExpression) e).value : dflt
    }

    /** Synthesise a void lemma whose {@code @Ensures} is {@code lawText} over {@code params}, and run it through
     *  the normal per-method verification (the same trick as {@link #runReducerLaw}). */
    private void runMonadicLaw(ClassNode carrier, String law, Parameter[] params, String lawText) {
        MethodNode m = new MethodNode(carrier.nameWithoutPackage + '$' + law.replace(' ', '_'),
            Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, ClassHelper.VOID_TYPE,
            params, ClassNode.EMPTY_ARRAY, new BlockStatement())
        m.declaringClass = carrier
        m.addAnnotation(new AnnotationNode(ENSURES_TYPE))
        AnnotationNode cs = new AnnotationNode(CONTRACT_SOURCE_TYPE)
        cs.addMember('ensures', new ConstantExpression(lawText))
        m.addAnnotation(cs)
        m.setSourcePosition(carrier)
        m.putNodeMetaData(MONADIC_LAW_KEY, [carrier.nameWithoutPackage, law] as String[])
        beforeVisitMethod(m)
        afterVisitMethod(m)
    }

    // ---- Phase L1: rely/guarantee well-formedness (Smith §IV compatibility lemmas) ----------------

    /**
     * Discharge the rely/guarantee compatibility obligations for a class's {@code @Rely}/{@code @Guarantee}
     * conditions: each rely reflexive and transitive, each guarantee reflexive, and every thread's guarantee
     * implies every <i>other</i> thread's rely ({@code G_i ⟹ R_j}, {@code i ≠ j}). These are the lemmas that let
     * per-thread rely/guarantee proofs compose; they are pure two-state-predicate implications, discharged like
     * the lattice/monoid laws. A condition is a pure boolean method whose parameters split in half into a
     * pre-state and a matching post-state.
     */
    private void verifyRelyGuarantee(ClassNode classNode) {
        List<Object[]> relies = new ArrayList<Object[]>()       // [threadName, MethodNode]
        List<Object[]> guars = new ArrayList<Object[]>()
        for (MethodNode m : classNode.methods) {
            if (!isRgPredicate(m)) continue
            String rt = rgThread(m, RELY_TYPE)
            String gt = rgThread(m, GUARANTEE_TYPE)
            if (rt != null) relies.add([rt, m] as Object[])
            if (gt != null) guars.add([gt, m] as Object[])
        }
        if (relies.isEmpty() && guars.isEmpty()) return

        for (Object[] r : relies) {
            MethodNode m = (MethodNode) r[1]
            runRgLaw(classNode, "rely '${m.name}' is reflexive", reflexiveParams(m), reflexiveText(m))
            runRgLaw(classNode, "rely '${m.name}' is transitive", transitiveParams(m), transitiveText(m))
        }
        for (Object[] g : guars) {
            MethodNode m = (MethodNode) g[1]
            runRgLaw(classNode, "guarantee '${m.name}' is reflexive", reflexiveParams(m), reflexiveText(m))
        }
        for (Object[] g : guars) {
            MethodNode gm = (MethodNode) g[1]
            for (Object[] r : relies) {
                if (g[0] == r[0]) continue                      // a thread needn't honour its own rely
                MethodNode rm = (MethodNode) r[1]
                if (gm.parameters.length != rm.parameters.length) continue
                runRgLaw(classNode, "guarantee '${gm.name}' (${g[0]}) implies rely '${rm.name}' (${r[0]})",
                    pairParams(gm), implicationText(gm, rm))
            }
        }
    }

    /** A {@code @Rely}/{@code @Guarantee} condition: a boolean method with an even, non-zero parameter count
     *  (n pre-state + n post-state) and no contract (so it inlines as a pure function). */
    private static boolean isRgPredicate(MethodNode m) {
        int n = m.parameters.length
        return n >= 2 && (n % 2 == 0) && m.returnType != null &&
            (m.returnType.name == 'boolean' || m.returnType.name == 'java.lang.Boolean') && findRequires(m) == null
    }

    /** {@code @Rely('X')} / {@code @Guarantee('X')} → the thread name {@code 'X'}, or null. */
    private static String rgThread(MethodNode m, ClassNode annType) {
        List<AnnotationNode> anns = m.getAnnotations(annType)
        if (anns == null || anns.isEmpty()) return null
        Expression v = anns.get(0).getMember('value')
        return (v instanceof ConstantExpression && ((ConstantExpression) v).value != null) ?
            ((ConstantExpression) v).value.toString() : null
    }

    /** n fresh parameters of the pre-state types — one state, for a reflexivity lemma {@code R(s, s)}. */
    private static Parameter[] reflexiveParams(MethodNode m) {
        int n = m.parameters.length.intdiv(2)
        Parameter[] out = new Parameter[n]
        for (int i = 0; i < n; i++) out[i] = new Parameter(m.parameters[i].type, 'a' + i)
        out
    }

    private static String reflexiveText(MethodNode m) {
        int n = m.parameters.length.intdiv(2)
        String s = csv('a', 0, n)
        "${m.name}(${s}, ${s})"
    }

    /** 3n fresh parameters (three states a, b, c) for a transitivity lemma. */
    private static Parameter[] transitiveParams(MethodNode m) {
        int n = m.parameters.length.intdiv(2)
        Parameter[] out = new Parameter[3 * n]
        String[] pfx = ['a', 'b', 'c']
        for (int s = 0; s < 3; s++) for (int i = 0; i < n; i++) out[s * n + i] = new Parameter(m.parameters[i].type, pfx[s] + i)
        out
    }

    private static String transitiveText(MethodNode m) {
        int n = m.parameters.length.intdiv(2)
        String a = csv('a', 0, n), b = csv('b', 0, n), c = csv('c', 0, n)
        "(${m.name}(${a}, ${b}) && ${m.name}(${b}, ${c})) ==> ${m.name}(${a}, ${c})"
    }

    /** 2n fresh parameters (one full pre→post transition) for a compatibility lemma {@code G(s,s') ==> R(s,s')}. */
    private static Parameter[] pairParams(MethodNode m) {
        int two = m.parameters.length
        Parameter[] out = new Parameter[two]
        for (int i = 0; i < two; i++) out[i] = new Parameter(m.parameters[i].type, 'a' + i)
        out
    }

    private static String implicationText(MethodNode gm, MethodNode rm) {
        String s = csv('a', 0, gm.parameters.length)
        "${gm.name}(${s}) ==> ${rm.name}(${s})"
    }

    /** {@code "<prefix>lo, <prefix>lo+1, …, <prefix>hi-1"}. */
    private static String csv(String prefix, int lo, int hi) {
        StringBuilder sb = new StringBuilder()
        for (int i = lo; i < hi; i++) { if (i > lo) sb.append(', '); sb.append(prefix).append(i) }
        sb.toString()
    }

    /** Synthesise and discharge one rely/guarantee lemma: a {@code void} method with the given parameters whose
     *  {@code @Ensures} is {@code lawText} (a pure predicate over the {@code @Rely}/{@code @Guarantee} functions). */
    private void runRgLaw(ClassNode owner, String law, Parameter[] params, String lawText) {
        MethodNode m = new MethodNode('rg$' + Integer.toHexString(law.hashCode()),
            Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, ClassHelper.VOID_TYPE,
            params, ClassNode.EMPTY_ARRAY, new BlockStatement())
        m.declaringClass = owner
        m.addAnnotation(new AnnotationNode(ENSURES_TYPE))
        AnnotationNode cs = new AnnotationNode(CONTRACT_SOURCE_TYPE)
        cs.addMember('ensures', new ConstantExpression(lawText))
        m.addAnnotation(cs)
        m.setSourcePosition(owner)
        m.putNodeMetaData(RG_LAW_KEY, [law] as String[])
        beforeVisitMethod(m)
        afterVisitMethod(m)
    }

    /** If {@code call} is a recognised deterministic int→String conversion, the value expression being
     *  converted (so the caller can check it is pure); else null. */
    private static Expression pureConversionValueExpr(MethodCallExpression call) {
        String m = call.methodAsString
        Expression obj = call.objectExpression
        List<Expression> args = (call.arguments instanceof ArgumentListExpression) ?
            ((ArgumentListExpression) call.arguments).expressions : Collections.<Expression>emptyList()
        String owner = channelOwnerName(obj)
        if (owner == 'String' && m == 'valueOf' && args.size() == 1) return args.get(0)
        if (owner == 'Integer' && m == 'toString' && args.size() == 1) return args.get(0)
        if (m == 'toString' && args.isEmpty() && owner != 'String' && owner != 'Integer') return obj
        null
    }

    /**
     * Set-typed parameters and declaring-class fields visible to {@code node}, paired with element
     * type (Phase 27). Element type comes from the declared generic if present
     * ({@code Set<String> tags} → String); a raw {@code Set} defaults to Integer for back-compat with
     * the Phase-16 Int-element behaviour. Step 4 wires non-Int element types end-to-end; this collect
     * pass already extracts them so a Set<String> field flows the right ClassNode to the encoder.
     */
    private static Map<String, ClassNode> collectSetElementTypes(MethodNode node) {
        Map<String, ClassNode> out = new LinkedHashMap<String, ClassNode>()
        for (Parameter p : node.parameters) if (isSetType(p.type)) out.put(p.name, firstGenericOrInt(p.type))
        ClassNode dc = node.declaringClass
        if (dc != null) for (FieldNode f : dc.fields) if (isSetType(f.type)) out.put(f.name, firstGenericOrInt(f.type))
        out
    }

    /**
     * Phase 45 — class-typed (object) parameters visible to {@code node}, paired with the declared
     * {@link ClassNode}. Filters out anything already owned by the other dispatch paths (sets,
     * maps, lists, primitives, primitive wrappers, String, enums, arrays) so this is the catch-all
     * for "named object with fields, possibly carrying class invariants". A reference here drives
     * the cross-class reasoning: receiver-qualified field reads, invariant assumption, etc.
     */
    /** Phase 193 — per-method catch-coverage index: for each try block, its source range plus the set of
     *  implicit-obligation exception names its handlers cover (curated, conservative — an unrecognised
     *  catch type covers nothing, so the obligation keeps refuting). Rebuilt per method. */
    private List<Object[]> currentCatchCoverage = new ArrayList<Object[]>()

    /** Catch-parameter simple name → the implicit-obligation exceptions it (super)covers. Curated: exact
     *  types, their JDK supertypes (NFE <: IllegalArgumentException; the broad RuntimeException /
     *  Exception / Throwable), nothing inferred. */
    private static final Map<String, List<String>> CATCH_COVERS = [
        'NullPointerException'          : ['NullPointerException'],
        'ArithmeticException'           : ['ArithmeticException'],
        'IndexOutOfBoundsException'     : ['IndexOutOfBoundsException'],
        'NumberFormatException'         : ['NumberFormatException'],
        'IllegalArgumentException'      : ['NumberFormatException'],
        'RuntimeException'              : ['NullPointerException', 'ArithmeticException', 'IndexOutOfBoundsException', 'NumberFormatException'],
        'Exception'                     : ['NullPointerException', 'ArithmeticException', 'IndexOutOfBoundsException', 'NumberFormatException'],
        'Throwable'                     : ['NullPointerException', 'ArithmeticException', 'IndexOutOfBoundsException', 'NumberFormatException'],
    ]

    /** Walk the clean body for try blocks and their handlers' coverage (see {@link #currentCatchCoverage}). */
    private static List<Object[]> collectCatchCoverage(MethodNode node) {
        List<Object[]> out = new ArrayList<Object[]>()
        Statement body = (Statement) node.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (body == null) body = node.code
        if (body == null) return out
        try {
            body.visit(new CodeVisitorSupport() {
                @Override void visitTryCatchFinally(org.codehaus.groovy.ast.stmt.TryCatchStatement tcs) {
                    Statement tb = tcs.tryStatement
                    Set<String> covered = new HashSet<String>()
                    for (org.codehaus.groovy.ast.stmt.CatchStatement cs : tcs.catchStatements) {
                        List<String> c = CATCH_COVERS.get(cs.variable?.type?.nameWithoutPackage)
                        if (c != null) covered.addAll(c)
                    }
                    if (tb != null && !covered.isEmpty() && tb.lineNumber > 0) {
                        out.add([tb.lineNumber, tb.columnNumber, tb.lastLineNumber, tb.lastColumnNumber, covered] as Object[])
                    }
                    super.visitTryCatchFinally(tcs)
                }
            })
        } catch (Throwable ignored) { }
        out
    }

    /** True iff {@code at} sits inside a try block whose handlers cover {@code exceptionName} — the
     *  obligation\'s failure mode is then *defined behaviour* (control transfers to the handler, whose
     *  path Phase 192 models), so no obligation fires. Synthetic positions (line -1) never match. */
    private boolean catchCovered(org.codehaus.groovy.ast.ASTNode at, String exceptionName) {
        if (at == null || at.lineNumber < 0) return false
        int l = at.lineNumber, c = at.columnNumber
        for (Object[] r : currentCatchCoverage) {
            int sl = (int) r[0], sc = (int) r[1], el = (int) r[2], ec = (int) r[3]
            boolean after = l > sl || (l == sl && c >= sc)
            boolean before = l < el || (l == el && c <= ec)
            if (after && before && ((Set<String>) r[4]).contains(exceptionName)) return true
        }
        false
    }

    /** The exception an implicit-obligation site would throw uncaught, else null (never suppressed). */
    private static String obligationExceptionOf(Object site) {
        if (site instanceof IndexSite || site instanceof StringCharAtSite || site instanceof StringSubstringSite)
            return 'IndexOutOfBoundsException'
        if (site instanceof DivideSite) return 'ArithmeticException'
        if (site instanceof ParseSite) return 'NumberFormatException'
        if (site instanceof DerefSite) return 'NullPointerException'
        null   // AssertSite (the developer\'s own spec) and OverflowSite (wraps, never throws) stay checked
    }

    private static Map<String, ClassNode> collectObjectParams(MethodNode node) {
        Map<String, ClassNode> out = new LinkedHashMap<String, ClassNode>()
        ClassNode declaring = node.declaringClass
        for (Parameter p : node.parameters) {
            if (isCrossClassObjectType(p.type, declaring)) out.put(p.name, p.type)
        }
        out
    }

    /** Tuple-typed (`TupleN<...>`) parameters and declaring-class fields → the tuple {@link ClassNode}. */
    private static Map<String, ClassNode> collectTupleParams(MethodNode node) {
        Map<String, ClassNode> out = new LinkedHashMap<String, ClassNode>()
        for (Parameter p : node.parameters) {
            if (isTupleType(p.type)) out.put(p.name, p.type)
        }
        ClassNode dc = node.declaringClass
        if (dc != null) for (FieldNode f : dc.fields) {
            if (isTupleType(f.type)) out.put(f.name, f.type)
        }
        out
    }

    private static boolean isTupleType(ClassNode t) {
        String n = t?.nameWithoutPackage
        n != null && (n ==~ /Tuple\d+/)
    }

    /** True if {@code t} is a non-primitive, non-collection, non-array class distinct from the declaring class. */
    private static boolean isCrossClassObjectType(ClassNode t, ClassNode declaringClass) {
        if (t == null) return false
        if (t.isArray()) return false
        if (isSetType(t) || isMapType(t) || isListType(t)) return false
        if (isNonIntScalar(t)) return false   // String, enums — own dispatch (Phase 27)
        if (isIntElement(t)) return false     // primitive wrappers — own dispatch
        String n = t.name
        // Filter out java.lang.Object, java.lang.* boxed, etc.
        if (n == 'java.lang.Object' || n == 'java.lang.String' || n?.startsWith('java.lang.')) return false
        // Same-class receivers (`this`) are handled by Phase 15a/b; foreign classes only.
        if (declaringClass != null && n == declaringClass.name) return false
        // Must have at least one field for the cross-class reads to be meaningful.
        try {
            return t.fields != null && !t.fields.isEmpty()
        } catch (Throwable ignored) {
            return false
        }
    }

    /**
     * Map-typed names visible to {@code node}, each paired with a {@code [keyType, valueType]} pair.
     * Raw {@code Map} defaults to {@code [Integer, Integer]} for back-compat. (Phase 27.)
     */
    private static Map<String, ClassNode[]> collectMapTypes(MethodNode node) {
        Map<String, ClassNode[]> out = new LinkedHashMap<String, ClassNode[]>()
        for (Parameter p : node.parameters) if (isMapType(p.type)) out.put(p.name, twoGenericsOrInt(p.type))
        ClassNode dc = node.declaringClass
        if (dc != null) for (FieldNode f : dc.fields) if (isMapType(f.type)) out.put(f.name, twoGenericsOrInt(f.type))
        out
    }

    /**
     * Phase 36 — for each visible {@code Map<K, Set<V>>}, the inner {@code Set}'s element type
     * {@code V}. The map's value type goes through two layers of generics ({@code gens[1]} of the
     * map, then {@code gens[0]} of that {@code Set}); any layer that isn't parameterised drops the
     * map from the result, so {@code Map<K, Set>} (raw inner set) won't be treated as nested.
     */
    private static Map<String, ClassNode> collectNestedSetValueTypes(MethodNode node) {
        Map<String, ClassNode> out = new LinkedHashMap<String, ClassNode>()
        for (Parameter p : node.parameters) {
            if (isMapType(p.type)) {
                ClassNode elem = nestedSetElementType(p.type)
                if (elem != null) out.put(p.name, elem)
            }
        }
        ClassNode dc = node.declaringClass
        if (dc != null) for (FieldNode f : dc.fields) {
            if (isMapType(f.type)) {
                ClassNode elem = nestedSetElementType(f.type)
                if (elem != null) out.put(f.name, elem)
            }
        }
        out
    }

    /** The inner element type of a {@code Map<_, Set<X>>}, or null if the value isn't a parameterised Set. */
    private static ClassNode nestedSetElementType(ClassNode mapType) {
        try {
            def mapGens = mapType?.genericsTypes
            if (mapGens == null || mapGens.length < 2) return null
            ClassNode valueType = mapGens[1].type
            if (valueType == null || !isSetType(valueType)) return null
            def setGens = valueType.genericsTypes
            if (setGens == null || setGens.length < 1 || setGens[0].type == null) return null
            return setGens[0].type
        } catch (Throwable ignored) {
            return null
        }
    }

    /**
     * Phase 37 — annotation simple-names that mark a type use as <em>non-null</em>. The set mirrors
     * what {@code groovy.typecheckers.NullChecker} matches: {@code @NonNull} (Checker Framework /
     * Android / Lombok), {@code @NotNull} (JetBrains), {@code @Nonnull} (JSR-305),
     * {@code @MonotonicNonNull} (Checker Framework). Element-level annotation on a list's generic
     * type ({@code List<@NonNull String>}) suppresses the per-element NPE obligation on
     * {@code xs[i].method()}.
     */
    private static final Set<String> NON_NULL_ANNOTATION_NAMES = [
        'NonNull', 'NotNull', 'Nonnull', 'MonotonicNonNull'
    ] as Set<String>

    /**
     * Phase 37 — annotation simple-names that mark a type use as <em>nullable</em>. Since Phase 239
     * an explicit {@code @Nullable}/{@code @CheckForNull} at a position <b>defeats</b> any
     * {@code @NonNull}-derived effect at that same position — the assumption sites (the param/field
     * non-null assumption, the implicit field invariant, the element/component obligation
     * suppression) and, uniformly, the Phase 131 return obligation: on a contradictory declaration
     * the author's disclaimer wins, the standard nullable-wins tool posture. The unannotated default
     * still carries the implicit obligation, so in the default mode {@code @Nullable} alone changes
     * nothing — a "non-null-by-default" strict mode (the full GROOVY-12252 parity) remains a future
     * phase, and this set is what it would key "explicitly nullable" off.
     */
    private static final Set<String> NULLABLE_ANNOTATION_NAMES = ['Nullable', 'CheckForNull'] as Set<String>

    /**
     * True if any of {@code anns} has a simple-name matching one of {@code names}. "Simple name"
     * here is the segment after the last {@code .} *and* after the last {@code $} — so an inner
     * {@code @C.NonNull} (which Groovy renders as {@code C$NonNull} in {@code nameWithoutPackage})
     * matches just as the top-level {@code @NonNull} does. Mirrors how NullChecker matches by
     * simple name, robust to annotation classes declared as inner types.
     */
    /**
     * Phase 44 — true if {@code node} or its declaring class carries an annotation whose simple
     * name is {@code simpleName}. Used for {@code @CheckOverflow} detection; a class-level
     * annotation enables the check for every method, the method-level form scopes it to one.
     */
    private static boolean methodOrClassHasAnnotation(MethodNode node, String simpleName) {
        if (annotationsHave(node.annotations, simpleName)) return true
        ClassNode dc = node.declaringClass
        if (dc != null && annotationsHave(dc.annotations, simpleName)) return true
        false
    }

    private static boolean annotationsHave(List<AnnotationNode> anns, String simpleName) {
        if (anns == null) return false
        for (AnnotationNode a : anns) {
            ClassNode cn = a?.classNode
            if (cn == null) continue
            String n = cn.nameWithoutPackage
            if (n == null) continue
            int dollar = n.lastIndexOf('$')
            String simple = dollar >= 0 ? n.substring(dollar + 1) : n
            if (simple == simpleName) return true
        }
        false
    }

    private static boolean hasAnnotationNamed(List<AnnotationNode> anns, Set<String> names) {
        if (anns == null) return false
        for (AnnotationNode a : anns) {
            ClassNode cn = a?.classNode
            if (cn == null) continue
            String n = cn.nameWithoutPackage
            if (n == null) continue
            int dollar = n.lastIndexOf('$')
            String simple = dollar >= 0 ? n.substring(dollar + 1) : n
            if (names.contains(simple)) return true
        }
        false
    }

    /**
     * True if the {@code ClassNode} {@code t} carries one of {@code names} as a <em>type</em> annotation.
     *
     * <p>A {@code TYPE_USE}-targeted annotation ({@code List<@NonNull String>}, and everything JSpecify
     * writes) does <strong>not</strong> land in {@link ClassNode#getAnnotations()} — Groovy keeps it in the
     * separate {@link ClassNode#getTypeAnnotations()} list. Reading only the former is why this matcher
     * looked like a Groovy limitation ("the AST doesn't preserve type-use annotations on generics") when it
     * was an accessor bug: the data has been on {@code getTypeAnnotations()} since at least Groovy 5.0.8 for
     * source-declared types, and since GROOVY-12206 (6.0.0-beta-1) for types read off <em>compiled</em>
     * classes too — so a JSpecify-annotated Java dependency now matches as well. Both lists are consulted
     * because a declaration-targeted annotation ({@code @NonNull String[] ys} where the annotation also
     * targets {@code PARAMETER}) still arrives on the declaration.
     */
    private static boolean hasTypeAnnotationNamed(ClassNode t, Set<String> names) {
        if (t == null) return false
        return hasAnnotationNamed(t.annotations, names) || hasAnnotationNamed(t.typeAnnotations, names)
    }

    /**
     * For a list-typed {@code ClassNode}, return true if its element generic carries a non-null
     * annotation. Reads annotations off the element {@link GenericsType}'s inner ClassNode — the
     * shape Groovy's parser leaves for {@code List<@NonNull String>} — through
     * {@link #hasTypeAnnotationNamed}, so the {@code TYPE_USE} spelling is seen.
     */
    private static boolean hasNonNullElementAnnotation(ClassNode listType) {
        try {
            def gens = listType?.genericsTypes
            if (gens == null || gens.length < 1) return false
            // Phase 239 — an explicit element @Nullable defeats the suppression (nullable wins).
            return hasTypeAnnotationNamed(gens[0]?.type, NON_NULL_ANNOTATION_NAMES) &&
                   !hasTypeAnnotationNamed(gens[0]?.type, NULLABLE_ANNOTATION_NAMES)
        } catch (Throwable ignored) {
            return false
        }
    }

    /** Phase 131 — true if {@code node} returns a reference type carrying a NullChecker-style @NonNull
     *  annotation (on the method or on the return type use). Primitive/void returns can't be null → false. */
    private static boolean hasNonNullReturn(MethodNode node) {
        if (node instanceof ConstructorNode) return false
        ClassNode rt = node.returnType
        if (rt == null || ClassHelper.isPrimitiveType(rt) || rt == ClassHelper.VOID_TYPE) return false
        // Phase 239 — a @Nullable on the same declaration defeats the obligation (nullable wins on a
        // contradictory declaration; the author explicitly disclaimed the non-null claim).
        boolean pos = hasAnnotationNamed(node.annotations, NON_NULL_ANNOTATION_NAMES) ||
                      hasTypeAnnotationNamed(rt, NON_NULL_ANNOTATION_NAMES)
        boolean veto = hasAnnotationNamed(node.annotations, NULLABLE_ANNOTATION_NAMES) ||
                       hasTypeAnnotationNamed(rt, NULLABLE_ANNOTATION_NAMES)
        return pos && !veto
    }

    /**
     * Same shape as {@link #hasNonNullElementAnnotation} but for the component type of an array.
     *
     * <p>Deliberately reads the <em>component</em> only, because only the component means "the
     * <em>elements</em> are non-null" — the claim that suppresses the per-element obligation. The array
     * ClassNode's own type annotations say the <em>array reference</em> is non-null, a different statement;
     * consulting them here would suppress an element obligation the author never disclaimed.
     *
     * <p><b>Where each spelling lands differs by source language</b> (measured on 6.0.0-beta-1):
     * <ul>
     *   <li><b>javac</b> follows the JLS — {@code @NonNull String[] ys} annotates the component (elements),
     *       {@code String @NonNull [] zs} the array type. So this matcher fires for a compiled
     *       (e.g. JSpecify-annotated Java) signature, which is what GROOVY-12206 newly made readable.</li>
     *   <li><b>Groovy source</b> puts a leading {@code @NonNull String[] xs} on the <em>parameter
     *       declaration</em> even for a {@code TYPE_USE}-only annotation, and only the postfix
     *       {@code String @NonNull []} on the array type. Neither is a component annotation — so in Groovy
     *       source there is no spelling for array <em>element</em> nullity, and this matcher stays inert
     *       there by design. {@code List<@NonNull String>} is the working source-level form; the
     *       {@code @Requires} contract remains the general one.</li>
     * </ul>
     */
    private static boolean hasNonNullComponentAnnotation(ClassNode arrType) {
        try {
            // Phase 239 — an explicit component @Nullable defeats the suppression (nullable wins).
            return hasTypeAnnotationNamed(arrType?.componentType, NON_NULL_ANNOTATION_NAMES) &&
                   !hasTypeAnnotationNamed(arrType?.componentType, NULLABLE_ANNOTATION_NAMES)
        } catch (Throwable ignored) {
            return false
        }
    }

    /**
     * Phase 41 — every {@link java.util.List}-typed name visible to {@code node}, irrespective of
     * element type. Used by the encoder to route {@code xs.count(v)} for lists through bounded
     * count {@code bcount(arr, v, 0, sizeOf(xs))} so the count tracks size-changing mutations
     * faithfully. Distinct from {@link #collectListElementTypes} which only collects non-Int lists.
     */
    private static Set<String> collectListNames(MethodNode node) {
        Set<String> out = new LinkedHashSet<String>()
        for (Parameter p : node.parameters) if (isListType(p.type)) out.add(p.name)
        ClassNode dc = node.declaringClass
        if (dc != null) for (FieldNode f : dc.fields) if (isListType(f.type)) out.add(f.name)
        out
    }

    /**
     * Phase 37 — names of List<X>/X[] containers visible to {@code node} whose element generic
     * (or array component) carries a {@code @NonNull}-like annotation. The implicit per-element
     * NPE obligation on {@code xs[i].method()} is skipped for these — the user has declared the
     * elements non-null, we trust the declaration.
     */
    private static Set<String> collectNonNullElementContainers(MethodNode node) {
        Set<String> out = new LinkedHashSet<String>()
        for (Parameter p : node.parameters) {
            if (isListType(p.type) && hasNonNullElementAnnotation(p.type)) out.add(p.name)
            else if (p.type?.isArray() && hasNonNullComponentAnnotation(p.type)) out.add(p.name)
        }
        ClassNode dc = node.declaringClass
        if (dc != null) for (FieldNode f : dc.fields) {
            if (isListType(f.type) && hasNonNullElementAnnotation(f.type)) out.add(f.name)
            else if (f.type?.isArray() && hasNonNullComponentAnnotation(f.type)) out.add(f.name)
        }
        out
    }

    /**
     * List-typed names with non-Int element types visible to {@code node}. Lists with Int elements
     * (or raw) keep the existing shape-based path — only non-Int receivers need the encoder hint.
     */
    private static Map<String, ClassNode> collectListElementTypes(MethodNode node) {
        Map<String, ClassNode> out = new LinkedHashMap<String, ClassNode>()
        for (Parameter p : node.parameters) {
            if (isListType(p.type)) {
                ClassNode elem = firstGenericOrInt(p.type)
                if (!isIntElement(elem)) out.put(p.name, elem)
            } else if (p.type?.isArray()) {              // Phase 77 — non-Int array component (e.g. double[])
                ClassNode comp = p.type.componentType
                if (comp != null && !isIntElement(comp)) out.put(p.name, comp)
            }
        }
        ClassNode dc = node.declaringClass
        if (dc != null) for (FieldNode f : dc.fields) {
            if (isListType(f.type)) {
                ClassNode elem = firstGenericOrInt(f.type)
                if (!isIntElement(elem)) out.put(f.name, elem)
            } else if (f.type?.isArray()) {
                ClassNode comp = f.type.componentType
                if (comp != null && !isIntElement(comp)) out.put(f.name, comp)
            }
        }
        // Phase 46a — typed locals like {@code List<String> result = []} carry their element type
        // on the DeclarationExpression's LHS. Without this scan, the empty-factory {@code []} mints
        // a default Int-element array and a subsequent {@code result.add(stringValue)} crashes Z3
        // with a sort-mismatch. The body walk is best-effort (failures here just leave the entry
        // unset, the same state as today).
        // Same clean-body scan as collectScalarTypes (Phase 47h fix): use the pre-contract body
        // so groovy-contracts' injected {@code final String result = …} declaration doesn't
        // pollute the type map.
        Statement cleanBody = (Statement) node.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (cleanBody == null) cleanBody = node.code
        if (cleanBody != null) try {
            cleanBody.visit(new ClassCodeVisitorSupport() {
                protected SourceUnit getSourceUnit() { null }
                @Override
                void visitClosureExpression(ClosureExpression ce) {
                    // Skip contract closures.
                }
                @Override
                void visitDeclarationExpression(DeclarationExpression de) {
                    for (VariableExpression v : declaredTargets(de)) {
                        ClassNode t = v.originType ?: v.type
                        String lname = v.name
                        if (t != null && isListType(t)) {
                            ClassNode elem = firstGenericOrInt(t)
                            if (!isIntElement(elem)) out.putIfAbsent(lname, elem)
                        } else if (t != null && t.isArray()) {
                            // Phase 123 — a typed *local* array (`String[] a = new String[n]`) carries its
                            // component type the same way a String[] parameter does; without this it defaults
                            // to an Int-element array and a String store crashes Z3 with a sort mismatch.
                            ClassNode comp = t.componentType
                            if (comp != null && !isIntElement(comp)) out.putIfAbsent(lname, comp)
                        }
                    }
                    super.visitDeclarationExpression(de)
                }
            })
        } catch (Throwable ignored) {}
        out
    }

    /** The first generic type parameter of {@code t}, or {@code Integer} if {@code t} is raw. */
    private static ClassNode firstGenericOrInt(ClassNode t) {
        try {
            def gens = t?.genericsTypes
            if (gens != null && gens.length >= 1 && gens[0].type != null) return gens[0].type
        } catch (Throwable ignored) {}
        ClassHelper.Integer_TYPE
    }

    /** A two-element {@code [key, value]} pair from {@code t}'s generics; {@code [Integer, Integer]} if raw. */
    private static ClassNode[] twoGenericsOrInt(ClassNode t) {
        ClassNode k = ClassHelper.Integer_TYPE, v = ClassHelper.Integer_TYPE
        try {
            def gens = t?.genericsTypes
            if (gens != null) {
                if (gens.length >= 1 && gens[0].type != null) k = gens[0].type
                if (gens.length >= 2 && gens[1].type != null) v = gens[1].type
            }
        } catch (Throwable ignored) {}
        [k, v] as ClassNode[]
    }

    /** True for {@code int}/{@code Integer} and the other Int-modelled scalar types. */
    private static boolean isIntElement(ClassNode t) {
        String n = t?.name
        n == 'int' || n == 'long' || n == 'short' || n == 'byte' || n == 'char' ||
            n == 'java.lang.Integer' || n == 'java.lang.Long' || n == 'java.lang.Short' ||
            n == 'java.lang.Byte' || n == 'java.lang.Character'
    }

    /**
     * Non-Int scalar parameter/field names visible to {@code node} (Phase 27 step 9).
     * Currently recognises {@code String} and enum types. Lets the encoder translate a
     * {@code String s} parameter as a String!Sort constant — without this, {@code s == "admin"}
     * mismatches (Int s, String literal RHS).
     */
    private static Map<String, ClassNode> collectScalarTypes(MethodNode node) {
        Map<String, ClassNode> out = new LinkedHashMap<String, ClassNode>()
        for (Parameter p : node.parameters) {
            ClassNode t = p.type
            if (isNonIntScalar(t) || Encoder.isCarrier(t)) out.put(p.name, t)   // Phase B — carrier params
        }
        ClassNode dc = node.declaringClass
        if (dc != null) for (FieldNode f : dc.fields) {
            ClassNode t = f.type
            if (isNonIntScalar(t) || Encoder.isCarrier(t)) out.put(f.name, t)
        }
        // Phase 47h — the implicit {@code result} variable in {@code @Ensures} takes the
        // method's return type. Without this entry, a {@code @Ensures({ result.startsWith(…) })}
        // postcondition on a String-returning method would fall through {@link Encoder#isStringReceiver}
        // (not a parameter / field / typed local) and skip honestly.
        ClassNode retType = node.returnType
        if (retType != null && (isNonIntScalar(retType) || Encoder.isCarrier(retType))) out.put('result', retType)   // Phase B/133 — carrier result
        // Phase 47h — typed locals like {@code String name = "world"} carry their type on the
        // DeclarationExpression's LHS. Without this, GString interpolation of a String local
        // falls into the int path and crashes Z3 with a sort mismatch. Scan the CLEAN
        // pre-contract body snapshot (groovy-contracts injects {@code final String result = …}
        // and other synthetic declarations into {@code node.code}; the user's untouched body
        // lives in {@link ContractExpansionTransform#ORIGINAL_BODY_KEY}). Closure bodies (where
        // contract {@code @Requires}/{@code @Ensures} closures stand even in the clean body) are
        // skipped as a belt-and-braces measure.
        Statement cleanBody = (Statement) node.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (cleanBody == null) cleanBody = node.code
        if (cleanBody != null) try {
            cleanBody.visit(new ClassCodeVisitorSupport() {
                protected SourceUnit getSourceUnit() { null }
                @Override
                void visitClosureExpression(ClosureExpression ce) {
                    // Skip — contract closures contain re-bound variables we shouldn't pick up.
                }
                @Override
                void visitDeclarationExpression(DeclarationExpression de) {
                    for (VariableExpression v : declaredTargets(de)) {
                        ClassNode t = v.originType ?: v.type
                        if (t != null && (isNonIntScalar(t) || Encoder.isCarrier(t))) {   // Phase 133 — carrier locals
                            out.putIfAbsent(v.name, t)
                        }
                    }
                    super.visitDeclarationExpression(de)
                }
            })
        } catch (Throwable ignored) {}
        out
    }

    /**
     * Phase 236 — the variable targets a declaration binds: the single scalar LHS, or each component of
     * a multiple-assignment `def (int a, String b) = …` (a {@link TupleExpression} LHS whose components
     * are {@link VariableExpression}s, each carrying its own declared type on {@code originType} —
     * GROOVY-12228 makes the typed spelling meaningful to STC, so the harvesters must see it too).
     * Every declared-type harvester iterates this instead of matching the scalar shape directly; the
     * untyped `def (a, b)` form yields components whose dynamic type fails each harvester's own type
     * test, so behaviour there is unchanged.
     */
    private static List<VariableExpression> declaredTargets(DeclarationExpression de) {
        Expression lhs = de.leftExpression
        if (lhs instanceof VariableExpression) return Collections.singletonList((VariableExpression) lhs)
        if (lhs instanceof TupleExpression) {
            List<VariableExpression> out = new ArrayList<VariableExpression>()
            for (Expression t : ((TupleExpression) lhs).expressions) {
                if (t instanceof VariableExpression) out.add((VariableExpression) t)
            }
            return out
        }
        Collections.<VariableExpression> emptyList()
    }

    /** True if {@code t} is {@code java.util.concurrent.atomic.AtomicInteger} or {@code AtomicLong} — the two
     *  atomics modelled as int cells (both are a single mutable integer behind get/set/CAS). */
    private static boolean isAtomicIntType(ClassNode t) {
        String n = t?.name
        n == 'java.util.concurrent.atomic.AtomicInteger' || n == 'java.util.concurrent.atomic.AtomicLong'
    }

    /** Names visible to {@code node} of {@code AtomicInteger}/{@code AtomicLong} type — fields, parameters and
     *  explicitly-typed locals. The verifier models each as an int cell (see {@link Encoder#atomicNames}). */
    private static Set<String> collectAtomicNames(MethodNode node) {
        Set<String> out = new HashSet<String>()
        for (Parameter p : node.parameters) if (isAtomicIntType(p.type)) out.add(p.name)
        ClassNode dc = node.declaringClass
        if (dc != null) for (FieldNode f : dc.fields) if (isAtomicIntType(f.type)) out.add(f.name)
        Statement cleanBody = (Statement) node.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (cleanBody == null) cleanBody = node.code
        if (cleanBody != null) try {
            cleanBody.visit(new ClassCodeVisitorSupport() {
                protected SourceUnit getSourceUnit() { null }
                @Override void visitClosureExpression(ClosureExpression ce) { }
                @Override
                void visitDeclarationExpression(DeclarationExpression de) {
                    for (VariableExpression v : declaredTargets(de)) {
                        if (isAtomicIntType(v.originType ?: v.type)) out.add(v.name)
                    }
                    super.visitDeclarationExpression(de)
                }
            })
        } catch (Throwable ignored) {}
        out
    }

    /** True if {@code t} is a decimal type Groovy models with exact reals: BigDecimal/Double/Float. */
    private static boolean isDecimalType(ClassNode t) {
        if (t == null) return false
        String n = t.name
        return n == 'java.math.BigDecimal'   // Phase 72 — only BigDecimal is exact; double/float are IEEE-754
    }

    /**
     * Phase 61 — names (params, declaring-class fields, the implicit {@code result}, and typed
     * locals) whose declared type is a decimal (BigDecimal/Double/Float). A reference to one of
     * these lowers to Z3's Real sort. Same clean-body + closure-skip scan as {@link #collectScalarTypes}.
     */
    private static Set<String> collectDecimalNames(MethodNode node) {
        Set<String> out = new LinkedHashSet<String>()
        for (Parameter p : node.parameters) {
            if (isDecimalType(p.type)) out.add(p.name)
        }
        ClassNode dc = node.declaringClass
        if (dc != null) for (FieldNode f : dc.fields) {
            if (isDecimalType(f.type)) out.add(f.name)
        }
        if (isDecimalType(node.returnType)) out.add('result')
        Statement cleanBody = (Statement) node.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (cleanBody == null) cleanBody = node.code
        if (cleanBody != null) try {
            cleanBody.visit(new ClassCodeVisitorSupport() {
                protected SourceUnit getSourceUnit() { null }
                @Override void visitClosureExpression(ClosureExpression ce) { /* skip contract closures */ }
                @Override
                void visitDeclarationExpression(DeclarationExpression de) {
                    for (VariableExpression v : declaredTargets(de)) {
                        if (isDecimalType(v.originType ?: v.type)) out.add(v.name)
                    }
                    super.visitDeclarationExpression(de)
                }
            })
        } catch (Throwable ignored) {}
        out
    }

    /** True if {@code t} is {@code double}/{@code float} — IEEE-754, the FP non-goal (modelled by skipping). */
    private static boolean isDoubleType(ClassNode t) {
        if (t == null) return false
        String n = t.name
        n == 'double' || n == 'float' || n == 'java.lang.Double' || n == 'java.lang.Float'
    }

    /** True if {@code t} is double-precision (double/Double), vs single-precision (float/Float). */
    private static boolean isDoublePrecision(ClassNode t) {
        t != null && (t.name == 'double' || t.name == 'java.lang.Double')
    }

    /**
     * Phase 73 — {@code double}/{@code float} names (params/fields/result/locals) → precision
     * ({@code true} = double/Float64). Modelled with Z3's faithful IEEE-754 FP theory in straight-line
     * code (Phase 72 skipped them; exact Int/Real modelling was unsound — `(a + b) - b == a` and
     * `0.1d + 0.2d == 0.3d` hold exactly but are false at runtime).
     */
    private static Map<String, Boolean> collectFpNames(MethodNode node) {
        Map<String, Boolean> out = new LinkedHashMap<String, Boolean>()
        for (Parameter p : node.parameters) if (isDoubleType(p.type)) out.put(p.name, isDoublePrecision(p.type))
        ClassNode dc = node.declaringClass
        if (dc != null) for (FieldNode f : dc.fields) if (isDoubleType(f.type)) out.put(f.name, isDoublePrecision(f.type))
        if (isDoubleType(node.returnType)) out.put('result', isDoublePrecision(node.returnType))
        Statement cleanBody = (Statement) node.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (cleanBody == null) cleanBody = node.code
        if (cleanBody != null) try {
            cleanBody.visit(new ClassCodeVisitorSupport() {
                protected SourceUnit getSourceUnit() { null }
                @Override void visitClosureExpression(ClosureExpression ce) {}
                @Override
                void visitDeclarationExpression(DeclarationExpression de) {
                    for (VariableExpression v : declaredTargets(de)) {
                        ClassNode t = v.originType ?: v.type
                        if (isDoubleType(t)) out.put(v.name, isDoublePrecision(t))
                    }
                    super.visitDeclarationExpression(de)
                }
            })
        } catch (Throwable ignored) {}
        out
    }

    /**
     * Phase 48b — collect names of {@code boolean} locals declared in the method body. Used by
     * the SSA-fresh-handle path so {@code boolean composite = false} mints {@code boolVar('composite#1')}
     * rather than {@code intVar} (which then crashes at {@code eq(intFresh, boolRhs)}). Same
     * clean-body + closure-skip pattern as {@link #collectScalarTypes}.
     */
    private static boolean isBooleanType(ClassNode t) {
        t != null && (t.name == 'boolean' || t.name == 'java.lang.Boolean')
    }

    /**
     * Boolean names — params, declaring-class fields, the implicit {@code result}, and body locals — so
     * the SSA-fresh-handle path and {@code varFor} mint a {@code boolVar} rather than an {@code intVar}.
     * Without the param/field/result cases a boolean *field* write {@code b = !b} crashed Z3 with
     * {@code eq(intFresh, boolRhs)} / {@code not(intExpr)} (the {@code String}/decimal field fix's
     * boolean sibling).
     */
    private static Set<String> collectBooleanLocals(MethodNode node) {
        Set<String> out = new HashSet<String>()
        for (Parameter p : node.parameters) if (isBooleanType(p.type)) out.add(p.name)
        ClassNode dc = node.declaringClass
        if (dc != null) for (FieldNode f : dc.fields) if (isBooleanType(f.type)) out.add(f.name)
        if (isBooleanType(node.returnType)) out.add('result')
        Statement cleanBody = (Statement) node.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (cleanBody == null) cleanBody = node.code
        if (cleanBody == null) return out
        try {
            cleanBody.visit(new ClassCodeVisitorSupport() {
                protected SourceUnit getSourceUnit() { null }
                @Override
                void visitClosureExpression(ClosureExpression ce) {}
                @Override
                void visitDeclarationExpression(DeclarationExpression de) {
                    for (VariableExpression v : declaredTargets(de)) {
                        if (isBooleanType(v.originType ?: v.type)) out.add(v.name)
                    }
                    super.visitDeclarationExpression(de)
                }
            })
        } catch (Throwable ignored) {}
        out
    }

    /**
     * Phase 28 — enum classes visible from {@code node}'s module, mapped from simple name (and
     * inner-class-stripped name) to value count. The Encoder uses this to fold
     * {@code Color.values().length} to the literal constant count in re-parsed contracts where the
     * receiver appears as an unresolved {@link VariableExpression}. Post-resolution body code has
     * the {@link ClassExpression} receiver and works without this map.
     */
    private static Map<String, Integer> collectEnumDomainSizes(MethodNode node) {
        // The derivation lives in ContractNormalizer (it is also the values().length fold scope).
        ContractNormalizer.enumDomainSizes(node.declaringClass)
    }

    /** True for non-Int scalar types we model under an uninterpreted Z3 sort: String, enums. */
    /** Phase 113 — tuple-typed locals declared in the (clean) body: name → its {@code TupleN} type. Used to
     *  recognise `Tuple2 r = callee(...)` so the local's slots can be bound to the callee's @Ensures. */
    private static Map<String, ClassNode> collectTupleTypes(MethodNode node) {
        Map<String, ClassNode> out = new LinkedHashMap<String, ClassNode>()
        Statement cleanBody = (Statement) node.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (cleanBody == null) cleanBody = node.code
        if (cleanBody != null) try {
            cleanBody.visit(new ClassCodeVisitorSupport() {
                protected SourceUnit getSourceUnit() { null }
                @Override void visitClosureExpression(ClosureExpression ce) { }
                @Override void visitDeclarationExpression(DeclarationExpression de) {
                    for (VariableExpression v : declaredTargets(de)) {
                        ClassNode t = v.originType ?: v.type
                        if (t != null && t.nameWithoutPackage != null && t.nameWithoutPackage.matches('Tuple\\d+')) {
                            out.put(v.name, t)
                        }
                    }
                    super.visitDeclarationExpression(de)
                }
            })
        } catch (Throwable ignored) {}
        out
    }

    private static boolean isNonIntScalar(ClassNode t) {
        if (t == null) return false
        if (t.isArray() || isSetType(t) || isMapType(t) || isListType(t)) return false
        if (isIntElement(t)) return false
        if (t.name == 'java.lang.String') return true
        try {
            if (t.isEnum()) return true
            if (t.superClass != null && t.superClass.name == 'java.lang.Enum') return true
        } catch (Throwable ignored) {}
        false
    }

    /** True if {@code t} is (or implements) {@code java.util.List}. */
    private static boolean isListType(ClassNode t) {
        if (t == null) return false
        try {
            return t.name == 'java.util.List' || t.implementsInterface(ClassHelper.make(List))
        } catch (Throwable ignored) {
            return false
        }
    }

    /** True if {@code t} is (or implements) {@code java.util.Set}. */
    private static boolean isSetType(ClassNode t) {
        if (t == null) return false
        try {
            return t.name == 'java.util.Set' || t.implementsInterface(ClassHelper.make(Set))
        } catch (Throwable ignored) {
            return false
        }
    }

    /** True if {@code t} is (or implements) {@code java.util.Map}. */
    private static boolean isMapType(ClassNode t) {
        if (t == null) return false
        try {
            return t.name == 'java.util.Map' || t.implementsInterface(ClassHelper.make(Map))
        } catch (Throwable ignored) {
            return false
        }
    }

    /** The accessor the developer wrote for {@code recv}'s size; defaults to {@code .size()}. */
    private String sizeAccessor(String recv) {
        sizeAccessors.getOrDefault(recv, '.size()')
    }

    /** VERIFY_REFUTATION — append a runnable repro (the reconstructed failing call as a test) to a refutation
     *  diagnostic, in the requested style. No-op (diagnostic unchanged) unless the env flag is set and a failing
     *  call was reconstructed. {@code exception} is the runtime exception the obligation throws, or null for a
     *  verify-only one (overflow). A static method gives a fully-runnable call; an instance method shows a
     *  best-effort {@code new C(…)} receiver (its field values are in the printed counterexample). */
    private String withRepro(String diag, CheckResult r, String exception) {
        // null / 'message' → the default bare `fails on:` line (rendered by appendModel); only the richer
        // formats (assert/junit/spock) render a self-checking test here.
        String fmt = Reporter.REFUTATION_FORMAT
        if (fmt == null || fmt == 'message' || r?.failingCall == null || currentMethod == null) return diag
        String cls = currentMethod.declaringClass?.nameWithoutPackage ?: 'C'
        String invocation = currentMethod.isStatic()
            ? "${cls}.${r.failingCall}".toString()
            : "new ${cls}(/* see counterexample */).${r.failingCall}".toString()
        diag + '\n' + Reporter.formatRepro(invocation, exception, currentMethod.name + 'Fails')
    }

    /**
     * Prepare a {@link CheckResult} for reporting (Phase 9): reconstruct a runnable failing call
     * from the raw model ({@link #buildFailingCall}), then render the displayed counterexample in the
     * programmer's vocabulary — the internal {@code recv.size} oracle key becomes
     * {@code recv.length}/{@code recv.size()}, and the internal {@code recv?null} flag is dropped
     * (it is surfaced through the failing call instead). Applied at the solver boundary so every
     * diagnostic shares the rendering; a no-op when there is no model.
     */
    private CheckResult shown(CheckResult r) {
        if (r == null) return r
        boolean intEmpty = r.counterexample == null || r.counterexample.isEmpty()
        boolean sortedEmpty = r.sortedCounterexample == null || r.sortedCounterexample.isEmpty()
        if (intEmpty && sortedEmpty) return r
        r.failingCall = buildFailingCall(r.counterexample, r.sortedCounterexample)
        // Phase 125 — array names whose Int-valued *elements* are meaningful to print: a parameter or instance
        // field reflects the actual input/entry state. A *local* array's model value is its arbitrary pre-state
        // (e.g. a loop-preservation check picks an unconstrained entry array), which would mislead — so those
        // element keys stay suppressed (the failing-call repro carries a param array's contents either way).
        Set<String> elementArrays = new HashSet<String>()
        if (currentMethod != null) {
            for (Parameter p : currentMethod.parameters) if (p.type?.isArray()) elementArrays.add(p.name)
            ClassNode dc = currentMethod.declaringClass
            if (dc != null) for (FieldNode fld : dc.fields) if (fld.type?.isArray()) elementArrays.add(fld.name)
        }
        Map<String, Long> display = new LinkedHashMap<String, Long>()
        r.counterexample.each { String k, Long v ->
            // internal keys: nullity flag, SSA version, synthetic temps (`$snap…` index snapshots, `$self`) —
            // surfaced via failingCall / the base (entry) variable, not shown raw.
            if (k.endsWith('?null') || k.contains('#') || k.startsWith('$')) return
            if (k.endsWith(']')) {
                int br = k.indexOf('[')
                String base = br >= 0 ? k.substring(0, br) : k
                if (elementArrays.contains(base)) display.put(k, v)   // param/field array element: meaningful
                return                                                // local/loop element: pre-state, suppress
            }
            // Phase 121 — a trait property is woven onto the implementing class as a `<Trait>__<field>` backing
            // field alongside the source-named property; show only the latter (the name the developer wrote).
            if (k.contains('__')) return
            // Phase 63 — the for-in desugar's synthetic index is internal; the loop variable carries
            // the source name, so suppress the index from the displayed counterexample.
            if (k.contains(ContractExpansionTransform.FOR_IN_INDEX)) return
            // Phase 67 — a decimal (BigDecimal/Double/Float) name's Int model value is a meaningless
            // shadow (its real value lives in the Real sort, which the Int model walk doesn't read), and
            // a decimal scalar has no size — so suppress both rather than print `price = 0, price.size() = 0`.
            if (currentDecimalNames.contains(k)) return
            if (k.endsWith('.size')) {
                String recv = k.substring(0, k.length() - '.size'.length())
                if (currentDecimalNames.contains(recv)) return
                display.put(recv + sizeAccessor(recv), v)
            } else {
                display.put(k, v)
            }
        }
        r.counterexample = display
        r
    }

    private static final List<String> INT_TYPE_NAMES = [
        'int', 'long', 'short', 'byte', 'char',
        'java.lang.Integer', 'java.lang.Long', 'java.lang.Short', 'java.lang.Byte', 'java.lang.Character']
    private static final List<String> BOOL_TYPE_NAMES = ['boolean', 'java.lang.Boolean']
    /** Component types whose modelled int contents can be rendered as element literals (slice 2). */
    private static final List<String> NUMERIC_COMPONENT_NAMES = [
        'int', 'long', 'short', 'byte', 'char', 'Integer', 'Long', 'Short', 'Byte', 'Character']

    /**
     * Reconstruct a runnable call to the current method that exhibits the failure, from the raw
     * counterexample — e.g. {@code g(new int[0], -1)}, {@code d(0, 0)}, {@code n(null)}. Best-effort:
     * scalars and a `null` receiver are exact; arrays/collections are rebuilt at the modelled *size*
     * (contents are not yet pinned — that is slice 2); an unmodelled object parameter falls back to
     * {@code null}. Returns null when there is no current method.
     */
    private String buildFailingCall(Map<String, Long> ce, Map<String, String> sortedCe) {
        if (currentMethod == null) return null
        List<String> args = new ArrayList<String>()
        for (Parameter p : currentMethod.parameters) {
            args.add(renderArg(p, ce, sortedCe))
        }
        "${currentMethod.name}(${args.join(', ')})"
    }

    /**
     * Render one parameter as a Groovy literal drawn from the counterexample. {@code sortedCe} holds
     * non-Int model values (Phase 27 step 9): a String parameter that the model pinned to {@code admin}
     * appears as {@code [name: "admin"]} and renders as the quoted Groovy literal; an enum parameter
     * pinned to {@code RED} renders as {@code <ClassSimpleName>.RED} (the inner-class binary prefix is
     * stripped, mirroring the enum sort name normalization in the encoder).
     */
    private static String renderArg(Parameter p, Map<String, Long> ce, Map<String, String> sortedCe) {
        ClassNode t = p.type
        boolean nulled = ce.get(p.name + '?null') == 1L
        if (t != null && t.isArray()) {
            if (nulled) return 'null'
            long n = sizeOf(p.name, ce)
            String comp = t.componentType.nameWithoutPackage
            List<Long> elems = pinnedElements(p.name, n, ce)
            // Render explicit contents only when the model committed to a non-zero element and the
            // component is numeric; otherwise `new T[n]` (which already *is* the all-zero array).
            if (elems != null && comp in NUMERIC_COMPONENT_NAMES && elems.any { it != 0L }) {
                return "[${elems.join(', ')}] as ${comp}[]"
            }
            return "new ${comp}[${n}]"
        }
        String tn = t?.name
        if (tn in INT_TYPE_NAMES) {
            Long v = ce.get(p.name)
            return String.valueOf(v != null ? v : 0L)
        }
        if (tn in BOOL_TYPE_NAMES) {
            Long v = ce.get(p.name)
            return (v != null && v == 1L) ? 'true' : 'false'
        }
        if (nulled) return 'null'
        if (tn == 'java.lang.String') {
            String modelVal = sortedCe?.get(p.name)
            return modelVal != null ? "\"${modelVal}\"".toString() : '""'
        }
        if (t != null && (t.isEnum() || isEnumLikeType(t))) {
            String modelVal = sortedCe?.get(p.name)
            return modelVal != null ? "${simpleEnumName(t)}.${modelVal}".toString() : 'null'
        }
        if (isSetType(t)) return nulled ? 'null' : '[] as Set'
        if (isMapType(t)) return nulled ? 'null' : '[:]'
        if (isCollectionType(t)) {
            long n = sizeOf(p.name, ce)
            List<Long> elems = pinnedElements(p.name, n, ce)
            if (elems != null && elems.any { it != 0L }) return "[${elems.join(', ')}]"
            return n == 0L ? '[]' : '[' + (['null'] * (int) n).join(', ') + ']'
        }
        return 'null'   // best effort for an arbitrary object type
    }

    /** Strip the inner-class binary prefix from an enum's nameWithoutPackage (mirrors Encoder.enumSortName). */
    private static String simpleEnumName(ClassNode t) {
        ContractNormalizer.simpleEnumName(t)
    }

    /** True if {@code t} appears to be an Enum subclass (mirrors Encoder.isEnumLikeType). */
    private static boolean isEnumLikeType(ClassNode t) {
        try {
            return t != null && t.superClass != null && t.superClass.name == 'java.lang.Enum'
        } catch (Throwable ignored) {
            return false
        }
    }

    private static long sizeOf(String name, Map<String, Long> ce) {
        Long sz = ce.get(name + '.size')
        (sz != null && sz > 0L) ? sz : 0L
    }

    /**
     * The contents the model committed to for {@code name}, as {@code name[0..n)}; missing elements
     * default to 0. Returns null when the model pinned no element of this receiver (so the caller
     * keeps the size-filled form).
     */
    private static List<Long> pinnedElements(String name, long n, Map<String, Long> ce) {
        if (n <= 0L) return null
        boolean any = false
        List<Long> out = new ArrayList<Long>()
        for (int k = 0; k < n; k++) {
            Long v = ce.get(name + '[' + k + ']')
            if (v != null) any = true
            out.add(v != null ? v : 0L)
        }
        any ? out : null
    }

    private static boolean isCollectionType(ClassNode t) {
        if (t == null) return false
        try {
            return t.name == 'java.util.Collection' || t.name == 'java.util.List' ||
                   t.implementsInterface(ClassHelper.make(Collection))
        } catch (Throwable ignored) {
            return false
        }
    }

    /**
     * Harvest, into {@link #sizeAccessors}, the size accessor the developer wrote for each receiver —
     * scanning the method's contracts (re-parsed) and its clean body for {@code recv.length},
     * {@code recv.size} and {@code recv.size()}. First spelling seen wins; receivers never written with
     * a size accessor keep the {@code .size()} default.
     */
    private void buildSizeAccessors(MethodNode node) {
        sizeAccessors = new HashMap<String, String>()
        for (String kind : ['requires', 'ensures', 'decreases']) {
            try {
                Expression c = contractAstFor(node, kind)
                if (c != null) c.visit(accessorScanner())
            } catch (Throwable ignored) {
            }
        }
        Statement body = (Statement) node.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (body == null) body = node.code
        if (body != null) {
            try {
                body.visit(accessorScanner())
            } catch (Throwable ignored) {
            }
        }
    }

    /** A visitor that records {@code recv.length} / {@code recv.size} / {@code recv.size()} spellings. */
    private ClassCodeVisitorSupport accessorScanner() {
        new ClassCodeVisitorSupport() {
            protected SourceUnit getSourceUnit() { null }
            @Override
            void visitPropertyExpression(PropertyExpression pe) {
                String r = receiverName(pe.objectExpression)
                if (r != null) {
                    if (pe.propertyAsString == 'length') sizeAccessors.putIfAbsent(r, '.length')
                    else if (pe.propertyAsString == 'size') sizeAccessors.putIfAbsent(r, '.size()')
                }
                super.visitPropertyExpression(pe)
            }
            @Override
            void visitMethodCallExpression(MethodCallExpression mce) {
                if (mce.methodAsString == 'size' && noArgs(mce)) {
                    String r = receiverName(mce.objectExpression)
                    if (r != null) sizeAccessors.putIfAbsent(r, '.size()')
                }
                super.visitMethodCallExpression(mce)
            }
        }
    }

    private static String receiverName(Expression e) {
        e instanceof VariableExpression ? ((VariableExpression) e).name : null
    }

    private static boolean noArgs(MethodCallExpression mce) {
        Expression a = mce.arguments
        if (a instanceof ArgumentListExpression) return ((ArgumentListExpression) a).expressions.isEmpty()
        if (a instanceof TupleExpression) return ((TupleExpression) a).expressions.isEmpty()
        true
    }

    /**
     * Phase 69 — array/list names whose {@code .sum()} a contract references (incl. {@code old.xs.sum()}).
     * Each store to such an array maintains its whole-array sum via the per-store sum law, so two
     * compensating stores (a transfer) leave the total unchanged — "no money is lost".
     */
    private static Set<String> sumArrayNames(Expression e) {
        Set<String> out = new HashSet<String>()
        if (e == null) return out
        try {
            e.visit(new ClassCodeVisitorSupport() {
                protected SourceUnit getSourceUnit() { null }
                @Override
                void visitMethodCallExpression(MethodCallExpression mce) {
                    if (mce.methodAsString == 'sum') {
                        Expression recv = mce.objectExpression
                        if (recv instanceof VariableExpression) out.add(((VariableExpression) recv).name)
                        else if (recv instanceof PropertyExpression) out.add(((PropertyExpression) recv).propertyAsString)
                    }
                    super.visitMethodCallExpression(mce)
                }
            })
        } catch (Throwable ignored) {
        }
        out
    }

    /** The single argument of each {@code .count(arg)} call — the values a postcondition counts. */
    private static List<Expression> countValueArgs(Expression e) {
        List<Expression> out = new ArrayList<Expression>()
        if (e == null) return out
        try {
            e.visit(new ClassCodeVisitorSupport() {
                protected SourceUnit getSourceUnit() { null }
                @Override
                void visitMethodCallExpression(MethodCallExpression mce) {
                    Expression a = mce.arguments
                    if (mce.methodAsString == 'count' && a instanceof ArgumentListExpression &&
                        ((ArgumentListExpression) a).expressions.size() == 1) {
                        out.add(((ArgumentListExpression) a).expressions.get(0))
                    }
                    super.visitMethodCallExpression(mce)
                }
            })
        } catch (Throwable ignored) {
        }
        out
    }

    /** The {@code k} (second) argument of each {@code Sets.boundedCount(s, k)} call — the bounds the bcount law tracks. */
    private static List<Expression> bcountKArgs(Expression e) {
        List<Expression> out = new ArrayList<Expression>()
        if (e == null) return out
        try {
            e.visit(new ClassCodeVisitorSupport() {
                protected SourceUnit getSourceUnit() { null }
                @Override
                void visitMethodCallExpression(MethodCallExpression mce) {
                    Expression recv = mce.objectExpression
                    boolean isSets = (recv instanceof VariableExpression && ((VariableExpression) recv).name == 'Sets') ||
                                     (recv instanceof PropertyExpression && ((PropertyExpression) recv).propertyAsString == 'Sets')
                    Expression a = mce.arguments
                    if (isSets && mce.methodAsString == 'boundedCount' && a instanceof ArgumentListExpression &&
                        ((ArgumentListExpression) a).expressions.size() == 2) {
                        out.add(((ArgumentListExpression) a).expressions.get(1))
                    }
                    super.visitMethodCallExpression(mce)
                }
            })
        } catch (Throwable ignored) {
        }
        out
    }

    /** The locations a method declares it modifies via {@code @Modifies}; null when it has none. */
    private Set<String> modifiedNames(MethodNode node) {
        Expression e = contractAstFor(node, 'modifies')
        if (e == null) return null
        Set<String> out = new HashSet<String>()
        addModifiedLocation(e, out)
        out
    }

    private static void addModifiedLocation(Expression e, Set<String> out) {
        if (e instanceof ListExpression) {
            for (Expression x : ((ListExpression) e).expressions) addModifiedLocation(x, out)
        } else if (e instanceof VariableExpression) {
            out.add(((VariableExpression) e).name)
        } else if (e instanceof PropertyExpression) {
            Expression obj = ((PropertyExpression) e).objectExpression
            if (obj instanceof VariableExpression && ((VariableExpression) obj).name == 'this') {
                out.add(((PropertyExpression) e).propertyAsString)
            }
        }
    }

    /**
     * Frame-check (Phase 13): a method that declares {@code @Modifies} must write only the
     * caller-visible locations it lists — fields and array parameters/fields (a store {@code a[i]=v}
     * or a field write {@code this.x=v} / bare {@code x=v}). Local writes don't count. {@code @Modifies({})}
     * means *nothing* is modified (pure). A write outside the declared set is a loud error.
     */
    private void frameCheck(MethodNode node) {
        Set<String> declared = modifiedNames(node)
        if (declared == null) return
        Statement body = (Statement) node.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (body == null) body = node.code
        if (body == null) return
        Set<String> visible = new HashSet<String>()
        if (node.declaringClass != null) node.declaringClass.fields.each { visible.add(it.name) }
        node.parameters.each { Parameter p -> visible.add(p.name) }
        List<String> offenders = new ArrayList<String>()
        try {
            body.visit(new ClassCodeVisitorSupport() {
                protected SourceUnit getSourceUnit() { null }
                @Override
                void visitBinaryExpression(BinaryExpression be) {
                    if (be.operation.type == Types.ASSIGN) {
                        String w = writtenLocation(be.leftExpression)
                        // Caller-visible (a field or array param/field), and not declared → frame violation.
                        if (w != null && visible.contains(w) && !declared.contains(w)) {
                            offenders.add(w)
                        }
                    }
                    super.visitBinaryExpression(be)
                }
                @Override
                void visitMethodCallExpression(MethodCallExpression mce) {
                    // A set mutation `s.add(x)`/`s.remove(x)` or a map `m.put(k,v)` writes the collection —
                    // frame-checked like an array store, since it is not an assignment LHS.
                    String mm = mce.methodAsString
                    if (mce.objectExpression instanceof VariableExpression) {
                        String w = ((VariableExpression) mce.objectExpression).name
                        boolean setWrite = (mm == 'add' || mm == 'remove') && currentSetElementTypes.containsKey(w)
                        boolean mapWrite = (mm == 'put') && currentMapTypes.containsKey(w)
                        if ((setWrite || mapWrite) && visible.contains(w) && !declared.contains(w)) {
                            offenders.add(w)
                        }
                    }
                    super.visitMethodCallExpression(mce)
                }
            })
        } catch (Throwable ignored) {
        }
        for (String loc : offenders) {
            addStaticTypeError(Reporter.formatModifiesViolation(node.name, loc, declared), node)
        }
    }

    /** The caller-visible location written by an assignment LHS, or null (e.g. a local). */
    private static String writtenLocation(Expression lhs) {
        if (lhs instanceof BinaryExpression &&
            ((BinaryExpression) lhs).operation.type == Types.LEFT_SQUARE_BRACKET &&
            ((BinaryExpression) lhs).leftExpression instanceof VariableExpression) {
            return ((VariableExpression) ((BinaryExpression) lhs).leftExpression).name   // a[i] = v -> array a
        }
        if (lhs instanceof PropertyExpression) {
            Expression obj = ((PropertyExpression) lhs).objectExpression
            if (obj instanceof VariableExpression && ((VariableExpression) obj).name == 'this') {
                return ((PropertyExpression) lhs).propertyAsString   // this.x = v -> field x
            }
        }
        if (lhs instanceof VariableExpression) return ((VariableExpression) lhs).name   // x = v (field or local)
        null
    }

    /** Field names referenced via {@code old.field} in a postcondition (groovy-contracts' old map). */
    private static Set<String> oldFieldNames(Expression e) {
        Set<String> names = new HashSet<String>()
        if (e == null) return names
        try {
            e.visit(new ClassCodeVisitorSupport() {
                protected SourceUnit getSourceUnit() { null }
                @Override
                void visitPropertyExpression(PropertyExpression pe) {
                    if (Encoder.isOldReceiver(pe.objectExpression)) names.add(pe.propertyAsString)
                    super.visitPropertyExpression(pe)
                }
            })
        } catch (Throwable ignored) {
        }
        names
    }

    VerifyChecker(StaticTypeCheckingVisitor visitor) {
        super(visitor)
    }

    // ── Phase 209 — pack-resolved dynamic references (the STC companion half of an encoding pack) ──
    // A pack may bless an unresolved property/method it can also faithfully model (e.g. a statically
    // visible metaClass registration). Everything not claimed by a pack stays a compile error, exactly
    // as @TypeChecked demands — this is a narrow, evidence-backed gate, not a dynamic-Groovy on-switch.

    @Override
    boolean handleUnresolvedProperty(PropertyExpression pexp) {
        ClassNode rt = getType(pexp.objectExpression)
        ClassNode enclosing = typeCheckingVisitor.typeCheckingContext.enclosingClassNode
        for (EncodingPack pk : PackRegistry.packs()) {
            ClassNode stored = pk.resolveDynamicProperty(rt, pexp, enclosing)
            if (stored != null) {
                storeType(pexp, stored)
                return true
            }
        }
        return false
    }

    @Override
    List<MethodNode> handleMissingMethod(ClassNode receiver, String name, ArgumentListExpression argList,
                                         ClassNode[] argTypes, MethodCall call) {
        ClassNode enclosing = typeCheckingVisitor.typeCheckingContext.enclosingClassNode
        def ec = typeCheckingVisitor.typeCheckingContext.getEnclosingClosure()
        ClosureExpression closure = ec != null ? ec.closureExpression : null
        for (EncodingPack pk : PackRegistry.packs()) {
            MethodNode mn = pk.resolveDynamicMethod(receiver, name, argTypes, enclosing, closure)
            if (mn != null) return [mn]
        }
        return Collections.<MethodNode> emptyList()
    }

    @Override
    void setup() {
        // Per-check solver budget: 2s default, overridable via -Dverify.z3.timeoutMs / VERIFY_Z3_TIMEOUT_MS.
        // Refute-direction VCs (model search) are hardware-speed sensitive — CI runners need more headroom
        // than a dev laptop for the same crisp refutation.
        String tmo = System.getProperty('verify.z3.timeoutMs', System.getenv('VERIFY_Z3_TIMEOUT_MS') ?: '2000')
        backend = new Z3Backend(tmo.isInteger() ? tmo.toInteger() : 2000)
    }

    @Override
    boolean beforeVisitMethod(MethodNode node) {
        currentFacts = new PathFacts()
        currentMethod = node
        currentEvaluator = node.declaringClass != null ? new PureEvaluator(node.declaringClass) : null
        currentSetElementTypes = collectSetElementTypes(node)
        currentMapTypes = collectMapTypes(node)
        currentNestedSetValueTypes = collectNestedSetValueTypes(node)
        currentNonNullElementContainers = collectNonNullElementContainers(node)
        currentListNames = collectListNames(node)
        currentListElementTypes = collectListElementTypes(node)
        currentScalarTypes = collectScalarTypes(node)
        currentAtomicNames = collectAtomicNames(node)
        currentTupleTypes = collectTupleTypes(node)
        currentCombiners = collectCombiners(node)
        currentCarrierTypes = collectCarrierTypes(node)
        currentFunctionReturnTypes = collectFunctionReturnTypes(node)
        currentBiFunctionReturnTypes = ContractNormalizer.biFunctionReturnTypes(node)
        currentDecimalNames = collectDecimalNames(node)
        currentFpNames = collectFpNames(node)
        currentBooleanLocals = collectBooleanLocals(node)
        currentEnumDomainSizes = collectEnumDomainSizes(node)
        currentIsConstructor = (node instanceof ConstructorNode)
        currentOverflowChecking = methodOrClassHasAnnotation(node, 'CheckOverflow')
        currentObjectParams = collectObjectParams(node)
        currentTupleParams = collectTupleParams(node)
        currentCatchCoverage = collectCatchCoverage(node)
        buildSizeAccessors(node)
        // Phase 15a — pre-filter class invariants once per method. Static methods skip (no `this`).
        // Pre-filtering here means a single skip diagnostic per outside-fragment clause, even if
        // the method has many implicit-obligation sites, multiple paths, etc.
        List<Expression> rawInvs = (!node.isStatic() && node.declaringClass != null) ?
            classInvariantTexts(node.declaringClass) : Collections.<Expression> emptyList()
        currentClassInvariants = filterEncodableInvariants(rawInvs, node)
        if (node.code != null) {
            try {
                node.code.visit(currentFacts)
            } catch (Throwable t) {
                // Defensive: if precomputation fails, fall back to
                // "no facts known". The spike prefers continuing
                // verification over hard-failing the build.
                currentFacts = new PathFacts()
            }
        }
        false  // false = also run the default type-check visit
    }

    /**
     * Phase 15b — Groovy's StaticTypeCheckingVisitor doesn't fire the {@link #beforeVisitMethod} /
     * {@link #afterVisitMethod} hooks for constructors. Sweep them here, after all methods on the
     * class have been visited, manually invoking the same setup + verify path so a constructor
     * gets its class invariant proved at exit (with Int-field defaults from {@link #initFieldDefaults}
     * giving an empty-body constructor the same "JVM-default 0" entry state real code sees).
     */
    @Override
    void afterVisitClass(ClassNode classNode) {
        if (classNode == null) return
        verifyTraitDefaultMethods(classNode)
        // Phase 136 — a @Monadic carrier asserts the monad/functor laws; discharge the Tier-1 identity laws it
        // claims, derived from the annotation (à la @Reducer). Best-effort.
        try { verifyMonadicLaws(classNode) } catch (Throwable ignored) { }
        // Phase L1 (rely/guarantee) — discharge the well-formedness/compatibility lemmas of any @Rely/@Guarantee
        // conditions the class declares (reflexive/transitive relies, reflexive guarantees, G_i ⟹ R_j). Best-effort.
        try { verifyRelyGuarantee(classNode) } catch (Throwable ignored) { }
        for (ConstructorNode ctor : classNode.declaredConstructors) {
            try {
                beforeVisitMethod(ctor)
                afterVisitMethod(ctor)
            } catch (Throwable ignored) {
                // Best-effort: a constructor processing failure shouldn't break the class's other diagnostics.
            }
        }
    }

    @Override
    void afterVisitMethod(MethodNode node) {
        // Phase 121 — trait machinery: a trait's default method is woven into a static helper method on a
        // `…$Trait$Helper` class (a synthetic `$self` receiver as first parameter) and a delegating bridge on
        // each implementing class, both generated *after* the CONVERSION snapshot — so the verifier would see
        // a post-weave `try/catch` body (a spurious "skipped" error) and a phantom `$self != null` obligation.
        // Skip these synthetic methods quietly: trait code then compiles cleanly, and the trait's contribution
        // we *do* verify — its class `@Invariant`, enforced on each implementer's own methods — flows through
        // the interface walk in walkClassInvariants. (Verifying trait default-method *contracts* through the
        // weaving is a separate, larger slice.)
        if (isTraitMachineryMethod(node)) return
        try {
            Statement body = (Statement) node.getNodeMetaData(
                ContractExpansionTransform.ORIGINAL_BODY_KEY)
            if (body == null) body = node.code

            // Phase 118 — desugar Groovy's dataflow constructs into plain single-assignment code: a
            // `DataflowVariable` is a write-once local, so `x << v` is `x = v`, `await(x)`/`x.get()`/`x.val`
            // is a read of `x`, and `async { … }` is transparent (sound — single-assignment makes the result
            // order-independent, so running the binds in source order gives the deterministic value). The
            // rewrite makes the network ordinary SSA; the determinacy guarantee is the half we rely on.
            // No-op (returns the same body) unless the method actually uses these constructs.
            Statement desugared = desugarDataflow(body)
            if (!desugared.is(body)) {
                node.putNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY, desugared)
                body = desugared
            }

            // Phase 119 — desugar an async-channel pipeline into the composed per-element transform. FIFO
            // delivery means the i-th value received is the i-th value sent, run through the pipeline's pure
            // stages — so for a representative element, `src.send(x)` is `src = x`, `ch.map { f }` beta-reduces
            // to `f(ch)`, and receiving one element (`ch.first()`) is a read of `ch`. The pipeline collapses to
            // function composition (the combiner trick); FIFO ordering is the structural half we assume.
            // No-op unless the method actually builds a channel pipeline.
            Statement deChan = desugarChannels(body)
            if (!deChan.is(body)) {
                node.putNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY, deChan)
                body = deChan
            }

            List<LoopSite> sites
            try {
                sites = findLoopSites(body)
            } catch (UnsupportedConstructException e) {
                addStaticTypeError(Reporter.formatLoopSkipped(node.name, e.message), node)
                return
            }

            // Phase 71 — flag a self-contradictory @Requires before anything else: under it, every
            // @Ensures verifies trivially (the silent vacuous pass the project warns about most).
            checkPreconditionSatisfiable(node)

            // Phase 212 — shouldFail claims: each GroovyAssert.shouldFail(E) { … } in the body is a
            // GROUND exceptional claim ("this closed call throws E") — verified or refuted here, the
            // exceptional analogue of closed-call evaluation. Contained: never fails the compile flow.
            try {
                verifyShouldFailClaims(node, body)
            } catch (Throwable ignored) {
            }

            // Phase 213 — @ThrowsIf: the UNIVERSAL exceptional contract (throws exactly when the
            // condition holds). Both directions discharged per path; contained like the passes above.
            try {
                verifyThrowsIf(node, body)
            } catch (Throwable ignored) {
            }

            // Implicit safety obligations (array bounds, division by zero, null
            // dereference) fire on every method, contract or not. For an
            // annotated loop they are discharged *with the invariant in scope*
            // (Phase 5b); otherwise via the per-method value-flow/havoc pass
            // (Phase 5a). Best-effort: never fail the build over them.
            // Install the rely-step framing handler so a loop body under @UnderRely (a contracted call inside the
            // loop) is modelled with the environment running per iteration, exactly as the straight-line value-flow
            // pass frames such calls. Restored after, so a method without loops/rely-steps is unaffected.
            LoopEncoder.LoopCallHandler prevHandler = LoopEncoder.callHandler.get()
            LoopEncoder.callHandler.set(relyCallHandler(node))
            try {
                try {
                    if (!sites.isEmpty()) verifyLoopObligations(node, sites)
                    else verifyImplicitObligations(node)
                } catch (Throwable ignored) {
                }

                try {
                    // Phase 207 — SEQUENTIAL annotated loops: each site gets its own establishment /
                    // preservation / progress (earlier loops summarised in its prefix replay); only the
                    // LAST site carries the @Ensures / early-exit / post-loop-use checks (its suffix is
                    // the loop-free tail).
                    if (!sites.isEmpty()) {
                        for (int si = 0; si < sites.size(); si++) {
                            verifyLoop(node, sites.get(si), si == sites.size() - 1)
                        }
                    } else {
                        verifyPostcondition(node)
                    }
                } catch (Throwable t) {
                    // An unexpected encoder error (e.g. a value shape the fragment doesn't yet model end-to-end)
                    // must degrade to a loud skip, never crash the compile — the "skip outside the fragment,
                    // don't throw" contract. Anchored on a positioned proxy at the method's location (the
                    // Phase 94 convention; the historical MN-anchored drop no longer reproduces on alpha-2,
                    // the proxy is retained as insurance).
                    ConstantExpression at = new ConstantExpression(node.name)
                    at.setSourcePosition((ASTNode) node)
                    addStaticTypeError(Reporter.formatPostconditionSkipped(node.name, 'internal: ' + t.message), (ASTNode) at)
                }
            } finally {
                LoopEncoder.callHandler.set(prevHandler)
            }

            // Phase L1 (information flow): if the method declares an output security classification (@Label),
            // discharge the noninterference obligation — no labelled source above that classification may flow
            // to the result. Best-effort, like the other discharges. Straight-line returns only for now; an
            // unlabelled/unsupported source skips loudly inside.
            try {
                verifyNoLeak(node)
            } catch (Throwable ignored) {
            }

            // EncodingPack checker passes (Phase 190) — each pack's per-method AST analysis (e.g. UnitsPack's
            // C₀ kind-vector check of `as Quantity<K>` casts). Best-effort, contained per pack: a crashing
            // pass contributes nothing rather than failing the compile (the pre-migration posture kept).
            for (EncodingPack pk : PackRegistry.packs()) {
                try {
                    pk.checkMethod(this, node)
                } catch (Throwable ignored) {
                }
            }

            // Phase 7 (induction): prove the @Decreases measure decreases at each recursive call,
            // justifying the inductive hypothesis used in verifyPostcondition. No-op unless the
            // method carries a method-level @Decreases. Best-effort.
            try {
                verifyTermination(node)
            } catch (Throwable ignored) {
            }

            // Phase 13 (frame): a method with @Modifies must write only what it declares. Best-effort.
            try {
                frameCheck(node)
            } catch (Throwable ignored) {
            }

            // Phase 120 (behavioral subtyping / Liskov): if this method overrides a contracted parent method
            // and redeclares its own contract, prove the override is substitutable — its @Requires is weaker
            // (pre_parent ⟹ pre_child) and its @Ensures is stronger ((pre_parent ∧ post_child) ⟹ post_parent).
            // Pure contract-implication checks, independent of the body. Best-effort.
            try {
                verifyBehavioralSubtyping(node)
            } catch (Throwable ignored) {
            }

            // Phase 130 (monoid laws): if this method is a @Reducer/@Associative combiner, discharge the
            // associativity (and, for @Reducer with a declared zero, identity) laws the annotation *asserts*.
            // Best-effort. Runs last: it recursively visits synthesized lemma methods, which reset the per-method
            // `current*` state — fine, since nothing after this needs the combiner's context before the finally.
            try {
                verifyReducerLaws(node)
            } catch (Throwable ignored) {
            }
        } finally {
            currentFacts = null
            currentMethod = null
            currentEvaluator = null
            sizeAccessors = [:]
            currentClassInvariants = Collections.<Expression> emptyList()
            currentIsConstructor = false
            currentOverflowChecking = false
            currentAssertsTrusted = false
            currentObjectParams = new LinkedHashMap<String, ClassNode>()
            currentTupleParams = new LinkedHashMap<String, ClassNode>()
            currentSetElementTypes = new HashMap<String, ClassNode>()
            currentMapTypes = new HashMap<String, ClassNode[]>()
            currentNestedSetValueTypes = new HashMap<String, ClassNode>()
            currentNonNullElementContainers = new HashSet<String>()
            currentListNames = new HashSet<String>()
            currentListElementTypes = new HashMap<String, ClassNode>()
            currentScalarTypes = new HashMap<String, ClassNode>()
            currentAtomicNames = new HashSet<String>()
            currentTupleTypes = new HashMap<String, ClassNode>()
            currentCombiners = new HashMap<String, Object[]>()
            currentCarrierTypes = new HashMap<String, ClassNode>()
            currentFunctionReturnTypes = new HashMap<String, ClassNode>()
            currentDecimalNames = new HashSet<String>()
            currentFpNames = new HashMap<String, Boolean>()
            currentBooleanLocals = new HashSet<String>()
            currentEnumDomainSizes = new HashMap<String, Integer>()
        }
    }

    // ---- Phase 1: implicit safety obligations ----

    /**
     * Discharge the implicit preconditions that every program carries: an array
     * index is in bounds, a divisor is non-zero, a dereferenced receiver is
     * non-null. No annotation surface — these fire automatically on the relevant
     * AST shapes inside the method body. Each obligation is checked exactly like a
     * call-site precondition: assume the method's own {@code @Requires} and the
     * enclosing path facts, assert the negation of the obligation, and ask Z3
     * whether that is satisfiable (a model is a counterexample).
     *
     * The analysis is path-sensitive (it honours enclosing {@code if}s) but not
     * value-flow-sensitive: like the call-site checker, it does not track local
     * assignments, so the canonical demos are guard-based. Bodies are read from
     * the clean CONVERSION snapshot so groovy-contracts' injected asserts are not
     * mistaken for user dereferences.
     */
    /**
     * Phase 71 — report a contradictory {@code @Requires}. The project's stated worst case is a silent
     * *vacuous* pass: a "proof" that holds only because its assumptions can never all be true. If the
     * (soundly encoded) precondition together with any class invariants is UNSAT, every {@code @Ensures}
     * verifies trivially, so the contract proves nothing. Conservative: fires only when the precondition
     * fully translates and Z3 returns a definite UNSAT — UNKNOWN/SAT stay silent — and is best-effort, so
     * it can never break the build by itself.
     */
    private void checkPreconditionSatisfiable(MethodNode node) {
        boolean hasReq = findRequires(node) != null
        // A method with no @Requires but with Bean Validation constraints can still be vacuous (e.g. @Positive
        // @Negative on one parameter) — include those so the contradiction isn't a silent vacuous pass.
        if (!hasReq && !hasValidationConstraints(node)) return
        Expression reqAst = hasReq ? contractAstFor(node, 'requires') : null
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            if (reqAst != null) {
                Object pre = enc.translateBool(reqAst)
                if (pre == null) return   // didn't fully translate → can't judge soundly; stay silent
                s.assertExpr(pre)
                captureExplain(s, enc, reqAst, pre)
            }
            assumeClassInvariants(s, enc)
            assumeValidationConstraints(s, enc)   // the constraints participate in the satisfiability check too
            CheckResult r = s.check()   // VERIFIED == UNSATISFIABLE → the precondition can never hold
            if (r.status == CheckResult.Status.VERIFIED) {
                addStaticTypeError(Reporter.formatVacuousPrecondition(node.name, reqAst != null ? reqAst.text : null), node)
            }
        } catch (Throwable ignored) {
        } finally { try { s.close() } catch (Throwable ignored) {} }
    }

    private void verifyImplicitObligations(MethodNode node) {
        Statement body = (Statement) node.getNodeMetaData(
            ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (body == null) body = node.code
        if (body == null) return

        Expression reqAst = findRequires(node) != null ? contractAstFor(node, 'requires') : null

        // Phase 5a — value-flow. When the whole body is in the value-flow
        // fragment (straight-line + if/else + single-assignment locals, no
        // loops), discharge each obligation under the symbolic store that
        // *reaches* it, so safety implied by a preceding assignment — not only
        // by a guard — is provable. Anything outside that fragment (a loop, a
        // re-assignment, an unsupported statement) throws, and we fall back to
        // the path-fact-only havoc pass: sound, but value-flow-blind.
        currentAssertsTrusted = false
        try {
            List<VfObligation> sites = new ArrayList<VfObligation>()
            collectVfObligations(topStatements(body),
                new ArrayList<Object>(),
                new HashSet<String>(), sites)
            for (VfObligation v : sites) dischargeVfObligation(node, v, reqAst)
            currentAssertsTrusted = true   // every assert was discharged here → safe to assume them in the postcondition
        } catch (UnsupportedConstructException ignored) {
            // Value-flow bailed (a re-assignment — including the `i = i + 1` an expression-position `a[i++]`
            // expands to — or an unsupported shape). Re-discharge through dischargeRegion, which threads the
            // preceding straight-line statements (SSA), so an `a[i]` bounds check sees the reaching binding /
            // bumped index. Falls back to the value-flow-blind pass only if that itself throws.
            try {
                dischargeRegion(topStatements(body), reqAst, Collections.<Expression> emptyList(), null)
            } catch (Throwable t) {
                dischargeObligationsHavoc(node, body, reqAst)
            }
            // The fallback passes don't discharge user `assert`s, so any in this body go unchecked here — say so
            // loudly rather than skip silently (and they are not assumed in the postcondition: trusted stays false).
            for (AssertStatement as : collectAssertStatements(body)) {
                addStaticTypeError(Reporter.formatImplicitSkipped("assertion",
                    "the method body is outside the value-flow fragment (a re-assignment or loop)"), as)
            }
        }
    }

    /** True if {@code e} mentions any parameter of {@code m} by name — the "this assert is a precondition" smell. */
    private static boolean referencesParameter(Expression e, MethodNode m) {
        if (e == null || m == null || m.parameters.length == 0) return false
        Set<String> params = new HashSet<String>()
        for (Parameter p : m.parameters) params.add(p.name)
        boolean[] hit = [false]
        try {
            e.visit(new CodeVisitorSupport() {
                @Override void visitVariableExpression(VariableExpression v) { if (params.contains(v.name)) hit[0] = true }
            })
        } catch (Throwable ignored) { }
        hit[0]
    }

    /** True if {@code name} is a parameter or instance field of the current method — i.e. in scope at entry, so a
     *  {@code @Requires} may mention it. */
    private boolean isEntryName(String name) {
        if (currentMethod == null) return false
        for (Parameter p : currentMethod.parameters) if (p.name == name) return true
        ClassNode dc = currentMethod.declaringClass
        if (dc != null) for (FieldNode f : dc.fields) if (f.name == name) return true
        false
    }

    /** True if every variable in {@code e} names a parameter or instance field — so {@code e} is expressible as a
     *  precondition. VERIFY_SUGGEST won't propose a {@code @Requires} that references a local / loop variable. */
    private boolean referencesOnlyEntryState(Expression e) {
        if (e == null || currentMethod == null) return false
        Set<String> allowed = new HashSet<String>()
        for (Parameter p : currentMethod.parameters) allowed.add(p.name)
        ClassNode dc = currentMethod.declaringClass
        if (dc != null) for (FieldNode f : dc.fields) allowed.add(f.name)
        boolean[] ok = [true]
        try {
            e.visit(new CodeVisitorSupport() {
                @Override void visitVariableExpression(VariableExpression v) {
                    if (v.name != 'this' && !allowed.contains(v.name)) ok[0] = false
                }
            })
        } catch (Throwable ignored) { return false }
        ok[0]
    }

    /** VERIFY_SUGGEST (Tier 1) — the template {@code @Requires} that discharges a refuted *implicit* obligation:
     *  the positive form of the violated check (bounds / non-zero / non-null / in-range). Returns the contract
     *  text, or null when the flag is off, the site isn't a templatable kind, or the guard would reference a
     *  local / loop variable (not expressible as a precondition). A human-reviewed suggestion, never auto-applied. */
    private String suggestedGuard(Object site) {
        if (Reporter.SUGGEST_FORMAT == null) return null
        if (site instanceof IndexSite) {
            IndexSite ix = (IndexSite) site
            if (!isEntryName(ix.receiver) || !referencesOnlyEntryState(ix.index)) return null
            String i = ix.index.text
            return "0 <= ${i} && ${i} < ${ix.receiver}${sizeAccessor(ix.receiver)}".toString()
        }
        if (site instanceof DivideSite) {
            DivideSite dv = (DivideSite) site
            if (!referencesOnlyEntryState(dv.divisor)) return null
            return (dv.requirePositive ? "${dv.divisor.text} > 0" : "${dv.divisor.text} != 0").toString()
        }
        if (site instanceof DerefSite) {
            DerefSite df = (DerefSite) site
            if (df.indexExpr == null) return isEntryName(df.receiver) ? "${df.receiver} != null".toString() : null
            return (isEntryName(df.receiver) && referencesOnlyEntryState(df.indexExpr)) ?
                "${df.receiver}[${df.indexExpr.text}] != null".toString() : null
        }
        // No overflow template: the natural range-check guard (Integer.MIN_VALUE <= a+b <= Integer.MAX_VALUE)
        // is runtime-vacuous — groovy-contracts evaluates `a + b` with wrapping Groovy int arithmetic, so the
        // bound always holds. A sound overflow precondition depends on operand signs (no clean fill), so skip it.
        null
    }

    /** VERIFY_SUGGEST — append the suggested {@code @Requires} (if any) to a refutation diagnostic. No-op when the
     *  flag is off or the obligation isn't templatable / is out of precondition scope. */
    private String withSuggestion(String diag, Object site) {
        String guard = suggestedGuard(site)
        guard == null ? diag : diag + '\n' + Reporter.formatSuggestion(guard)
    }

    /** All {@code assert} statements lexically in {@code body} (best-effort; failures yield an empty list). */
    private static List<AssertStatement> collectAssertStatements(Statement body) {
        List<AssertStatement> out = new ArrayList<AssertStatement>()
        try {
            body.visit(new CodeVisitorSupport() {
                @Override void visitAssertStatement(AssertStatement s) { out.add(s); super.visitAssertStatement(s) }
            })
        } catch (Throwable ignored) { }
        out
    }

    /** The value-flow-blind fallback: assume @Requires + enclosing ifs only (pre-Phase-5 behaviour). */
    private void dischargeObligationsHavoc(MethodNode node, Statement body, Expression reqAst) {
        PathFacts pf = new PathFacts()
        try {
            body.visit(pf)
        } catch (Throwable t) {
            pf = new PathFacts()
        }
        ObligationCollector col = new ObligationCollector()
        col.overflowChecking = currentOverflowChecking
        try {
            body.visit(col)
        } catch (Throwable t) {
            return
        }
        for (IndexSite s : col.indexSites)  dischargeIndex(s, pf, reqAst)
        for (DivideSite s : col.divideSites) dischargeDivide(s, pf, reqAst)
        for (DerefSite s : col.derefSites)  dischargeDeref(s, pf, reqAst)
        for (OverflowSite s : col.overflowSites) dischargeOverflow(s, pf, reqAst)
        for (StringCharAtSite s : col.stringCharAtSites) dischargeStringCharAt(s, pf, reqAst)
        for (StringSubstringSite s : col.stringSubstringSites) dischargeStringSubstring(s, pf, reqAst)
        for (ParseSite s : col.parseSites) dischargeParse(s, pf, reqAst)
    }

    private void dischargeStringCharAt(StringCharAtSite site, PathFacts pf, Expression reqAst) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            assumeContext(s, enc, reqAst, site.node, pf)
            dischargeObligationUnder(s, enc, site)
        } finally {
            try { s.close() } catch (Throwable ignored) {}
        }
    }

    private void dischargeStringSubstring(StringSubstringSite site, PathFacts pf, Expression reqAst) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            assumeContext(s, enc, reqAst, site.node, pf)
            dischargeObligationUnder(s, enc, site)
        } finally {
            try { s.close() } catch (Throwable ignored) {}
        }
    }

    /**
     * An implicit obligation paired with the ordered steps that reach it. Steps are a heterogeneous
     * list of {@link Assign} / {@link Guard} / {@link LemmaCall} entries in source order — same
     * shape as {@code Path.steps} in the body-replay path. This ordering matters once
     * {@link LemmaCall} entries (Phase 42) join the list: a mutation may sit between an assign and
     * a downstream guard, and replaying the steps in source order keeps the size/contents oracles
     * consistent across the implicit-obligation pass and the body-replay pass.
     */
    @CompileStatic
    private static class VfObligation {
        Object site                 // IndexSite | DivideSite | DerefSite
        List<Object> steps          // Assign | FieldAssign | Guard | LemmaCall, in source order
    }

    /**
     * A bare scalar write to an Int-typed *field* or *parameter* (`tail = tail + 1`) — replayed as an SSA
     * *versioning* step, not a plain {@code name == rhs} binding. A field/param reuses its entry symbol, so a
     * binding would thread {@code tail == tail + 1} (self-contradictory) onto it — an UNSAT context that then
     * discharges every downstream obligation *vacuously and silently*. Versioning (evaluate the rhs against the
     * pre-write symbol, then rebind the name to a fresh symbol equal to it) keeps it sound, and lets a body that
     * bumps a shared counter discharge its real obligations. Non-Int field/param writes stay a loud skip.
     */
    @CompileStatic
    private static class FieldAssign {
        String name
        Expression rhs
        FieldAssign(String name, Expression rhs) { this.name = name; this.rhs = rhs }
    }

    /** Mints unique fresh symbols for SSA-versioned field/param writes ({@link FieldAssign}) at replay. */
    private int ssaCounter = 0

    /**
     * Walk the value-flow fragment, snapshotting for each implicit obligation
     * the guards and single-assignment bindings in effect at the point it is
     * evaluated. Forks at each {@code if} (the condition's own obligations are
     * evaluated before the branch); statements after an {@code if} continue with
     * the pre-{@code if} store, so a variable assigned only inside a branch is
     * havoc afterwards (sound — we never claim a merged value). Throws
     * {@link UnsupportedConstructException} on loops, re-assignment, or any
     * unsupported statement so the caller can fall back to the havoc pass.
     */
    private void collectVfObligations(List<Statement> stmts,
                                      List<Object> steps,
                                      Set<String> assigned, List<VfObligation> out) {
        // Hoist expression-position `++`/`--` so obligations are scanned on the rewritten access (`a[i]`);
        // the resulting `i = i+1` re-assignment throws this single-assignment pass out to the havoc pass
        // (which threads it via `preceding`), exactly as a plain `i = i + 1` already does.
        stmts = Encoder.expandIncDecStatements(stmts)
        for (Statement st : stmts) {
            if (st instanceof BlockStatement) {
                collectVfObligations(((BlockStatement) st).statements, steps, assigned, out)
                continue
            }
            if (st instanceof IfStatement) {
                IfStatement ifs = (IfStatement) st
                Expression cond = ifs.booleanExpression
                scanObligations(cond, steps, out)
                collectVfObligations(topStatements(ifs.ifBlock),
                    appendStep(steps, new Guard(cond, true)),
                    new HashSet<String>(assigned), out)
                Statement elseBlk = ifs.elseBlock
                boolean hasElse = elseBlk != null && !(elseBlk instanceof EmptyStatement)
                if (hasElse) {
                    collectVfObligations(topStatements(elseBlk),
                        appendStep(steps, new Guard(cond, false)),
                        new HashSet<String>(assigned), out)
                }
                // Early-exit narrowing. When an arm can't fall through, arriving here means the other arm
                // was taken, so the continuation carries that arm's guard — the `if (x == null) return`
                // idiom. Sound because the exiting arm's assignments are dead on this path (and the
                // single-assignment discipline forbids rebinding the names `cond` mentions), so `cond`
                // means at the continuation exactly what it meant at the `if`.
                boolean thenExits = alwaysExits(ifs.ifBlock)
                boolean elseExits = hasElse && alwaysExits(elseBlk)
                if (thenExits && elseExits) return           // neither arm falls through — the rest is dead
                if (thenExits || elseExits) {
                    // Rebind `steps` (rather than recursing) so the remaining statements in THIS list —
                    // and the in-place Assign/LemmaCall appends they make — build on the narrowed context.
                    steps = appendStep(steps, new Guard(cond, elseExits))
                }
                continue
            }
            if (st instanceof ReturnStatement) {
                scanObligations(((ReturnStatement) st).expression, steps, out)
                return   // rest of this list is dead on this path
            }
            if (st instanceof ThrowStatement) {
                // A throw ends the path exactly as a return does. Handled here (rather than falling through
                // to the "outside the fragment" bail) so a guard-throw body — `if (x == null) throw …` —
                // stays on the value-flow path and gets the narrowing above.
                scanObligations(((ThrowStatement) st).expression, steps, out)
                return   // rest of this list is dead on this path
            }
            if (st instanceof ExpressionStatement) {
                Expression e = ((ExpressionStatement) st).expression
                if (e instanceof DeclarationExpression) {
                    DeclarationExpression de = (DeclarationExpression) e
                    if (!(de.leftExpression instanceof VariableExpression)) {
                        throw new UnsupportedConstructException("multi-variable declaration")
                    }
                    String name = ((VariableExpression) de.leftExpression).name
                    scanObligations(de.rightExpression, steps, out)
                    if (!assigned.add(name)) throw new UnsupportedConstructException("re-assignment of '${name}'")
                    if (de.rightExpression != null) steps.add(new Assign(name, de.rightExpression))
                    continue
                }
                if (e instanceof BinaryExpression &&
                    ((BinaryExpression) e).operation.type == Types.ASSIGN) {
                    BinaryExpression be = (BinaryExpression) e
                    if (be.leftExpression instanceof VariableExpression) {
                        String name = ((VariableExpression) be.leftExpression).name
                        scanObligations(be.rightExpression, steps, out)
                        // A bare write to a *field* or *parameter* (not a fresh local) reuses that name's entry
                        // symbol. As a plain `name == rhs` binding it would thread the self-contradictory
                        // `tail == tail + 1` onto the entry value (UNSAT → every downstream obligation discharges
                        // vacuously). For an Int-typed field/param we emit a FieldAssign instead, replayed as an SSA
                        // *versioning* step (a fresh symbol for the post-write value) — sound, and it discharges the
                        // body's real obligations (the rely/guarantee shared counter `tail` is the motivating case).
                        // A non-Int field/param write (and a `this.`-qualified write, a PropertyExpression that
                        // throws below) still bails loudly to the "outside the value-flow fragment" skip. Field-delta
                        // *postconditions* are unaffected — they use the old-snapshot postcondition replay.
                        Variable acc = ((VariableExpression) be.leftExpression).accessedVariable
                        if (acc instanceof FieldNode || acc instanceof Parameter) {
                            ClassNode lt = (acc instanceof FieldNode) ? ((FieldNode) acc).type : ((Parameter) acc).type
                            if (isIntElement(lt)) {
                                steps.add(new FieldAssign(name, be.rightExpression))
                                continue
                            }
                            throw new UnsupportedConstructException("assignment to a non-Int field/parameter '${name}'")
                        }
                        if (!assigned.add(name)) throw new UnsupportedConstructException("re-assignment of '${name}'")
                        steps.add(new Assign(name, be.rightExpression))
                        continue
                    }
                    // Array-element store `a[i] = v`: not a scalar binding. Its *contents* aren't tracked
                    // by the value-flow pass (the implicit obligations — bounds/div/null — don't depend on
                    // them), but the LHS index access and the rhs still carry their own obligations. Handle
                    // it rather than throwing, so a body that stores stays on the value-flow path (which
                    // understands short-circuit guards) instead of the value-flow-blind havoc fallback.
                    if (be.leftExpression instanceof BinaryExpression &&
                        ((BinaryExpression) be.leftExpression).operation.type == Types.LEFT_SQUARE_BRACKET) {
                        scanObligations(be.leftExpression, steps, out)
                        scanObligations(be.rightExpression, steps, out)
                        continue
                    }
                    throw new UnsupportedConstructException("assignment to a non-variable target")
                }
                // Phase 42 — a standalone method call (xs.add(v), s.remove(x), m.put(k,v), …) is a
                // candidate LemmaCall: it might mutate size/contents that downstream obligations
                // depend on. Collect the call's own obligations *first* (pre-mutation state),
                // then thread it as a LemmaCall step so downstream sites see the effect during
                // discharge. Calls that don't match any apply-mutation handler are silently
                // ignored at replay time — the LemmaCall is then a no-op.
                scanObligations(e, steps, out)
                // Phase 237 — a survived statement-position non-null asserter (Objects.requireNonNull,
                // single-arg assertNotNull, assertThat(x).isNotNull()) is a guard-throw the program
                // moved past: the target is non-null on every continuing path. The Phase 222 survival
                // argument, threaded as a Guard step so only obligations AFTER the call see the fact —
                // a deref BEFORE it still refutes.
                Expression nnt = nonNullAssertedTarget(e)
                if (nnt != null) steps.add(new Guard(nonNullFact(nnt), true))
                if (e instanceof MethodCallExpression) {
                    steps.add(new LemmaCall(e))
                }
                continue
            }
            if (st instanceof AssertStatement) {
                // A user `assert P` is an obligation the author wrote explicitly: prove P at this point under the
                // reaching context. First collect any implicit obligations inside P (e.g. the `a[i]` in
                // `assert a[i] > 0`); then add the assertion itself; then thread it as a Guard so a *subsequent*
                // obligation may use it (e.g. `assert i < n; … a[i]`) — sound by assume/enforce, since P is proven
                // by the obligation just added.
                Expression cond = ((AssertStatement) st).booleanExpression
                scanObligations(cond, steps, out)
                AssertSite asite = new AssertSite()
                asite.node = st
                asite.cond = cond
                out.add(mkVf(asite, new ArrayList<Object>(steps)))
                steps.add(new Guard(cond, true))
                continue
            }
            // Loops, switch, try/catch, etc. — outside the value-flow fragment.
            throw new UnsupportedConstructException(
                "statement ${st.class.simpleName} outside value-flow fragment")
        }
    }

    /** Collect the implicit obligations syntactically present in {@code e}, each tagged with a snapshot of context. */
    private void scanObligations(Expression e, List<Object> steps, List<VfObligation> out) {
        if (e == null) return

        // Short-circuit / conditional operators carry a path condition *within* the expression: in
        // `p && q` the right operand is evaluated only when `p` holds; in `p || q` only when `p` is
        // false; in `c ? t : e`, `t` only when `c`, `e` only when not. So an obligation inside such a
        // branch (e.g. the `a[i-1]` in `i > 0 && a[i] < a[i-1]`) is discharged under that extra guard —
        // without this, the access is checked unprotected and a perfectly safe expression is refuted.
        if (e instanceof BooleanExpression) {   // Groovy wraps if/ternary conditions
            scanObligations(((BooleanExpression) e).expression, steps, out)
            return
        }
        if (e instanceof BinaryExpression) {
            int op = ((BinaryExpression) e).operation.type
            if (op == Types.LOGICAL_AND || op == Types.LOGICAL_OR) {
                BinaryExpression be = (BinaryExpression) e
                scanObligations(be.leftExpression, steps, out)
                scanObligations(be.rightExpression,
                    appendStep(steps, new Guard(be.leftExpression, op == Types.LOGICAL_AND)), out)
                return
            }
        }
        if (e instanceof TernaryExpression) {
            TernaryExpression te = (TernaryExpression) e
            scanObligations(te.booleanExpression, steps, out)
            scanObligations(te.trueExpression, appendStep(steps, new Guard(te.booleanExpression, true)), out)
            scanObligations(te.falseExpression, appendStep(steps, new Guard(te.booleanExpression, false)), out)
            return
        }

        ObligationCollector col = new ObligationCollector()
        col.overflowChecking = currentOverflowChecking
        try { e.visit(col) } catch (Throwable ignored) { return }
        if (col.indexSites.isEmpty() && col.divideSites.isEmpty() &&
            col.derefSites.isEmpty() && col.overflowSites.isEmpty() &&
            col.stringCharAtSites.isEmpty() && col.stringSubstringSites.isEmpty() &&
            col.parseSites.isEmpty()) return
        List<Object> snap = new ArrayList<Object>(steps)
        for (IndexSite s : col.indexSites)  out.add(mkVf(s, snap))
        for (DivideSite s : col.divideSites) out.add(mkVf(s, snap))
        for (DerefSite s : col.derefSites)  out.add(mkVf(s, snap))
        for (OverflowSite s : col.overflowSites) out.add(mkVf(s, snap))
        for (StringCharAtSite s : col.stringCharAtSites) out.add(mkVf(s, snap))
        for (StringSubstringSite s : col.stringSubstringSites) out.add(mkVf(s, snap))
        for (ParseSite s : col.parseSites) out.add(mkVf(s, snap))
    }

    /** Append a single step ({@link Guard} / {@link Assign} / {@link LemmaCall}) to a copy of {@code base}. */
    private static List<Object> appendStep(List<Object> base, Object step) {
        List<Object> r = new ArrayList<Object>(base); r.add(step); return r
    }


    private static VfObligation mkVf(Object site, List<Object> steps) {
        VfObligation v = new VfObligation()
        v.site = site; v.steps = steps
        return v
    }

    /** Discharge a value-flow obligation: assume @Requires + class invariants, replay the reaching steps in source order, then check. */
    private void dischargeVfObligation(MethodNode node, VfObligation v, Expression reqAst) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            if (reqAst != null) {
                Object pre = enc.translateBool(reqAst)
                if (pre != null) { s.assertExpr(pre); captureExplain(s, enc, reqAst, pre) }
                assumePreconditionNonNullFacts(s, enc, reqAst)
            }
            // Phase 15a — class invariants are method-entry facts, assumed before any
            // reaching step is replayed.
            assumeIntJvmBounds(s, enc)
            assumeClassInvariants(s, enc)
            // Phase 42 — replay the steps in source order. {@link Assign} factor handling
            // (materialised sets, factories) mirrors checkPath. {@link Guard} adds a path fact.
            // {@link LemmaCall} threads a set/map/list mutation via the same apply* handlers
            // checkPath uses; unrecognised calls are silently ignored so the implicit pass
            // doesn't fail on lemma-style callees that won't affect downstream oracles. The
            // ordered walk keeps the oracles' state consistent between the two passes.
            for (Object step : v.steps) {
                if (step instanceof Assign) {
                    Assign a = (Assign) step
                    if (enc.tryMaterialiseSetBinopAssign(a.name, a.rhs)) continue
                    if (enc.tryRecordFactoryAssign(a.name, a.rhs)) continue
                    // Phase 153/154 — async/await replay must match checkPath, or a downstream `r[i]` bounds / await
                    // read-out can't discharge in this seeded session: `def fa = async { e }` aliases fa to e, and
                    // `r = await(a,b,c)` records r as the gathered value-list factory.
                    if (Encoder.isAsyncCall(a.rhs) && Encoder.asyncBodyExpr(a.rhs) != null) {
                        enc.registerAsyncSource(a.name, Encoder.asyncBodyExpr(a.rhs)); continue
                    }
                    if (enc.tryRecordAwaitAll(a.name, a.rhs)) continue
                    if (enc.tryBindAwaitAny(a.name, a.rhs)) continue
                    // Phase 113 — a tuple-returning call (`r = callee(...)`): constrain r's slots by the
                    // callee's @Ensures so a downstream `a[r.vN]` / call-arg obligation sees the slot bounds.
                    // Mirrors checkPath; without it r$vN is unconstrained here and the bound can't discharge.
                    if (isCallExpr(a.rhs) && currentTupleTypes.get(a.name) != null) {
                        enc.registerTupleLocal(a.name, currentTupleTypes.get(a.name))
                        if (assumeCalleeEnsures(s, enc, a.rhs, node, null, hasDecreases(node), a.name)) continue
                    }
                    assertSurvivalFacts(s, enc, a.rhs, node)   // Phase 222 — executed call ⟹ no arm held
                    // Phase 227 — `def d = q` on a reference: the local shares the source's nullity (a
                    // downstream `d.m()` deref obligation must see the caller's `q != null`)
                    if (a.rhs instanceof VariableExpression) {
                        enc.bindNullity(a.name, enc.nullityOf(((VariableExpression) a.rhs).name))
                    }
                    Object rhs = enc.translate(a.rhs)
                    if (rhs != null) { s.assertExpr(s.eq(enc.varFor(a.name), rhs)); continue }
                    // Phase 221 — scalar `i = call()` whose callee has consumable @Ensures (checkPath's
                    // scalar branch, mirrored): without this, a registry-spec'd call in the obligation
                    // replay leaves `i` unconstrained and a downstream `s.charAt(i)` bound can't discharge.
                    if (isCallExpr(a.rhs)) {
                        if (calleeReturnsList(a.rhs, node)) {
                            // Phase 225 — list-returning callee: the rename route (see checkPath), so the
                            // callee's reference-oracle facts land on the local for downstream obligations
                            listLocalFromCall(s, enc, a.name, a.rhs, node)
                        } else {
                            Object fresh = s.intVar('specw$' + Integer.toHexString(System.identityHashCode(a.rhs)))
                            if (assumeCalleeEnsures(s, enc, a.rhs, node, fresh, hasDecreases(node))) {
                                s.assertExpr(s.eq(enc.varFor(a.name), fresh))
                            }
                        }
                    }
                } else if (step instanceof FieldAssign) {
                    // SSA-version a field/param write: read the rhs against the CURRENT (pre-write) symbol, then
                    // rebind the name to a fresh symbol equal to it, so subsequent reads see the post-write value
                    // without the entry symbol picking up a self-contradictory `name == rhs` constraint.
                    FieldAssign a = (FieldAssign) step
                    Object rhs = enc.translate(a.rhs)
                    if (rhs != null) {
                        Object fresh = s.intVar('ssa$' + a.name + '$' + (ssaCounter++))
                        s.assertExpr(s.eq(fresh, rhs))
                        enc.bind(a.name, fresh)
                    }
                } else if (step instanceof SoftAssume) {
                    Object c = enc.translate(((SoftAssume) step).cond)   // Phase 223 — catch-entry fact
                    if (c != null) {
                        s.assertExpr(c)
                        if (Reporter.EXPLAIN) {
                            s.explainNoteFact("TRUSTED catch-entry fact (${((SoftAssume) step).cond.text.replaceAll(/\s+/, ' ')}) — registry arms".toString(), c)
                        }
                    }
                } else if (step instanceof Guard) {
                    Guard g = (Guard) step
                    Object c = enc.translate(g.cond)
                    if (c != null) s.assertExpr(g.positive ? c : s.not(c))
                } else if (step instanceof LemmaCall) {
                    Expression call = ((LemmaCall) step).call
                    // Note: countVals are scoped to a postcondition's @Ensures, not relevant for implicit
                    // obligations (bounds/null/div) — pass empty so the bcount boundary law just skips for
                    // unrelated v's. The size-thread is what we need here.
                    if (applySetMutation(s, enc, call)) continue
                    if (applyMapPut(s, enc, call)) continue
                    if (applyListMutation(s, enc, call, Collections.<Object>emptyList())) continue
                    // Caller-side framing for a standalone @Modifies / @Ensures call: havoc the callee's declared
                    // frame and assume its @Ensures — exactly as the postcondition path (`assumeCalleeEnsures`)
                    // does — so a downstream obligation can't assume a field the call modified is unchanged.
                    // Without this the call was a silent no-op, so an in-segment obligation could be proven over a
                    // field a @Modifies call actually changed (the call-framing gap). An uncontracted call (no
                    // @Modifies/@Ensures) still no-ops here — assumeCalleeEnsures returns false, nothing to model.
                    assumeCalleeEnsures(s, enc, call, node, null, hasDecreases(node))
                }
            }
            dischargeObligationUnder(s, enc, v.site)
        } finally {
            try { s.close() } catch (Throwable ignored) {}
        }
    }

    /** Assume the method's own @Requires (if encodable), the class invariants, plus the path facts at a site. */
    private void assumeContext(SmtSession s, Encoder enc, Expression reqAst, ASTNode site, PathFacts pf) {
        if (reqAst != null) {
            Object pre = enc.translateBool(reqAst)
            if (pre != null) {
                s.assertExpr(pre)
                captureExplain(s, enc, reqAst, pre)
            }
            assumePreconditionNonNullFacts(s, enc, reqAst)
        }
        // Phase 44c — every Int-typed parameter and field is JVM-bounded to
        // {@code [Integer.MIN_VALUE, Integer.MAX_VALUE]}. Always asserted (not opt-in): the JVM
        // contract guarantees it, the verifier just hadn't been modelling it. Especially material
        // for {@code @CheckOverflow}, where Z3 would otherwise pick a math-int counterexample
        // outside the 32-bit range and produce a refute that the runtime can't actually exhibit.
        assumeIntJvmBounds(s, enc)
        // Phase 15a — class invariants are method-entry facts for the implicit-obligation discharge.
        // An invariant that bounds a field's length, for instance, lets a bare `a[i]` inside the body
        // verify under a loop-invariant-supplied range without restating the bound on every method.
        assumeClassInvariants(s, enc)
        for (IfFact f : pf.factsAt(site)) {
            Object c = enc.translate(f.condition)
            if (c == null) continue   // an unencodable fact just weakens the assumption set — safe
            s.assertExpr(f.inThenBranch ? c : s.not(c))
        }
    }

    /**
     * VERIFY_EXPLAIN — capture the authored precondition's top-level {@code &&} conjuncts (label + already-interned
     * term) for the post-proof ablation read-out. Re-translating each conjunct here is side-effect-free: the whole
     * precondition was just translated, so every var / literal is already minted. Any unencodable conjunct aborts
     * the registration (fail closed → "no explanation"), keeping the read-out honest rather than partial.
     */
    /**
     * VERIFY_EXPLAIN — the single capture hook, dropped in right after a precondition is asserted at every path
     * that assumes one (value-flow, per-site, havoc, loop). Centralised so a new assume path can't silently lose
     * the read-out. No-op unless the flag is on.
     */
    private void captureExplain(SmtSession s, Encoder enc, Expression reqAst, Object pre) {
        if (Reporter.EXPLAIN && pre != null && reqAst != null) registerExplainClauses(s, enc, reqAst, pre)
    }

    private void registerExplainClauses(SmtSession s, Encoder enc, Expression reqAst, Object preTerm) {
        List<String> labels = new ArrayList<String>()
        List<Object> terms = new ArrayList<Object>()
        for (Expression c : splitConjuncts(reqAst)) {
            Object t = enc.translateBool(c)
            if (t == null) { s.explainMarkGap(); return }   // a clause is outside the fragment → honest gap, not silence
            labels.add('@Requires ' + c.text)
            terms.add(t)
        }
        if (!labels.isEmpty()) s.explainRegister(preTerm, labels, terms)
    }

    /**
     * VERIFY_EXPLAIN — for a discharged (VERIFIED) implicit obligation, print which authored {@code @Requires}
     * clauses the proof actually leaned on. No-op unless the flag is on and the goal verified; the ablation runs
     * in fresh solvers and cannot affect the result already reported.
     */
    private void explainIfVerified(SmtSession s, CheckResult r, String obligation) {
        if (Reporter.EXPLAIN && r.status == CheckResult.Status.VERIFIED) {
            Reporter.emitExplain(obligation, s.explainLoadBearing(), s.explainHadGap())
        }
    }

    /**
     * Phase 44c — assert {@code INT_MIN ≤ x ≤ INT_MAX} for every Int-typed parameter and
     * declaring-class field. Sound by the JVM's {@code int} contract; needed under
     * {@code @CheckOverflow} so the verifier's math-int counterexamples match the values the
     * runtime can actually exhibit. Locals are bounded transitively via their assignment rhs.
     */
    /**
     * Phase 45b — when a method returns a list-typed local, alias {@code result}'s size and
     * array oracles to the local's threaded state. Without this, {@code result.size()} in an
     * @Ensures resolves to a fresh unconstrained {@code sizeOf("result")} that has no
     * relationship to the actual returned list — so a {@code @Ensures({ result.size() <= n })}
     * couldn't verify even when the body provably maintained that bound on the local.
     */
    private void aliasResultToReturnedListLocal(SmtSession s, Encoder enc, Expression returnExpr) {
        if (!(returnExpr instanceof VariableExpression)) return
        String localName = ((VariableExpression) returnExpr).name
        if (localName == null || localName == 'result') return
        // Alias when the name is a known list-typed identifier from any of three signals:
        //   (a) currentListNames — parameter / field declared list.
        //   (b) peekArray(localName) — array oracle already minted (body-replay path: the local
        //       was bound by a factory or a list mutation).
        //   (c) hasSizeOracle(localName) — size oracle already minted, e.g. by an invariant
        //       that referenced {@code positive.size()} (the loop pass: checkUse asserts the
        //       invariant first, which mints sizeOf even when the body wasn't replayed).
        if (currentListNames.contains(localName) ||
            enc.peekArray(localName) != null ||
            enc.hasSizeOracle(localName)) {
            enc.bindSize('result', enc.sizeOf(localName))
            enc.bindArray('result', enc.arrayFor(localName))
            // Add 'result' to currentListNames so {@code result.count(v)} routes through bcount
            // (Phase 41) the same way the local would.
            currentListNames.add('result')
        }
        // Phase 210 — the SET analogue: a set-typed local returned directly aliases result's set handle
        // and element-type classification, so @Ensures({ result.containsAll(a) }) reasons about the
        // returned set instead of skipping as outside-fragment (which also made the contract spell the
        // body LOCAL — not runtime-evaluable by groovy-contracts, a rung divergence).
        if (currentSetElementTypes.containsKey(localName) || enc.peekSet(localName) != null) {
            enc.bindSet('result', enc.setFor(localName))
            ClassNode et = currentSetElementTypes.get(localName)
            if (et != null) currentSetElementTypes.put('result', et)
        }
    }

    /**
     * Phase 97 / 101 — derive {@code != null} for a reference named in a top-level precondition conjunct whose
     * truth *requires* it to be non-null, so a later unguarded {@code recv.bar()} discharges its null-deref
     * obligation without a redundant explicit {@code recv != null}:
     * <ul>
     *   <li>safe navigation {@code recv?.foo()} / {@code recv?.prop} (Phase 97) — a null receiver makes
     *       {@code ?.} evaluate to {@code null}, which is falsy.</li>
     *   <li>range membership {@code v in lo..hi} (Phase 101) — a range never contains {@code null}, so the
     *       membership forces {@code v != null}. (List/Set membership does NOT — the collection may hold
     *       {@code null} — so only {@code Range} right-operands qualify.)</li>
     * </ul>
     * Sound only for top-level {@code &&} conjuncts: under an {@code ||} branch or a negation the implication
     * doesn't hold, so the walk descends through {@code &&} only.
     */
    private void assumePreconditionNonNullFacts(SmtSession s, Encoder enc, Expression reqAst) {
        if (reqAst == null) return
        List<Expression> conjuncts = new ArrayList<Expression>()
        collectAndConjuncts(reqAst, conjuncts)
        for (Expression c : conjuncts) {
            String recv = safeNavReceiverName(c)
            if (recv == null) recv = rangeMembershipValueName(c)
            if (recv != null) s.assertExpr(s.not(enc.nullityOf(recv)))
        }
    }

    /** The value name of a *range*-membership conjunct {@code v in lo..hi} whose value is a simple variable,
     *  else null. A range can't contain {@code null}, so the membership implies {@code v != null}; list/set
     *  membership (which may hold {@code null}) is deliberately excluded. */
    private static String rangeMembershipValueName(Expression e) {
        if (e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e
            if (be.operation.text == 'in' && be.rightExpression instanceof RangeExpression &&
                be.leftExpression instanceof VariableExpression) {
                return ((VariableExpression) be.leftExpression).name
            }
        }
        null
    }

    private static void collectAndConjuncts(Expression e, List<Expression> out) {
        if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.LOGICAL_AND) {
            collectAndConjuncts(((BinaryExpression) e).leftExpression, out)
            collectAndConjuncts(((BinaryExpression) e).rightExpression, out)
        } else {
            out.add(e)
        }
    }

    /** The receiver name of a safe-navigation call/property {@code recv?.x} whose receiver is a simple
     *  variable, else null. */
    private static String safeNavReceiverName(Expression e) {
        if (e instanceof MethodCallExpression) {
            MethodCallExpression m = (MethodCallExpression) e
            if (m.safe && m.objectExpression instanceof VariableExpression) {
                return ((VariableExpression) m.objectExpression).name
            }
        } else if (e instanceof PropertyExpression) {
            PropertyExpression pe = (PropertyExpression) e
            if (pe.safe && pe.objectExpression instanceof VariableExpression) {
                return ((VariableExpression) pe.objectExpression).name
            }
        }
        null
    }

    private void assumeIntJvmBounds(SmtSession s, Encoder enc) {
        if (currentMethod == null) return
        for (Parameter p : currentMethod.parameters) {
            assumeJvmIntegralBound(s, enc, p.type, p.name)
        }
        ClassNode dc = currentMethod.declaringClass
        if (dc != null) {
            for (FieldNode f : dc.fields) {
                assumeJvmIntegralBound(s, enc, f.type, f.name)
            }
        }
        // Bean Validation constraints (@Positive / @Min / @Max / …) are method-entry facts about the same params
        // and fields. Folded in here so every discharge path that assumes JVM bounds also assumes them — one
        // place, no scatter. (The vacuity check, which doesn't take this path, calls them separately.)
        assumeValidationConstraints(s, enc)
    }

    /**
     * Jakarta / {@code javax.validation.constraints} numeric constraints on a parameter or field, read as
     * method-entry preconditions — the same posture as {@code @Requires} / {@code @NonNull}: assumed in the body,
     * the caller's obligation. Matched by fully-qualified name, so the engine carries no dependency on the
     * validation API. First slice: numeric ({@code int}/{@code long}) constraints; {@code @NotNull} is already
     * handled by the nullness reader, and {@code @Size}/{@code @NotEmpty} are a later slice.
     */
    private void assumeValidationConstraints(SmtSession s, Encoder enc) {
        if (currentMethod == null) return
        for (Parameter p : currentMethod.parameters) assumeConstraintsFor(s, enc, p.annotations, p.type, p.name)
        ClassNode dc = currentMethod.declaringClass
        if (dc != null) for (FieldNode f : dc.fields) assumeConstraintsFor(s, enc, f.annotations, f.type, f.name)
    }

    private void assumeConstraintsFor(SmtSession s, Encoder enc, List<AnnotationNode> anns, ClassNode type, String name) {
        if (anns == null || anns.isEmpty()) return
        // A @NonNull-style annotation (the NullChecker / Checker Framework / JSR-305 vocabulary, matched by simple
        // name) on a reference parameter or field is a non-null precondition — assumed in the body, the same posture
        // as `@Requires({ x != null })`, with NullChecker enforcing it flow-sensitively at call sites.
        // Phase 239 — an explicit @Nullable on the same declaration (or its type use) defeats the
        // assumption: assuming non-null over the author's own disclaimer would be the unsound direction.
        if (type != null && !ClassHelper.isPrimitiveType(type) && hasAnnotationNamed(anns, NON_NULL_ANNOTATION_NAMES) &&
            !hasAnnotationNamed(anns, NULLABLE_ANNOTATION_NAMES) && !hasTypeAnnotationNamed(type, NULLABLE_ANNOTATION_NAMES)) {
            assertFact(s, s.not(enc.nullityOf(name)), '@NonNull ' + name)
        }
        boolean numeric = isJvmInt(type) || isJvmLong(type)            // @Positive/@Min/… → bound on the value
        boolean isStr = type?.name == 'java.lang.String'              // @Size/@NotEmpty → string length
        boolean sized = type != null && (type.isArray() || isListType(type))   // @Size/@NotEmpty → collection size
        if (!numeric && !isStr && !sized) return
        Object v = numeric ? enc.varFor(name) : null
        Object sz = isStr ? s.stringLength(enc.varForOfSort(name, s.declareSort('String')))
                          : (sized ? enc.sizeOf(name) : null)
        for (AnnotationNode a : anns) {
            String fqn = a?.classNode?.name
            if (fqn == null) continue
            if (!fqn.startsWith('jakarta.validation.constraints.') && !fqn.startsWith('javax.validation.constraints.')) continue
            String c = fqn.substring(fqn.lastIndexOf('.') + 1)
            if (numeric) {
                switch (c) {
                    case 'Positive':       assertFact(s, s.gt(v, s.intLit(0L)), '@Positive ' + name); break
                    case 'PositiveOrZero': assertFact(s, s.ge(v, s.intLit(0L)), '@PositiveOrZero ' + name); break
                    case 'Negative':       assertFact(s, s.lt(v, s.intLit(0L)), '@Negative ' + name); break
                    case 'NegativeOrZero': assertFact(s, s.le(v, s.intLit(0L)), '@NegativeOrZero ' + name); break
                    case 'Min':            { Long n = longMember(a); if (n != null) assertFact(s, s.ge(v, s.intLit(n)), "@Min(${n}) ${name}".toString()); break }
                    case 'Max':            { Long n = longMember(a); if (n != null) assertFact(s, s.le(v, s.intLit(n)), "@Max(${n}) ${name}".toString()); break }
                }
            } else if (sz != null) {   // String / array / List — @Size / @NotEmpty bound the length or size
                switch (c) {
                    case 'NotEmpty':
                        // @NotEmpty implies non-null *and* size ≥ 1 (unlike @Size, which a null value satisfies).
                        assertFact(s, s.not(enc.nullityOf(name)), '@NotEmpty ' + name + ' (≠ null)')
                        assertFact(s, s.ge(sz, s.intLit(1L)),      '@NotEmpty ' + name + ' (size ≥ 1)')
                        break
                    case 'Size':
                        int mn = intMember(a, 'min', 0)
                        int mx = intMember(a, 'max', Integer.MAX_VALUE)
                        if (mn > 0)                 assertFact(s, s.ge(sz, s.intLit((long) mn)), "@Size(min=${mn}) ${name}".toString())
                        if (mx < Integer.MAX_VALUE) assertFact(s, s.le(sz, s.intLit((long) mx)), "@Size(max=${mx}) ${name}".toString())
                        break
                }
            }
        }
    }

    /** Assert a derived constraint fact and, under VERIFY_EXPLAIN, register it for the load-bearing read-out. */
    private void assertFact(SmtSession s, Object fact, String label) {
        s.assertExpr(fact)
        if (Reporter.EXPLAIN) s.explainNoteFact(label, fact)
    }

    /** The {@code long}-valued {@code value} member of a {@code @Min}/{@code @Max} annotation, or null. */
    private static Long longMember(AnnotationNode a) {
        Expression m = a.getMember('value')
        if (m instanceof ConstantExpression) {
            Object val = ((ConstantExpression) m).value
            if (val instanceof Number) return ((Number) val).longValue()
        }
        null
    }

    /** An {@code int}-valued member of a {@code @Size} annotation ({@code min}/{@code max}), or {@code dflt}. */
    private static int intMember(AnnotationNode a, String member, int dflt) {
        Expression m = a.getMember(member)
        if (m instanceof ConstantExpression) {
            Object val = ((ConstantExpression) m).value
            if (val instanceof Number) return ((Number) val).intValue()
        }
        dflt
    }

    /** True if any parameter or field carries a Bean Validation constraint annotation (so the vacuity check runs). */
    private static boolean hasValidationConstraints(MethodNode node) {
        for (Parameter p : node.parameters) if (hasAnyValidationConstraint(p.annotations)) return true
        ClassNode dc = node.declaringClass
        if (dc != null) for (FieldNode f : dc.fields) if (hasAnyValidationConstraint(f.annotations)) return true
        false
    }

    private static boolean hasAnyValidationConstraint(List<AnnotationNode> anns) {
        if (anns == null) return false
        for (AnnotationNode a : anns) {
            String fqn = a?.classNode?.name
            if (fqn != null && (fqn.startsWith('jakarta.validation.constraints.') || fqn.startsWith('javax.validation.constraints.'))) return true
        }
        false
    }

    /** Phase 44c — assert the integral type's JVM range for a parameter/field: {@code int}/{@code Integer}
     *  to {@code [INT_MIN, INT_MAX]}, {@code long}/{@code Long} to {@code [LONG_MIN, LONG_MAX]}. Without the
     *  long case, a {@code long} param is an unbounded math integer, so the 64-bit overflow check picks a
     *  counterexample *below* {@code Long.MIN_VALUE} ({@code n + 1 < LONG_MIN}) that the runtime can't exhibit. */
    private void assumeJvmIntegralBound(SmtSession s, Encoder enc, ClassNode t, String name) {
        long lo, hi
        if (isJvmInt(t))       { lo = (long) Integer.MIN_VALUE; hi = (long) Integer.MAX_VALUE }
        else if (isJvmLong(t)) { lo = Long.MIN_VALUE;           hi = Long.MAX_VALUE }
        else return
        Object v = enc.varFor(name)
        Object bound = s.and([s.le(s.intLit(lo), v), s.le(v, s.intLit(hi))])
        s.assertExpr(bound)
        if (Reporter.EXPLAIN) s.explainNoteFact("JVM bound (${name} in ${isJvmInt(t) ? 'int' : 'long'} range)".toString(), bound)
    }

    private static boolean isJvmInt(ClassNode t) {
        String n = t?.name
        n == 'int' || n == 'java.lang.Integer'
    }

    private static boolean isJvmLong(ClassNode t) {
        String n = t?.name
        n == 'long' || n == 'java.lang.Long'
    }

    private void dischargeIndex(IndexSite site, PathFacts pf, Expression reqAst) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            assumeContext(s, enc, reqAst, site.node, pf)
            dischargeObligationUnder(s, enc, site)
        } finally {
            try { s.close() } catch (Throwable ignored) {}
        }
    }

    private void dischargeDivide(DivideSite site, PathFacts pf, Expression reqAst) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            assumeContext(s, enc, reqAst, site.node, pf)
            dischargeObligationUnder(s, enc, site)
        } finally {
            try { s.close() } catch (Throwable ignored) {}
        }
    }

    private void dischargeParse(ParseSite site, PathFacts pf, Expression reqAst) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            assumeContext(s, enc, reqAst, site.node, pf)
            dischargeObligationUnder(s, enc, site)
        } finally {
            try { s.close() } catch (Throwable ignored) {}
        }
    }

    private void dischargeDeref(DerefSite site, PathFacts pf, Expression reqAst) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            assumeContext(s, enc, reqAst, site.node, pf)
            dischargeObligationUnder(s, enc, site)
        } finally {
            try { s.close() } catch (Throwable ignored) {}
        }
    }

    private void dischargeOverflow(OverflowSite site, PathFacts pf, Expression reqAst) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            assumeContext(s, enc, reqAst, site.node, pf)
            dischargeObligationUnder(s, enc, site)
        } finally {
            try { s.close() } catch (Throwable ignored) {}
        }
    }

    /** Phase 44c — the static type's simple name, preferring STC's inferred type (so a nested
     *  {@code (a + b)} operand reports its promoted result type, not the raw node type). */
    private static String overflowTypeName(Expression e) {
        if (e == null) return null
        ClassNode inf = (ClassNode) e.getNodeMetaData(StaticTypesMarker.INFERRED_TYPE)
        ClassNode t = inf != null ? inf : e.getType()
        return t?.nameWithoutPackage
    }
    /** True if the expression is {@code long}/{@code Long} — promotes its arithmetic to 64-bit. */
    private static boolean isLongTyped(Expression e) {
        String n = overflowTypeName(e)
        return n == 'long' || n == 'Long'
    }
    /** True if the expression is {@code BigInteger} — unbounded, so no overflow obligation applies. */
    private static boolean isBigIntegerTyped(Expression e) {
        return overflowTypeName(e) == 'BigInteger'
    }

    /**
     * Assert the negation of one implicit obligation against an already-seeded
     * session (context assumptions added by the caller) and report if it is not
     * discharged. Shared by the havoc pass and the Phase 5 value-flow pass.
     */
    private void dischargeObligationUnder(SmtSession s, Encoder enc, Object site) {

        // Phase 193 — an obligation inside a try whose handler covers its exception is DEFINED behaviour:
        // the throw transfers to the catch path (modelled since Phase 192), so nothing is uncaught and a
        // "Possible X ... fails on f(...)" refutation would be factually wrong (f(...) returns the
        // handler's value). Silent, like the map-lookup no-obligation return below; conservative — only
        // the curated CATCH_COVERS types suppress, and only for sites positioned inside the try block.
        String obEx = obligationExceptionOf(site)
        if (obEx != null && site.hasProperty('node') && catchCovered((org.codehaus.groovy.ast.ASTNode) site['node'], obEx)) return
        if (site instanceof AssertSite) {
            AssertSite asite = (AssertSite) site
            Object p = enc.translateGoal(asite.cond)
            if (p == null) {
                addStaticTypeError(Reporter.formatImplicitSkipped("assertion",
                    "condition '${asite.cond.text}' is outside fragment"), asite.node)
                return
            }
            s.assertExpr(s.not(p))                       // negation of the asserted predicate
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                // If the assertion is over a method parameter, it is usually a caller precondition written as a
                // runtime check; nudge toward @Requires, which documents it and is checked at every call site.
                boolean overParam = referencesParameter(asite.cond, currentMethod)
                addStaticTypeError(withRepro(Reporter.formatAssertion(asite.cond.text, r, overParam), r, 'AssertionError'), asite.node)
            }
            return
        }
        if (site instanceof IndexSite) {
            IndexSite ix = (IndexSite) site
            // m[k] on a map is a key lookup, not a bounds-checked array index — no obligation.
            if (currentMapTypes.containsKey(ix.receiver)) return
            Object idx = enc.translate(ix.index)
            if (idx == null) {
                addStaticTypeError(Reporter.formatImplicitSkipped("array index",
                    "index '${ix.index.text}' is outside fragment"), ix.node)
                return
            }
            Object size = enc.sizeOf(ix.receiver)
            Object inBounds = s.and([s.le(s.intLit(0L), idx), s.lt(idx, size)])
            s.assertExpr(s.not(inBounds))
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(withSuggestion(withRepro(Reporter.formatIndexBounds(
                    ix.index.text, ix.receiver + sizeAccessor(ix.receiver), r), r, 'IndexOutOfBoundsException'), ix), ix.node)
            }
            explainIfVerified(s, r, "${ix.receiver}[${ix.index.text}] in bounds")
            return
        }
        if (site instanceof DivideSite) {
            DivideSite dv = (DivideSite) site
            // IEEE-754 division never throws (x / 0.0 == ±Inf/NaN), so an FP-valued divide carries no
            // divide-by-zero obligation — skip silently (the integer/decimal `b != 0` check doesn't apply).
            if (dv.node instanceof Expression && enc.isFpValued((Expression) dv.node)) return
            // Phase 143 — a decimal (BigDecimal) divisor is checked in the Real sort (against a Real zero), so a
            // `metres / 1000.0` divide discharges instead of skipping for an Int-only divisor translation.
            boolean decimalDiv = dv.divisor != null && enc.isDecimalValued(dv.divisor)
            Object divisor = decimalDiv ? enc.asRealValue(dv.divisor) : enc.translate(dv.divisor)
            if (divisor == null) {
                addStaticTypeError(Reporter.formatImplicitSkipped("division",
                    "divisor '${dv.divisor.text}' is outside fragment"), dv.node)
                return
            }
            Object zero = decimalDiv ? enc.asRealValue(new ConstantExpression(0.0G)) : s.intLit(0L)
            if (dv.requirePositive) {
                // a.mod(b) throws ArithmeticException("BigInteger: modulus not positive") unless b > 0.
                s.assertExpr(s.not(s.gt(divisor, zero)))   // negation of (divisor > 0)
                CheckResult r = shown(s.check())
                if (r.status != CheckResult.Status.VERIFIED) {
                    addStaticTypeError(Reporter.formatModulusNotPositive(dv.divisor.text, r), dv.node)
                }
                return
            }
            s.assertExpr(s.not(s.ne(divisor, zero)))   // negation of (divisor != 0)
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(withSuggestion(withRepro(Reporter.formatDivisionByZero(dv.divisor.text, r), r, 'ArithmeticException'), dv), dv.node)
            }
            explainIfVerified(s, r, "${dv.divisor.text} != 0")
            return
        }
        if (site instanceof ParseSite) {
            ParseSite ps = (ParseSite) site
            Object str = enc.translateInSort(ps.arg, s.declareSort('String'))
            if (str == null) {
                addStaticTypeError(Reporter.formatImplicitSkipped("parse",
                    "argument '${ps.arg.text}' is outside fragment"), ps.node)
                return
            }
            s.assertExpr(s.not(s.parseIntValid(str)))   // negation of "is a valid numeral"
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(Reporter.formatNumberFormat(ps.arg.text, r), ps.node)
            }
            explainIfVerified(s, r, "${ps.arg.text} parses as int")
            return
        }
        if (site instanceof DerefSite) {
            DerefSite df = (DerefSite) site
            if (df.indexExpr != null) {
                // Phase 37 — indexed receiver (xs[i].method() / xs.get(i).method()): consult the
                // per-element nullity oracle. A @NonNull-element container is trusted — no
                // obligation fires. (No quantifier needed to encode the "trust"; we just skip.)
                if (currentNonNullElementContainers.contains(df.receiver)) return
                Object idx = enc.translate(df.indexExpr)
                if (idx == null) {
                    addStaticTypeError(Reporter.formatImplicitSkipped("element dereference",
                        "index '${df.indexExpr.text}' is outside fragment"), df.node)
                    return
                }
                Object flag = s.select(enc.elementNullityFor(df.receiver), idx)
                s.assertExpr(s.eq(flag, s.intLit(1L)))   // negation of (flag == 0, i.e. non-null)
                CheckResult r = shown(s.check())
                if (r.status != CheckResult.Status.VERIFIED) {
                    addStaticTypeError(withSuggestion(withRepro(Reporter.formatNullDereference(
                        "${df.receiver}[${df.indexExpr.text}]", df.method, r), r, 'NullPointerException'), df), df.node)
                }
                explainIfVerified(s, r, "${df.receiver}[${df.indexExpr.text}] != null")
                return
            }
            // Obligation: ¬isNull(recv). Assert its negation, isNull(recv), and
            // check: SAT means the receiver can be null on this path.
            s.assertExpr(enc.nullityOf(df.receiver))
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(withSuggestion(withRepro(Reporter.formatNullDereference(df.receiver, df.method, r), r, 'NullPointerException'), df), df.node)
            }
            explainIfVerified(s, r, "${df.receiver} != null")
        }
        if (site instanceof StringCharAtSite) {
            StringCharAtSite cs = (StringCharAtSite) site
            // Discriminate by receiver type: charAt has a meaningful bounds obligation only on
            // String receivers. A non-String receiver (a List-typed name that happens to be
            // called .charAt — Groovy doesn't define that, but be defensive) skips silently.
            ClassNode rt = currentScalarTypes.get(cs.receiver)
            if (rt == null || rt.name != 'java.lang.String') return
            Object idx = enc.translate(cs.indexExpr)
            if (idx == null) {
                addStaticTypeError(Reporter.formatImplicitSkipped("charAt index",
                    "index '${cs.indexExpr.text}' is outside fragment"), cs.node)
                return
            }
            Object recvHandle = enc.varForOfSort(cs.receiver, s.declareSort('String'))
            Object len = s.stringLength(recvHandle)
            Object inBounds = s.and([s.le(s.intLit(0L), idx), s.lt(idx, len)])
            s.assertExpr(s.not(inBounds))
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(withRepro(Reporter.formatIndexBounds(
                    cs.indexExpr.text, cs.receiver + '.length()', r), r, 'IndexOutOfBoundsException'), cs.node)
            }
            explainIfVerified(s, r, "${cs.receiver}.charAt(${cs.indexExpr.text}) in bounds")
            return
        }
        if (site instanceof StringSubstringSite) {
            StringSubstringSite ss = (StringSubstringSite) site
            ClassNode rt = currentScalarTypes.get(ss.receiver)
            if (rt == null || rt.name != 'java.lang.String') return
            Object begin = enc.translate(ss.beginExpr)
            if (begin == null) {
                addStaticTypeError(Reporter.formatImplicitSkipped("substring begin",
                    "argument '${ss.beginExpr.text}' is outside fragment"), ss.node)
                return
            }
            Object recvHandle = enc.varForOfSort(ss.receiver, s.declareSort('String'))
            Object len = s.stringLength(recvHandle)
            Object inBounds
            if (ss.endExpr == null) {
                // Single-arg: 0 <= begin <= length
                inBounds = s.and([s.le(s.intLit(0L), begin), s.le(begin, len)])
            } else {
                Object end = enc.translate(ss.endExpr)
                if (end == null) {
                    addStaticTypeError(Reporter.formatImplicitSkipped("substring end",
                        "argument '${ss.endExpr.text}' is outside fragment"), ss.node)
                    return
                }
                // Two-arg: 0 <= begin <= end <= length
                inBounds = s.and([s.le(s.intLit(0L), begin), s.le(begin, end), s.le(end, len)])
            }
            s.assertExpr(s.not(inBounds))
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                String accessor = ss.endExpr == null
                    ? "${ss.beginExpr.text}"
                    : "${ss.beginExpr.text}, ${ss.endExpr.text}"
                addStaticTypeError(withRepro(Reporter.formatIndexBounds(
                    accessor, ss.receiver + '.length()', r), r, 'IndexOutOfBoundsException'), ss.node)
            }
            explainIfVerified(s, r, "${ss.receiver}.substring(${ss.beginExpr.text}${ss.endExpr != null ? ', ' + ss.endExpr.text : ''}) in bounds")
            return
        }
        if (site instanceof OverflowSite) {
            OverflowSite ov = (OverflowSite) site
            // Phase 44 — assert the negation of {@code INT_MIN <= result <= INT_MAX}; SAT means
            // the math result can lie outside 32-bit signed range on this path. Operands outside
            // the fragment surface as a "skipped" diagnostic rather than a refute, mirroring the
            // bounds/null/div skip rule.
            Object L = enc.translate(ov.left)
            Object R = ov.right != null ? enc.translate(ov.right) : null
            if (L == null || (ov.right != null && R == null)) {
                addStaticTypeError(Reporter.formatImplicitSkipped("integer overflow",
                    "operand of '${ov.text}' is outside fragment"), ov.node)
                return
            }
            // Phase 44b-div — division overflow uses a specific-pair failure assertion rather than
            // the general "result outside [INT_MIN, INT_MAX]" form, because the only arithmetic
            // case where {@code /} overflows is {@code Integer.MIN_VALUE / -1}. Asserting that exact
            // pair (and checking SAT) is equivalent to asserting the result's range violation but
            // doesn't require an integer-{@code div} SMT operator.
            // Phase 44c — width-aware bound. BigInteger arithmetic is unbounded (cannot overflow), so it
            // carries no obligation. Otherwise the operation's width follows Java binary numeric promotion
            // of the OPERANDS: 64-bit when either operand is long/Long, else 32-bit — int, and also
            // byte/short/char, which promote to int in arithmetic (their narrow widths matter only at a
            // narrowing cast/assignment, a separate slice). Operands, not the result type: `long x = a + b`
            // with int a/b overflows at *int* width — the addition is computed before the widen-to-long.
            if (isBigIntegerTyped(ov.left) || isBigIntegerTyped(ov.right)) return
            int width = (isLongTyped(ov.left) || isLongTyped(ov.right)) ? 64 : 32
            Object loLit = s.intLit(width == 64 ? Long.MIN_VALUE : (long) Integer.MIN_VALUE)
            Object hiLit = s.intLit(width == 64 ? Long.MAX_VALUE : (long) Integer.MAX_VALUE)
            if (ov.op == 'div') {
                // The only arithmetic `/` overflow is MIN_VALUE / -1 (math result one past MAX_VALUE).
                s.assertExpr(s.and([s.eq(L, loLit), s.eq(R, s.intLit(-1L))]))
                CheckResult r = shown(s.check())
                if (r.status != CheckResult.Status.VERIFIED) {
                    addStaticTypeError(withRepro(Reporter.formatOverflow(ov.text, ov.op, width, r), r, null), ov.node)
                }
                return
            }
            Object result = (ov.op == '+')   ? s.plus(L, R) :
                            (ov.op == '-')   ? s.minus(L, R) :
                            (ov.op == '*')   ? s.times(L, R) :
                            (ov.op == 'neg') ? s.neg(L) :
                                               null
            if (result == null) return    // unrecognised op shouldn't happen, but be defensive
            // ¬(MIN ≤ result ∧ result ≤ MAX)  ≡  result < MIN ∨ result > MAX
            s.assertExpr(s.or([s.lt(result, loLit), s.gt(result, hiLit)]))
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(withRepro(Reporter.formatOverflow(ov.text, ov.op, width, r), r, null), ov.node)
            }
        }
    }

    /**
     * Phase 5b — discharge a loop method's implicit obligations with the loop's
     * {@code @Invariant} in scope. Prefix sites see {@code @Requires} and the
     * straight-line prefix store; the guard and body sites additionally assume
     * the invariant (and, in the body, the guard); suffix sites assume the
     * invariant and the negated guard. Loop-modified variables are otherwise
     * havoc, so this proves exactly what the user's invariant is strong enough
     * to support — and honestly reports "could not decide" when it is not.
     */
    private void verifyLoopObligations(MethodNode node, List<LoopSite> sites) {
        Expression reqAst = findRequires(node) != null ? contractAstFor(node, 'requires') : null
        // 1. The region before the FIRST loop: @Requires + the straight-line store; no invariant yet.
        dischargeRegion(sites.get(0).segmentBefore, reqAst, Collections.<Expression>emptyList(), null)
        for (int si = 0; si < sites.size(); si++) {
            LoopSite site = sites.get(si)
            LoopSpec spec = site.spec
            // 1b. Phase 207 — the region between the previous loop and this one is the previous site's
            // segmentAfter (discharged below under ITS inv ∧ ¬guard); nothing extra here.
            // 2. Guard expression: evaluated whenever the invariant holds.
            for (Object s : sitesInExpression(spec.guard)) {
                dischargeSeeded(s, reqAst, spec.invariants, null, Collections.<Statement>emptyList())
            }
            // 3. Body: invariant ∧ guard, threaded through the (straight-line) body. handleAsserts=true so an
            // in-loop `assert` (the masking-fix class-invariant assert after a shared write) is discharged here.
            List<Expression> bodyAssumed = new ArrayList<Expression>(spec.invariants)
            bodyAssumed.add(spec.guard)
            dischargeRegion(spec.body, reqAst, bodyAssumed, null, Collections.<Statement>emptyList(), true)
            // 4. The region after this loop up to the next one (or the method end): inv ∧ ¬guard.
            dischargeRegion(site.segmentAfter, reqAst, spec.invariants, spec.guard)
            // 5. Phase 91 — a nested annotated loop's index/bounds obligations (e.g. `a[k] = …`) are
            // discharged in the INNER loop's own context (inner_inv ∧ inner_guard), where the inner index is
            // constrained — not under the outer invariant, where it isn't. dischargeRegion (step 3) skips them.
            for (Statement innerLoop : annotatedInnerLoops(spec.body)) {
                LoopSpec innerSpec = (LoopSpec) innerLoop.getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY)
                List<Expression> innerAssumed = new ArrayList<Expression>(innerSpec.invariants)
                innerAssumed.add(innerSpec.guard)
                dischargeRegion(innerSpec.body, reqAst, innerAssumed, null, Collections.<Statement>emptyList(), true)
            }
        }
    }

    /**
     * Discharge every obligation in a straight-line region, each under the seed plus the region's
     * preceding statements. Phase 46d — two short-circuit-aware refinements over the original:
     * <ul>
     *   <li>For in-region {@code if (cond) { … }} statements, recurse into the then-branch with
     *       {@code cond} added to {@code assumePos}, and (if present) into the else-branch with
     *       {@code !cond} added. Threads an in-body null guard like {@code if (xs[i] != null) …}
     *       as a path fact, same shape the straight-line {@link PathFacts} pass gets outside loops.</li>
     *   <li>Within an expression, descend through {@code &&}/{@code ||}/ternary so the right
     *       operand is discharged under the short-circuit guard. {@code xs[i] != null && xs[i].m()}
     *       discharges the second deref under the first conjunct, the same way Groovy's runtime
     *       short-circuits before evaluating it.</li>
     * </ul>
     */
    private void dischargeRegion(List<Statement> stmts, Expression reqAst,
                                 List<Expression> assumePos, Expression assumeNeg,
                                 List<Statement> outerPreceding = Collections.<Statement>emptyList(),
                                 boolean handleAsserts = false) {
        if (stmts == null) return
        // Expression-position `++`/`--` (`a[i++]`) → an explicit `[…uses i…, i = i+1]` sequence, so the
        // index's implicit bounds obligation is collected on `a[i]` and a later access sees the bumped `i`
        // through `preceding` (the increment statement is now part of it). Matches the VC-side hoist.
        stmts = Encoder.expandIncDecStatements(stmts)
        for (int i = 0; i < stmts.size(); i++) {
            Statement st = stmts.get(i)
            // The state at this site is everything that ran before it: the statements preceding it in
            // any ENCLOSING region (e.g. an `int mid = …` before the `if`) plus those preceding it here.
            // Without the enclosing prefix, an obligation nested in an `else if` branch would lose the
            // `mid` binding (havoc → spurious IndexOutOfBounds — the binary-search false positive).
            List<Statement> preceding = new ArrayList<Statement>(outerPreceding)
            preceding.addAll(stmts.subList(0, i))
            // Phase 91 — a nested annotated loop's OWN obligations are discharged separately, under its
            // invariant+guard (verifyInnerLoopObligations) — not here, where the inner index isn't yet
            // constrained. It still threads into `preceding` for later sites (LoopEncoder.symExec
            // summarises it during the replay).
            if (st instanceof LoopingStatement &&
                ((Statement) st).getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY) != null) {
                continue
            }
            if (st instanceof IfStatement) {
                IfStatement ifs = (IfStatement) st
                // Obligations in the if-condition itself: discharge with short-circuit awareness —
                // {@code xs[i] != null && xs[i].m()} needs the right deref to see the left guard.
                dischargeExpression(ifs.booleanExpression, reqAst, assumePos, assumeNeg, preceding)
                List<Expression> thenAssume = new ArrayList<Expression>(assumePos)
                thenAssume.add(ifs.booleanExpression)
                dischargeRegion(topStatements(ifs.ifBlock), reqAst, thenAssume, assumeNeg, preceding, handleAsserts)
                Statement elseBlk = ifs.elseBlock
                boolean hasElse = elseBlk != null && !(elseBlk instanceof EmptyStatement)
                if (hasElse) {
                    List<Expression> elseAssume = new ArrayList<Expression>(assumePos)
                    elseAssume.add(new NotExpression(ifs.booleanExpression))
                    dischargeRegion(topStatements(elseBlk), reqAst, elseAssume, assumeNeg, preceding, handleAsserts)
                }
                // Early-exit narrowing, as in collectVfObligations — the same idiom has to work on the SSA
                // fallback path (a body the value-flow pass bailed on: a re-assignment, a loop). Rebinding
                // `assumePos` narrows every later site in this region; `preceding` is untouched, so the
                // SSA replay still threads this `if` exactly as before.
                boolean thenExits = alwaysExits(ifs.ifBlock)
                boolean elseExits = hasElse && alwaysExits(elseBlk)
                if (thenExits && elseExits) return           // neither arm falls through — the rest is dead
                if (thenExits || elseExits) {
                    List<Expression> cont = new ArrayList<Expression>(assumePos)
                    cont.add(elseExits ? ifs.booleanExpression
                                       : (Expression) new NotExpression(ifs.booleanExpression))
                    assumePos = cont
                }
                continue
            }
            // Non-if statement: walk each top-level expression with short-circuit awareness too,
            // not just {@code sitesInStatement}, so an inline {@code a != null && a.m()} in any
            // statement gets the same treatment.
            dischargeStatementShortCircuit(st, reqAst, assumePos, assumeNeg, preceding, handleAsserts)
        }
    }

    /**
     * Phase 46d — short-circuit-aware discharge for one expression. Recurses through
     * {@code &&}/{@code ||}/ternary so each operand is discharged under the guard implied by
     * the operators that short-circuit before reaching it; leaf expressions are collected via
     * {@link #sitesInExpression} and discharged under the accumulated guards.
     */
    private void dischargeExpression(Expression e, Expression reqAst,
                                     List<Expression> assumePos, Expression assumeNeg,
                                     List<Statement> preceding) {
        if (e == null) return
        if (e instanceof BooleanExpression) {
            dischargeExpression(((BooleanExpression) e).expression, reqAst, assumePos, assumeNeg, preceding)
            return
        }
        if (e instanceof BinaryExpression) {
            int op = ((BinaryExpression) e).operation.type
            if (op == Types.LOGICAL_AND || op == Types.LOGICAL_OR) {
                BinaryExpression be = (BinaryExpression) e
                dischargeExpression(be.leftExpression, reqAst, assumePos, assumeNeg, preceding)
                List<Expression> rightAssume = new ArrayList<Expression>(assumePos)
                // && short-circuits when left is false → right runs when left is TRUE.
                // || short-circuits when left is true  → right runs when left is FALSE.
                rightAssume.add(op == Types.LOGICAL_AND
                    ? be.leftExpression
                    : new NotExpression(be.leftExpression))
                dischargeExpression(be.rightExpression, reqAst, rightAssume, assumeNeg, preceding)
                return
            }
        }
        if (e instanceof TernaryExpression) {
            TernaryExpression te = (TernaryExpression) e
            dischargeExpression(te.booleanExpression, reqAst, assumePos, assumeNeg, preceding)
            List<Expression> thenAssume = new ArrayList<Expression>(assumePos)
            thenAssume.add(te.booleanExpression)
            dischargeExpression(te.trueExpression, reqAst, thenAssume, assumeNeg, preceding)
            List<Expression> elseAssume = new ArrayList<Expression>(assumePos)
            elseAssume.add(new NotExpression(te.booleanExpression))
            dischargeExpression(te.falseExpression, reqAst, elseAssume, assumeNeg, preceding)
            return
        }
        // Leaf: collect any obligations syntactically present, discharge each under the
        // accumulated assumptions.
        for (Object site : sitesInExpression(e)) {
            dischargeSeeded(site, reqAst, assumePos, assumeNeg, preceding)
        }
    }

    /**
     * Phase 46d — discharge a non-{@code if} statement's obligations with short-circuit
     * awareness on its top-level expressions. For an {@code ExpressionStatement} or
     * {@code ReturnStatement}, route the expression through {@link #dischargeExpression};
     * for compound shapes (blocks, declarations with rhs), fall through to the original
     * statement-level discharge.
     */
    private void dischargeStatementShortCircuit(Statement st, Expression reqAst,
                                                List<Expression> assumePos, Expression assumeNeg,
                                                List<Statement> preceding, boolean handleAsserts = false) {
        if (st instanceof ExpressionStatement) {
            dischargeExpression(((ExpressionStatement) st).expression,
                reqAst, assumePos, assumeNeg, preceding)
            return
        }
        if (st instanceof ReturnStatement) {
            dischargeExpression(((ReturnStatement) st).expression,
                reqAst, assumePos, assumeNeg, preceding)
            return
        }
        if (handleAsserts && st instanceof AssertStatement) {
            // An in-loop `assert P` (e.g. the masking-fix class-invariant assert after a shared write): prove P
            // holds under the loop invariant ∧ guard ∧ the replayed preceding body. First discharge any obligations
            // inside P (e.g. an `a[i]` in the condition), then the assertion itself. symExec assumes P downstream.
            // Gated on handleAsserts so the straight-line fallback (which loud-skips asserts) is unchanged.
            Expression cond = ((AssertStatement) st).booleanExpression
            dischargeExpression(cond, reqAst, assumePos, assumeNeg, preceding)
            AssertSite asite = new AssertSite()
            asite.node = st
            asite.cond = cond
            dischargeSeeded(asite, reqAst, assumePos, assumeNeg, preceding)
            return
        }
        // Fallback: collect statement-wide sites and discharge each — preserves the original
        // behaviour for shapes we don't pattern-match (block statements that the loop body's
        // top-level walk shouldn't encounter, etc.).
        List<Object> sites = sitesInStatement(st)
        if (sites.isEmpty()) return
        for (Object site : sites) {
            dischargeSeeded(site, reqAst, assumePos, assumeNeg, preceding)
        }
    }

    /**
     * Fresh session: assume {@code @Requires}, the positive facts and the
     * optional negated fact, then bind-thread the preceding straight-line
     * statements (SSA semantics — correct even when the loop counter is
     * re-assigned), and discharge the obligation.
     */
    private void dischargeSeeded(Object site, Expression reqAst,
                                 List<Expression> assumePos, Expression assumeNeg,
                                 List<Statement> preceding) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            // Phase 91b — an array-index bound (`0 ≤ idx < size`) depends only on the index arithmetic and
            // the size oracle, never on array *contents*. So for an IndexSite, drop content-quantifier
            // conjuncts (`xs.every { … }`) from the assumed facts: it's sound (fewer hypotheses), and it
            // keeps Z3 out of the quantifier+NIA path that makes it bail on the flat-index monotonicity.
            // Phase 108 — but a *content-dependent* index (`b[a[k]]`, where the index `a[k]` itself reads an
            // array) is bounded only by the value-range quantifier (`∀q. 0 ≤ a[q] < b.length`), so stripping it
            // would discard the one fact that proves the bound. Keep quantifiers for those (the no-loop path
            // already does); the arithmetic-index case (`a[i*m+j]`) still strips, avoiding the NIA dead-end.
            boolean stripQ = (site instanceof IndexSite) && !indexReadsArrayContent(((IndexSite) site).index)
            if (reqAst != null) {
                Object p = enc.translate(stripQ ? dropQuantifierConjuncts(reqAst) : reqAst)
                if (p != null) s.assertExpr(p)
            }
            // Phase 15a — class invariants are method-entry facts, in scope across the loop's
            // prefix/guard/body/suffix regions just like @Requires.
            assumeIntJvmBounds(s, enc)
            assumeClassInvariants(s, enc)
            if (assumePos != null) {
                for (Expression e : assumePos) {
                    Object h = enc.translate(stripQ ? dropQuantifierConjuncts(e) : e)
                    if (h != null) s.assertExpr(h)
                }
            }
            if (assumeNeg != null) {
                Object h = enc.translate(assumeNeg)
                if (h != null) s.assertExpr(s.not(h))
            }
            try {
                LoopEncoder.symExec(preceding, enc, s)
            } catch (UnsupportedConstructException ignored) {
                // Can't model the preceding statements → leave those vars havoc (sound).
            }
            // Phase 91b — NIA monotonicity hint for array-index bounds (e.g. a flat `a[i*m + j]` fill,
            // where the bound `i*m + j < a.length` needs `i*m + m <= n*m` from `i < n ∧ m >= 0`, which Z3's
            // nonlinear tactic won't derive). Emit guarded ground lemmas for products that share a factor.
            if (site instanceof IndexSite) {
                List<Expression> ctx = new ArrayList<Expression>()
                if (reqAst != null) ctx.add(reqAst)
                if (assumePos != null) ctx.addAll(assumePos)
                ctx.add(((IndexSite) site).index)
                emitMonotonicityLemmas(s, enc, ctx)
            }
            dischargeObligationUnder(s, enc, site)
        } finally {
            try { s.close() } catch (Throwable ignored) {}
        }
    }

    /**
     * Phase 91b — give Z3 the one nonlinear stepping stone it can't find on its own: multiplying an
     * inequality by a non-negative factor. For every pair of product terms in the obligation's context
     * that share a factor `r` (`p*r` and `q*r`), assert the guarded ground facts
     * {@code (p ≤ q ∧ 0 ≤ r) ⟹ p*r ≤ q*r} and {@code (p < q ∧ 0 ≤ r) ⟹ p*r + r ≤ q*r} (both orderings).
     * Each is universally true, so asserting it is *sound* — it can only help the UNSAT (proof) direction.
     * Built from the original AST so the product terms unify (by Z3 hash-consing) with those in the goal.
     * Scoped to this obligation's solver session, and only when ≥ 2 products actually share a factor, so
     * it doesn't perturb the rest of the suite.
     */
    private void emitMonotonicityLemmas(SmtSession s, Encoder enc, List<Expression> exprs) {
        List<BinaryExpression> prods = new ArrayList<BinaryExpression>()
        for (Expression e : exprs) collectProducts(e, prods)
        if (prods.isEmpty()) return
        Set<String> emitted = new HashSet<String>()
        // Sign: `(0 ≤ p ∧ 0 ≤ r) ⟹ 0 ≤ p*r` — needed for the *lower* bound `0 ≤ i*m + j`.
        for (BinaryExpression pr : prods) {
            if (emitted.add('sign|' + pr.text)) assertSign(s, enc, pr.leftExpression, pr.rightExpression)
        }
        // Monotonicity across products sharing a factor — for the *upper* bound.
        for (int a = 0; a < prods.size(); a++) {
            for (int b = a + 1; b < prods.size(); b++) {
                Expression[] pqr = sharedFactor(prods.get(a), prods.get(b))
                if (pqr == null) continue
                Expression p = pqr[0], q = pqr[1], r = pqr[2]
                if (p.text == q.text) continue                       // same product → trivial
                String key = 'mono|' + ([p.text, q.text].sort() as List).join('|') + '|' + r.text
                if (!emitted.add(key)) continue
                assertMonotone(s, enc, p, q, r, true);  assertMonotone(s, enc, q, p, r, true)
                assertMonotone(s, enc, p, q, r, false); assertMonotone(s, enc, q, p, r, false)
            }
        }
    }

    /** Assert {@code (0 ≤ p ∧ 0 ≤ r) ⟹ 0 ≤ p*r} (a product of non-negatives is non-negative). */
    private void assertSign(SmtSession s, Encoder enc, Expression p, Expression r) {
        Expression zero = new ConstantExpression(Integer.valueOf(0))
        Expression body = bin(zero, Types.COMPARE_LESS_THAN_EQUAL, bin(p, Types.MULTIPLY, r))
        Expression guard = bin(bin(zero, Types.COMPARE_LESS_THAN_EQUAL, p), Types.LOGICAL_AND,
            bin(zero, Types.COMPARE_LESS_THAN_EQUAL, r))
        assertTrueFact(s, enc, bin(new NotExpression(guard), Types.LOGICAL_OR, body))
    }

    /** Collect MULTIPLY sub-expressions (not into quantifier closures — those products are out of scope). */
    private static void collectProducts(Expression e, List<BinaryExpression> out) {
        if (e == null) return
        if (e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e
            if (be.operation.type == Types.MULTIPLY) out.add(be)
            collectProducts(be.leftExpression, out)
            collectProducts(be.rightExpression, out)
        } else if (e instanceof BooleanExpression) {
            collectProducts(((BooleanExpression) e).expression, out)
        } else if (e instanceof NotExpression) {
            collectProducts(((NotExpression) e).expression, out)
        }
    }

    /** If two products share a factor, return {@code [otherFactorOf1, otherFactorOf2, sharedFactor]}. */
    private static Expression[] sharedFactor(BinaryExpression p1, BinaryExpression p2) {
        Expression a1 = p1.leftExpression, b1 = p1.rightExpression
        Expression a2 = p2.leftExpression, b2 = p2.rightExpression
        if (b1.text == b2.text) return [a1, a2, b1] as Expression[]
        if (a1.text == a2.text) return [b1, b2, a1] as Expression[]
        if (a1.text == b2.text) return [b1, a2, a1] as Expression[]
        if (b1.text == a2.text) return [a1, b2, b1] as Expression[]
        null
    }

    /** Assert {@code (p <op> q ∧ 0 ≤ r) ⟹ (p*r [+ r if strict] ≤ q*r)} as {@code ¬guard ∨ body} (true). */
    private void assertMonotone(SmtSession s, Encoder enc, Expression p, Expression q, Expression r, boolean strict) {
        Expression pr = bin(p, Types.MULTIPLY, r)
        Expression qr = bin(q, Types.MULTIPLY, r)
        Expression lhs = strict ? bin(pr, Types.PLUS, r) : pr
        Expression body = bin(lhs, Types.COMPARE_LESS_THAN_EQUAL, qr)
        Expression cmp = bin(p, strict ? Types.COMPARE_LESS_THAN : Types.COMPARE_LESS_THAN_EQUAL, q)
        Expression guard = bin(cmp, Types.LOGICAL_AND,
            bin(new ConstantExpression(Integer.valueOf(0)), Types.COMPARE_LESS_THAN_EQUAL, r))
        assertTrueFact(s, enc, bin(new NotExpression(guard), Types.LOGICAL_OR, body))
    }

    private void assertTrueFact(SmtSession s, Encoder enc, Expression lemma) {
        try {
            Object h = enc.translate(lemma)
            if (h != null) s.assertExpr(h)
        } catch (Throwable ignored) {}
    }

    private static BinaryExpression bin(Expression l, int type, Expression r) {
        new BinaryExpression(l, Token.newSymbol(type, -1, -1), r)
    }

    // ── Phase 118 — dataflow desugaring ─────────────────────────────────────────────────────────
    /** Rewrite a body using `DataflowVariable`/`<<`/`await`/`async` into plain single-assignment code; returns
     *  the same body unchanged if it uses none of them. */
    private static Statement desugarDataflow(Statement body) {
        if (!(body instanceof BlockStatement)) return body
        Set<String> df = new HashSet<String>()
        collectDataflowVars((BlockStatement) body, df)
        if (df.isEmpty()) return body
        List<Statement> out = new ArrayList<Statement>()
        rewriteDfStatements(((BlockStatement) body).statements, df, out)
        new BlockStatement(out, ((BlockStatement) body).variableScope)
    }

    private static void collectDataflowVars(BlockStatement body, Set<String> df) {
        body.visit(new CodeVisitorSupport() {
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (de.leftExpression instanceof VariableExpression && isDataflowNew(de.rightExpression)) {
                    df.add(((VariableExpression) de.leftExpression).name)
                }
                super.visitDeclarationExpression(de)
            }
        })
    }

    private static boolean isDataflowNew(Expression e) {
        if (!(e instanceof ConstructorCallExpression)) return false
        String n = ((ConstructorCallExpression) e).type?.nameWithoutPackage
        n == 'DataflowVariable' || n == 'Dataflows'
    }

    private static boolean isDfVarRef(Expression e, Set<String> df) {
        e instanceof VariableExpression && df.contains(((VariableExpression) e).name)
    }

    /** The single closure argument of an `async { … }` call (MethodCall or static), else null. */
    private static ClosureExpression asyncClosure(Expression e) {
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

    private static void rewriteDfStatements(List<Statement> stmts, Set<String> df, List<Statement> out) {
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
    private static Expression rewriteDfExpr(Expression e, Set<String> df) {
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

    // ── Phase 119 — async-channel pipeline desugaring ───────────────────────────────────────────
    /** Rewrite an `AsyncChannel` pipeline into the composed per-element transform; returns the body unchanged
     *  if it builds no channel. A source channel becomes a write-once scalar (`src.send(x)` is `src = x`); a
     *  `map { f }` stage is the pure transform `f` applied to the upstream value; receiving one element
     *  (`first()`) is a read. The pipeline collapses to function composition — FIFO ordering (the i-th value
     *  received is the i-th sent) is the structural half we assume. Pipeline-derived vars are resolved lazily
     *  at the receive site, so a producer in a trailing `async {}` still binds the right (post-send) value. */
    private static Statement desugarChannels(Statement body) {
        if (!(body instanceof BlockStatement)) return body
        Set<String> ch = new HashSet<String>()
        collectChannelVars((BlockStatement) body, ch)
        if (ch.isEmpty()) return body
        List<Statement> out = new ArrayList<Statement>()
        Map<String, Expression> defs = new HashMap<String, Expression>()
        rewriteChStatements(((BlockStatement) body).statements, ch, defs, out)
        new BlockStatement(out, ((BlockStatement) body).variableScope)
    }

    /** A var is a channel var if declared from `AsyncChannel.create(...)` or from a pipeline op whose source is
     *  already a channel var. Single forward pass — declarations are in source order. */
    private static void collectChannelVars(BlockStatement body, Set<String> ch) {
        body.visit(new CodeVisitorSupport() {
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (de.leftExpression instanceof VariableExpression &&
                    (isChannelCreate(de.rightExpression) || isChannelExpr(de.rightExpression, ch))) {
                    ch.add(((VariableExpression) de.leftExpression).name)
                }
                super.visitDeclarationExpression(de)
            }
        })
    }

    /** `AsyncChannel.create(...)` — interface static factory, either AST shape (post-STC static call, or a
     *  method call on a class/property reference named {@code AsyncChannel}). */
    private static boolean isChannelCreate(Expression e) {
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

    private static String channelOwnerName(Expression obj) {
        if (obj instanceof ClassExpression) return ((ClassExpression) obj).type?.nameWithoutPackage
        if (obj instanceof PropertyExpression) return ((PropertyExpression) obj).propertyAsString
        if (obj instanceof VariableExpression) return ((VariableExpression) obj).name
        null
    }

    /** A channel-valued expression: a channel var, or a pipeline op (`map`/`filter`/`tap`) on one. */
    private static boolean isChannelExpr(Expression e, Set<String> ch) {
        if (e instanceof VariableExpression) return ch.contains(((VariableExpression) e).name)
        if (e instanceof MethodCallExpression) {
            MethodCallExpression m = (MethodCallExpression) e
            return (m.methodAsString in ['map', 'filter', 'tap']) && isChannelExpr(m.objectExpression, ch)
        }
        false
    }

    private static void rewriteChStatements(List<Statement> stmts, Set<String> ch, Map<String, Expression> defs, List<Statement> out) {
        for (Statement st : stmts) {
            if (st instanceof BlockStatement) { rewriteChStatements(((BlockStatement) st).statements, ch, defs, out); continue }
            if (st instanceof ExpressionStatement) {
                Expression e = ((ExpressionStatement) st).expression
                ClosureExpression cl = asyncClosure(e)                       // async { … } → flatten inline (transparent)
                if (cl != null) {
                    if (cl.code instanceof BlockStatement) rewriteChStatements(((BlockStatement) cl.code).statements, ch, defs, out)
                    continue
                }
                if (e instanceof MethodCallExpression) {
                    MethodCallExpression m = (MethodCallExpression) e
                    if (isChannelExpr(m.objectExpression, ch) && m.methodAsString == 'close') continue   // close → drop
                    if (isChannelExpr(m.objectExpression, ch) && m.methodAsString == 'send') {            // send(v) → ch = v
                        List<Expression> a = (m.arguments instanceof ArgumentListExpression) ?
                            ((ArgumentListExpression) m.arguments).expressions : Collections.<Expression>emptyList()
                        if (a.size() == 1) {
                            out.add(new ExpressionStatement(bin(m.objectExpression, Types.ASSIGN, rewriteChExpr(a.get(0), ch, defs))))
                            continue
                        }
                    }
                }
                if (e instanceof DeclarationExpression && ((DeclarationExpression) e).leftExpression instanceof VariableExpression) {
                    DeclarationExpression de = (DeclarationExpression) e
                    String name = ((VariableExpression) de.leftExpression).name
                    if (isChannelCreate(de.rightExpression)) {              // def src = AsyncChannel.create(n) → def src = 0
                        VariableExpression lhs = new VariableExpression(name)
                        out.add(new ExpressionStatement(new DeclarationExpression(lhs, de.operation, new ConstantExpression(Integer.valueOf(0)))))
                        continue
                    }
                    if (isChannelExpr(de.rightExpression, ch)) {           // def out = src.map{..} → record pipeline, defer
                        defs.put(name, de.rightExpression)
                        continue
                    }
                }
                out.add(new ExpressionStatement(rewriteChExpr(e, ch, defs)))
                continue
            }
            if (st instanceof ReturnStatement) {
                Expression r = ((ReturnStatement) st).expression
                out.add(new ReturnStatement(r == null ? r : rewriteChExpr(r, ch, defs)))
                continue
            }
            out.add(st)
        }
    }

    /** Resolve a channel-valued expression to its scalar value: expand a pipeline-derived var to its recorded
     *  definition, beta-reduce each `map { f }` over its upstream value, and drop `first()`/receive reads. */
    private static Expression rewriteChExpr(Expression e, Set<String> ch, Map<String, Expression> defs) {
        if (e == null) return e
        ExpressionTransformer t = new ExpressionTransformer() {
            @Override Expression transform(Expression expr) {
                if (expr instanceof VariableExpression && defs.containsKey(((VariableExpression) expr).name)) {
                    return transform(defs.get(((VariableExpression) expr).name))         // expand derived var lazily
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
                    if (m.methodAsString == 'first' && isChannelExpr(m.objectExpression, ch) && noArgs(m)) {
                        return transform(m.objectExpression)                              // receive one element
                    }
                }
                expr.transformExpression(this)
            }
        }
        t.transform(e)
    }

    private static ClosureExpression singleClosureArg(MethodCallExpression m) {
        if (!(m.arguments instanceof ArgumentListExpression)) return null
        List<Expression> a = ((ArgumentListExpression) m.arguments).expressions
        (a.size() == 1 && a.get(0) instanceof ClosureExpression) ? (ClosureExpression) a.get(0) : null
    }

    /** β-reduce a single-expression closure `{ p -> body }` over {@code arg}: substitute the closure's parameter
     *  (or implicit `it`) with {@code arg} in {@code body}. Returns null for an unsupported (multi-statement) shape. */
    private static Expression betaReduce(ClosureExpression cl, Expression arg) {
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

    /** Drop the top-level `&&` conjuncts of {@code e} that contain a quantifier (`every`/`any`/closure);
     *  the rest are re-AND'd (or {@code true} if all were quantified). Used to keep array-bounds discharges
     *  quantifier-free — their truth never depends on array contents. */
    /**
     * Phase 108 — does this index expression read array *content* (a nested subscript like `a[k]` in
     * `b[a[k]]`)? Such an index's bound depends on the value stored, i.e. on a content quantifier, so the
     * Phase-91b quantifier-strip (sound for pure arithmetic indices) must not apply to it.
     */
    private static boolean indexReadsArrayContent(Expression e) {
        if (e == null) return false
        boolean[] found = new boolean[1]
        e.visit(new CodeVisitorSupport() {
            @Override void visitBinaryExpression(BinaryExpression be) {
                if (be.operation.type == Types.LEFT_SQUARE_BRACKET) found[0] = true
                super.visitBinaryExpression(be)
            }
        })
        found[0]
    }

    private static Expression dropQuantifierConjuncts(Expression e) {
        List<Expression> kept = new ArrayList<Expression>()
        for (Expression c : splitConjuncts(e)) if (!hasQuantifier(c)) kept.add(c)
        if (kept.isEmpty()) return new ConstantExpression(Boolean.TRUE)
        Expression r = kept.get(0)
        for (int i = 1; i < kept.size(); i++) r = bin(r, Types.LOGICAL_AND, kept.get(i))
        r
    }
    private static List<Expression> splitConjuncts(Expression e) {
        // NotExpression IS-A BooleanExpression: unwrapping it would DROP THE NEGATION — the Phase-205
        // else-guard soundness bug (an else-branch obligation was discharged under the positive guard).
        if (e instanceof NotExpression) return [(Expression) e]
        if (e instanceof BooleanExpression) return splitConjuncts(((BooleanExpression) e).expression)
        if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.LOGICAL_AND) {
            BinaryExpression be = (BinaryExpression) e
            List<Expression> out = new ArrayList<Expression>(splitConjuncts(be.leftExpression))
            out.addAll(splitConjuncts(be.rightExpression))
            return out
        }
        [e]
    }
    /** Quantifier- or aggregation-bearing: an `every`/`any`/closure, or an aggregation call
     *  (`sum`/`product`/`count`/`min`/`max`/`inject`) — all of which pull a *quantified axiom*
     *  (the `sum$`/`prod$`/… base+step) into the solver. An array-index bound never depends on a
     *  collection's contents *or* its aggregate, so such conjuncts are dropped from a bounds discharge
     *  (Phase 91b), which keeps Z3 out of the quantifier+NIA path it bails on. `size`/`length` are NOT
     *  here — a bound legitimately uses them. */
    private static final Set<String> AGG_METHODS =
        ['every','any','sum','product','count','min','max','inject'] as Set
    private static boolean hasQuantifier(Expression e) {
        boolean[] found = [false] as boolean[]
        e.visit(new CodeVisitorSupport() {
            @Override void visitClosureExpression(ClosureExpression ce) { found[0] = true }
            @Override void visitMethodCallExpression(MethodCallExpression mce) {
                if (AGG_METHODS.contains(mce.methodAsString)) found[0] = true
                super.visitMethodCallExpression(mce)
            }
        })
        found[0]
    }

    private List<Object> sitesInStatement(Statement st) {
        ObligationCollector col = new ObligationCollector()
        col.overflowChecking = currentOverflowChecking
        try { if (st != null) st.visit(col) } catch (Throwable ignored) {}
        return combineSites(col)
    }

    private List<Object> sitesInExpression(Expression e) {
        ObligationCollector col = new ObligationCollector()
        col.overflowChecking = currentOverflowChecking
        try { if (e != null) e.visit(col) } catch (Throwable ignored) {}
        return combineSites(col)
    }

    private static List<Object> combineSites(ObligationCollector col) {
        List<Object> r = new ArrayList<Object>()
        r.addAll(col.indexSites); r.addAll(col.divideSites); r.addAll(col.derefSites)
        r.addAll(col.overflowSites); r.addAll(col.stringCharAtSites)
        r.addAll(col.stringSubstringSites); r.addAll(col.parseSites)
        return r
    }

    @CompileStatic private static class IndexSite  { ASTNode node; String receiver; Expression index }
    /** A user {@code assert P} — its own obligation is the predicate {@code cond} itself. */
    @CompileStatic private static class AssertSite { ASTNode node; Expression cond }
    // requirePositive: Groovy's a.mod(b) (BigInteger.mod) throws unless b > 0; the `%`/`/`/intdiv/
    // remainder forms only require b != 0.
    @CompileStatic private static class DivideSite { ASTNode node; Expression divisor; boolean requirePositive = false }
    /** Phase 54 — {@code Integer.parseInt(arg)}: the implicit obligation that {@code arg} is a valid
     *  integer numeral (else {@code NumberFormatException}). */
    @CompileStatic private static class ParseSite { ASTNode node; Expression arg }

    /** True if {@code e} refers to the {@code Integer} class (any of the three AST shapes). */
    @CompileStatic
    private static boolean isIntegerClassRef(Expression e) {
        (e instanceof VariableExpression && ((VariableExpression) e).name == 'Integer') ||
        (e instanceof PropertyExpression && ((PropertyExpression) e).propertyAsString == 'Integer') ||
        (e instanceof ClassExpression && ((ClassExpression) e).type?.nameWithoutPackage == 'Integer')
    }
    /**
     * Phase 46e — character-index bounds: the implicit obligation {@code 0 <= i < s.length()}
     * at an {@code s.charAt(i)} site. Modelled separately from {@link IndexSite} because the
     * upper bound is the string length oracle ({@code stringLength(s)}) rather than a list's
     * {@code sizeOf} — the two share the "indexed access" shape but the size source differs.
     */
    @CompileStatic private static class StringCharAtSite {
        ASTNode node
        String receiver
        Expression indexExpr
    }

    /**
     * Phase 47 — substring bounds: at an {@code s.substring(begin, end)} call, the implicit
     * obligation {@code 0 <= begin && begin <= end && end <= s.length()} is asserted as one
     * conjunctive check. Single-argument {@code s.substring(begin)} uses
     * {@code 0 <= begin <= s.length()} (with {@code endExpr == null} marking that shape).
     */
    @CompileStatic private static class StringSubstringSite {
        ASTNode node
        String receiver
        Expression beginExpr
        Expression endExpr   // null = single-arg substring(begin)
    }
    /**
     * A method-call dereference site to be discharged via the nullity oracle. Two shapes:
     * - Scalar receiver ({@code recv.method()}): {@code indexExpr} is null; nullity comes from {@code nullityOf(receiver)}.
     * - Indexed receiver ({@code xs[i].method()} / {@code xs.get(i).method()}, Phase 37):
     *   {@code indexExpr} is non-null; nullity comes from {@code select(elementNullityFor(receiver), idx) == 1}.
     */
    @CompileStatic private static class DerefSite  {
        ASTNode node
        String receiver
        String method
        Expression indexExpr   // null = scalar deref; non-null = indexed (Phase 37)
    }

    /**
     * Phase 44 — a binary arithmetic operation whose result must stay in {@code [INT_MIN, INT_MAX]}
     * under {@code @CheckOverflow}. Sub-expressions are collected too, so {@code (a + b) * c} yields
     * one site for {@code a + b} and one for the outer product.
     */
    @CompileStatic private static class OverflowSite {
        ASTNode node
        Expression left
        Expression right
        String op       // "+", "-", "*"
        String text     // pretty-printed for the diagnostic, e.g. "(count + 1)"
    }

    /**
     * Walks a method body once, collecting the implicit-precondition sites:
     * array/list subscripts, integer division/modulo, and instance-method
     * dereferences on a named local/parameter receiver. Static calls, {@code this}
     * receivers, and calls on non-variable receivers are skipped — they are either
     * provably non-null or out of the spike's reach.
     */
    @CompileStatic
    private static class ObligationCollector extends ClassCodeVisitorSupport {
        final List<IndexSite> indexSites = []
        final List<DivideSite> divideSites = []
        final List<ParseSite> parseSites = []
        final List<DerefSite> derefSites = []
        /** Phase 44 — populated only when the enclosing method/class carries {@code @CheckOverflow}. */
        final List<OverflowSite> overflowSites = []
        /** Phase 46e — collected at every {@code charAt(i)} call shape (string-typing checked at discharge). */
        final List<StringCharAtSite> stringCharAtSites = []
        /** Phase 47 — collected at every {@code substring(...)} call shape (string-typing checked at discharge). */
        final List<StringSubstringSite> stringSubstringSites = []
        /**
         * Phase 44 — gates {@link OverflowSite} collection. The walking pass still descends into
         * sub-expressions so nested {@code a + b * c} arithmetic generates one site per operation;
         * disabling this flag makes the overflow check a no-op without affecting bounds/null/div
         * collection.
         */
        boolean overflowChecking = false

        @Override
        protected SourceUnit getSourceUnit() { null }

        @Override
        void visitBinaryExpression(BinaryExpression be) {
            // Match by operator text rather than token id: the parser assigns `%`
            // a token outside the Types.MOD constant, so text is the robust key.
            String sym = be.operation.text
            if (be.operation.type == Types.LEFT_SQUARE_BRACKET &&
                be.leftExpression instanceof VariableExpression) {
                indexSites.add(new IndexSite(node: be,
                    receiver: ((VariableExpression) be.leftExpression).name,
                    index: be.rightExpression))
            } else if (sym == '/' || sym == '%') {
                // Phase 152 — a JSR 385 `quantity / quantity` dispatches to Quantity.divide, NOT numeric division, so
                // the divisor is a quantity (not a number that could be 0): no divide-by-zero obligation. The exact-
                // division soundness for the magnitude is handled by the reader's terminating-divisor guard instead.
                if (!Encoder.packsClaimExpression(be)) divideSites.add(new DivideSite(node: be, divisor: be.rightExpression))
            }
            // Phase 44 — overflow check on +, -, * (only when enabled by @CheckOverflow). The
            // assignment operator '=' shares Types.PLUS via compound assignment in some forms, so
            // the check is operator-text gated rather than type-gated for robustness.
            if (overflowChecking && (sym == '+' || sym == '-' || sym == '*')) {
                overflowSites.add(new OverflowSite(node: be,
                    left: be.leftExpression, right: be.rightExpression, op: sym, text: be.text))
            }
            // Phase 44b-div — division overflow: {@code Integer.MIN_VALUE / -1} is the *only*
            // arithmetic case where {@code /} overflows (the math result is 2^31, one past
            // INT_MAX). Asserted as the specific input pair rather than computed via a math
            // {@code div}, because {@code SmtSession} doesn't expose integer division (the encoder
            // treats {@code /} via the NIA opt-out + divide-by-zero check). {@code %} is unaffected —
            // Java specifies {@code Integer.MIN_VALUE % -1 == 0}.
            if (overflowChecking && sym == '/') {
                overflowSites.add(new OverflowSite(node: be,
                    left: be.leftExpression, right: be.rightExpression, op: 'div', text: be.text))
            }
            super.visitBinaryExpression(be)
        }

        @Override
        void visitUnaryMinusExpression(UnaryMinusExpression ue) {
            // Phase 44b-neg — unary {@code -a} overflows when {@code a == Integer.MIN_VALUE}
            // (the math negation {@code 2147483648} is one past INT_MAX). Same OverflowSite
            // pipeline as the binary cases; {@code right == null} marks the unary shape.
            if (overflowChecking) {
                overflowSites.add(new OverflowSite(node: ue,
                    left: ue.expression, right: null, op: 'neg', text: ue.text))
            }
            super.visitUnaryMinusExpression(ue)
        }

        @Override
        void visitMethodCallExpression(MethodCallExpression mce) {
            Expression recv = mce.objectExpression
            // Groovy integer-division / modulo method forms: the obligation is on the divisor, not
            // the (numeric, non-null-tracked) receiver — so collect a DivideSite and skip the deref/
            // index synthesis below. intdiv/remainder require b != 0; mod requires b > 0.
            String mm = mce.methodAsString
            List<Expression> dargs = mce.arguments instanceof ArgumentListExpression ?
                ((ArgumentListExpression) mce.arguments).expressions : Collections.<Expression>emptyList()
            if (dargs.size() == 1 && (mm == 'intdiv' || mm == 'remainder' || mm == 'mod')) {
                divideSites.add(new DivideSite(node: mce, divisor: dargs.get(0), requirePositive: mm == 'mod'))
                super.visitMethodCallExpression(mce)
                return
            }
            // Integer.parseInt(arg): the arg must be a valid numeral (else NumberFormatException).
            if (dargs.size() == 1 && mm == 'parseInt' && isIntegerClassRef(recv)) {
                parseSites.add(new ParseSite(node: mce, arg: dargs.get(0)))
                super.visitMethodCallExpression(mce)
                return
            }
            if (!mce.implicitThis && recv instanceof VariableExpression) {
                VariableExpression v = (VariableExpression) recv
                Variable accessed = v.accessedVariable
                // Only real value variables (parameters / locals) — never a class
                // name (static call) or an unresolved dynamic reference.
                boolean realVar = accessed instanceof Parameter || accessed instanceof VariableExpression
                // Phase 124 — a primitive-typed receiver (e.g. `int n`) is never null: `n.toString()` autoboxes
                // but cannot NPE, so it carries no nullity obligation (and no collection index site).
                ClassNode recvType = accessed != null ? accessed.getType() : null
                boolean primitiveRecv = recvType != null && ClassHelper.isPrimitiveType(recvType)
                if (realVar && !primitiveRecv && v.name != 'this' && v.name != 'super') {
                    derefSites.add(new DerefSite(node: mce, receiver: v.name, method: mce.methodAsString))
                    // Phase 39 — synthesize an IndexSite for method-form indexed reads so the
                    // bounds check fires the same way it does for the bracket form. xs.get(i)
                    // lifts the arg directly; xs.first()/xs.head() use literal 0. xs.last()'s
                    // index is sizeOf-1 — not synthesised as an Expression here; users guard with
                    // {@code xs.size() > 0} and the @Ensures-driven check covers correctness.
                    // Phase 40 — same trick for removeLast()/pop(): the implicit precondition
                    // {@code xs.size() > 0} maps to IndexSite(xs, 0), so pop-on-empty refutes with
                    // the standard bounds-check diagnostic.
                    synthIndexSiteFor(mce, v.name)
                } else if (accessed instanceof FieldNode && v.name != 'this' && v.name != 'super') {
                    // Phase 43 — instance field receiver: synthesise the IndexSite for the
                    // runtime-throwing shapes only ({@code get(i)}, {@code first()}, {@code head()},
                    // {@code removeLast()}, {@code pop()}). Do NOT add a DerefSite: existing tests
                    // that mutate set/map/list fields ({@code s.add(x)}, {@code m.put(k,v)},
                    // {@code xs.add(v)}) don't declare {@code @Requires({ field != null })}, so
                    // adding a scalar nullity obligation here would regress them. The bounds
                    // check on a field's runtime-throwing read still fires — pop-on-empty
                    // refutes uniformly whether xs is a parameter or a field.
                    synthIndexSiteFor(mce, v.name)
                }
            } else if (!mce.implicitThis) {
                // Phase 37 — xs[i].method() and xs.get(i).method() shapes. The dereference target
                // is the element value at idx, with the per-element nullity oracle as the obligation.
                Encoder.IndexedNullTarget ind = Encoder.indexedAccessTarget(recv)
                if (ind != null) {
                    derefSites.add(new DerefSite(
                        node: mce, receiver: ind.containerName,
                        method: mce.methodAsString, indexExpr: ind.indexExpr))
                }
            }
            super.visitMethodCallExpression(mce)
        }

        /**
         * Shared IndexSite synthesis for indexed-read shapes ({@code .get(i)}, {@code .first()},
         * {@code .head()}, {@code .removeLast()}, {@code .pop()}) on a named receiver. The
         * runtime-throwing variants (first/head/removeLast/pop) map to {@code IndexSite(name, 0)};
         * {@code .get(i)} lifts the arg expression. Used by both the parameter-receiver branch
         * (Phase 39/40) and the field-receiver branch (Phase 43).
         */
        private void synthIndexSiteFor(MethodCallExpression mce, String name) {
            String mName = mce.methodAsString
            List<Expression> margs = mce.arguments instanceof ArgumentListExpression ?
                ((ArgumentListExpression) mce.arguments).expressions :
                Collections.<Expression>emptyList()
            if (mName == 'get' && margs.size() == 1) {
                indexSites.add(new IndexSite(node: mce, receiver: name, index: margs.get(0)))
            } else if ((mName == 'first' || mName == 'head' ||
                        mName == 'removeLast' || mName == 'pop' ||
                        mName == 'max' || mName == 'min') && margs.isEmpty()) {
                // first/head/pop and the witnessed extrema max()/min() all throw on an empty receiver
                // (UnsupportedOperationException for max/min), so the receiver must be provably non-empty —
                // the same `0 < size` obligation as a `[0]` read, synthesised as IndexSite(name, 0).
                indexSites.add(new IndexSite(node: mce, receiver: name, index: new ConstantExpression(0)))
            } else if (mName == 'charAt' && margs.size() == 1) {
                // Phase 46e — {@code s.charAt(i)} on a parameter / field. String vs list
                // discrimination happens at discharge: a {@code List<Character>} doesn't have
                // a {@code charAt} method (Groovy's {@code String.charAt} only — list reads use
                // {@code get(i)}), so any {@code charAt} call shape that reaches here came
                // from a String-typed receiver in practice.
                stringCharAtSites.add(new StringCharAtSite(
                    node: mce, receiver: name, indexExpr: margs.get(0)))
            } else if (mName == 'substring' && (margs.size() == 1 || margs.size() == 2)) {
                // Phase 47 — bounds: 0 <= begin (<= end)? <= length(s).
                stringSubstringSites.add(new StringSubstringSite(
                    node: mce, receiver: name, beginExpr: margs.get(0),
                    endExpr: margs.size() == 2 ? margs.get(1) : null))
            }
        }
    }

    /**
     * Discharge a method's own {@code @Ensures} postcondition
     * against its body. Enumerate the body's execution paths and, for
     * each, ask Z3 whether {@code pathFacts ∧ ¬postcondition} is
     * satisfiable — a model is a return on which the postcondition fails.
     */
    private void verifyPostcondition(MethodNode node) {
        AnnotationNode ens = findEnsures(node)
        // Phase 15a — class invariants on the declaring class behave like an extra exit obligation
        // for non-static methods. So we now run even when there's no @Ensures, provided the class
        // carries an invariant. The pre-filtered list lives in {@link #currentClassInvariants}.
        List<Expression> classInvs = currentClassInvariants
        // Phase 131 — a @NonNull return is an implicit postcondition `result != null`. NullChecker only
        // *asserts* it (flow-level); groovy-verify can *prove* it (value-level), catching returns that are null
        // for reasons flow analysis can't follow. Conjoined into the postcondition below.
        boolean nnReturn = hasNonNullReturn(node)

        if (ens == null && classInvs.isEmpty() && !nnReturn) return
        if (node.code == null) return

        Expression postAst = ens != null ? contractAstFor(node, 'ensures') : null
        if (ens != null && postAst == null) {
            addStaticTypeError(
                Reporter.formatPostconditionSkipped(node.name,
                    "contract source was not captured by ContractExpansionTransform"),
                node)
            return
        }
        if (nnReturn) {
            Expression nn = parseContract('result != null')
            if (nn != null) {
                postAst = (postAst == null) ? nn : (parseContract("(${postAst.text}) && (result != null)") ?: postAst)
            }
        }

        // A method may use its own @Requires as an entry assumption.
        AnnotationNode reqOwn = findRequires(node)
        Expression reqAst = reqOwn != null ? contractAstFor(node, 'requires') : null

        try {
            // Prefer the clean body snapshot taken at CONVERSION; by now
            // groovy-contracts has rewritten node.code in place.
            Statement body = (Statement) node.getNodeMetaData(
                ContractExpansionTransform.ORIGINAL_BODY_KEY)
            if (body == null) body = node.code
            // A constructor has no return value (it implicitly produces `this`); treat its body
            // as void-shaped for path enumeration — paths terminate without a return expression.
            List<Path> paths = BodyEncoder.enumeratePaths(body, node.isVoidMethod() || node instanceof ConstructorNode)
            for (Path p : paths) {
                checkPath(node, p, postAst, reqAst, classInvs)
            }
        } catch (UnsupportedConstructException e) {
            addStaticTypeError(
                Reporter.formatPostconditionSkipped(node.name, e.message), node)
        }
    }

    // ---- Phase L1: information flow — static-label noninterference (no-leak) ----------------------

    /**
     * Discharge the noninterference obligation for a method that declares an output security classification
     * via {@code @Label}. For each {@code return e}, the security level of {@code e} — {@code ΓE(e)}, the join
     * of the labels of the sources flowing into it (plus the program-counter label) — must not exceed the
     * result's classification: {@code leq(join(ΓE(e), PC), L(result))}. The goal is synthesised as a lattice
     * expression over the class's own {@code leq}/{@code join} and discharged by the same Z3 backend; a high
     * value reaching a low result refutes. Slice 1 covers static labels over straight-line code, local
     * Γ-threading (1b) and branch PC / implicit flow (1c); arrays, loops and value-dependent classifications
     * are later slices, and an unlabelled/unsupported source skips loudly.
     *
     * <p>The analysis is a syntax-directed walk (the paper's framing) carrying a {@code Γ} environment
     * (variable → security level, as a lattice AST) and a {@code PC} label (the join of the levels of the
     * guards enclosing the current point). Unlike a flat path enumeration, the recursive walk scopes the PC to
     * its branch, so post-{@code if} code does not inherit it. Branch joins merge the two arms' environments by
     * lattice join. This subsumes the straight-line case (no guards ⇒ {@code PC = ⊥}).
     */
    private void verifyNoLeak(MethodNode node) {
        if (node instanceof ConstructorNode) return
        String outLevel = labelValue(node)                 // result classification (may be null — e.g. a void sink-caller)
        boolean anyLabel = outLevel != null
        for (Parameter p : node.parameters) {
            if (labelValue(p) != null || labelBy(p) != null) { anyLabel = true; break }
        }
        if (!anyLabel && node.declaringClass != null) {    // a labelled FIELD (e.g. an array's element label) a sink call could read
            for (FieldNode f : node.declaringClass.fields) if (labelValue(f) != null || labelBy(f) != null) { anyLabel = true; break }
        }
        if (!anyLabel) return                              // nothing labelled → not in the information-flow analysis
        ClassNode lat = latticeEnumOf(node)
        if (lat == null) {
            // A labelled *result* method clearly intends in-class analysis, so a missing lattice is flagged; a
            // params-only method (a sink declaration consumed by callers elsewhere) is left alone — its class
            // need not carry the lattice.
            if (outLevel != null) {
                addStaticTypeError(Reporter.formatLeakSkipped(node.name,
                    "no security lattice (a same-class enum-valued leq/join/meet) is in scope"), node)
            }
            return
        }
        Statement body = (Statement) node.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (body == null) body = node.code
        if (body == null) return
        Map<String, Expression> env = new LinkedHashMap<String, Expression>()
        for (Parameter p : node.parameters) {              // each labelled parameter → its classification (constant or value-dependent)
            Expression g = paramClassification(p, node, lat)
            if (g != null) env.put(p.name, g)
        }
        ifFacts = new ArrayList<Object[]>()                // path conditions assumed at discharge (value-dependent levels)
        arrayElemGamma = new HashMap<String, Expression>()
        try {
            ifWalk(body, env, null, lat, outLevel, node)   // PC starts at ⊥ (null)
        } catch (UnsupportedConstructException ex) {
            addStaticTypeError(Reporter.formatLeakSkipped(node.name, ex.message), node)
        } finally {
            ifFacts = new ArrayList<Object[]>()
            arrayElemGamma = new HashMap<String, Expression>()
        }
    }

    // ==================== Phase 131 C₀ kind-vector pass — migrated to UnitsPack.checkMethod (Phase 190) ====================

    /** Path conditions (each {@code [Expression cond, Boolean positive]}) enclosing the current walk point —
     *  assumed when discharging a value-dependent classification so it resolves under the branch. */
    private List<Object[]> ifFacts = new ArrayList<Object[]>()

    /** Γ of the value last written to an array element, keyed {@code "arr[indexText]"} — so a control-field update
     *  that reclassifies that element (the §III-A array secure-update) can check the held value is within its new
     *  level. Cleared at branch boundaries (only straight-line writes are tracked; a branched write → untracked). */
    private Map<String, Expression> arrayElemGamma = new HashMap<String, Expression>()

    /**
     * Syntax-directed information-flow walk. Carries {@code env} (variable → Γ level) and {@code pc} (the
     * program-counter label, null = ⊥), emitting a no-leak obligation at each {@code return} and returning the
     * environment after {@code s}. Throws {@link UnsupportedConstructException} for a construct outside the
     * fragment (loops, switch, …) so the caller skips loudly.
     */
    private Map<String, Expression> ifWalk(Statement s, Map<String, Expression> env, Expression pc,
                                           ClassNode lat, String outLevel, MethodNode node) {
        if (s == null || s instanceof EmptyStatement) return env
        if (s instanceof BlockStatement) {
            Map<String, Expression> cur = env
            for (Statement st : ((BlockStatement) s).statements) {
                cur = ifWalk(st, cur, pc, lat, outLevel, node)
            }
            return cur
        }
        if (s instanceof ReturnStatement) {
            Expression e = ((ReturnStatement) s).expression
            if (e != null) {
                checkCallSinks(e, env, pc, lat, node)          // a call in the return expr, e.g. return sink(secret)
                if (outLevel != null) emitReturnLeak(node, e, env, pc, lat, outLevel)
            }
            return env
        }
        if (s instanceof AssertStatement) {
            // A synthesised post-write invariant assert (the @UnderRely masking fix) carries no information flow —
            // it neither reaches a sink nor rebinds Γ. Scan its condition for a sink, then treat it as a no-op.
            checkCallSinks(((AssertStatement) s).booleanExpression, env, pc, lat, node)
            return env
        }
        if (s instanceof IfStatement) {
            IfStatement ifs = (IfStatement) s
            Expression cond = ifs.booleanExpression
            // Array-element classifications are only tracked across straight-line writes; a branch makes the held
            // value position-uncertain, so forget them (a later secure-update then loud-skips rather than unsoundly
            // trusting a one-arm write).
            arrayElemGamma.clear()
            checkCallSinks(cond, env, pc, lat, node)       // a call in the guard
            // Branching on classified data raises the PC inside both arms (implicit flow): PC ⊔ ΓE(guard).
            Expression pcInner = pcJoin(pc, gammaExpr(cond, env, lat))
            // Push the guard as a path condition so a value-dependent classification resolves under the branch;
            // pop on exit so it is scoped (mirrors the PC). The else arm carries its negation.
            ifFacts.add([cond, Boolean.TRUE] as Object[])
            Map<String, Expression> thenEnv
            try { thenEnv = ifWalk(ifs.ifBlock, copyEnv(env), pcInner, lat, outLevel, node) }
            finally { ifFacts.remove(ifFacts.size() - 1) }
            Statement elseBlk = ifs.elseBlock
            Map<String, Expression> elseEnv
            if (elseBlk != null && !(elseBlk instanceof EmptyStatement)) {
                ifFacts.add([cond, Boolean.FALSE] as Object[])
                try { elseEnv = ifWalk(elseBlk, copyEnv(env), pcInner, lat, outLevel, node) }
                finally { ifFacts.remove(ifFacts.size() - 1) }
            } else {
                elseEnv = copyEnv(env)
            }
            return mergeEnvs(thenEnv, elseEnv)             // post-if: join the arms; PC is popped (not pcInner)
        }
        if (s instanceof ExpressionStatement) {
            Expression stmtExpr = ((ExpressionStatement) s).expression
            if (handleRelyStep(stmtExpr, node)) return env     // a synthesised rely-step: havoc interfered slots, no flow
            checkCallSinks(stmtExpr, env, pc, lat, node)       // a bare sink call, or one in an assignment RHS
            // An array store `arr[idx] = x`: record the element's data classification so a later control-field
            // update that reclassifies it (the §III-A array secure-update) can check the held value is in range.
            if (recordArrayStore(stmtExpr, env, pc, lat)) return env
            String[] nameHolder = new String[1]
            Expression rhs = assignTarget(stmtExpr, nameHolder)
            if (nameHolder[0] != null) {
                // §III-A secure-update: if the target is a control variable (read by a value-dependent
                // classification), changing it must not leave a controlled variable holding data above its NEW
                // classification. Checked against the pre-assignment Γ of each controlled variable.
                checkSecureUpdate(nameHolder[0], rhs, env, lat, node)
                checkArraySecureUpdate(nameHolder[0], rhs, lat, node)   // §III-A over array elements (boundary element)
                Map<String, Expression> ne = copyEnv(env)
                Expression g = gammaExpr(rhs, env, lat)
                // An assignment under a non-⊥ PC raises the target to at least the PC (implicit flow). An
                // untracked RHS un-binds the target (a later return on it skips loudly).
                if (g == null) ne.remove(nameHolder[0]) else ne.put(nameHolder[0], pcJoin(g, pc))
                return ne
            }
            return env                                     // a non-assigning statement expression: no flow effect
        }
        if (s instanceof WhileStatement || s instanceof DoWhileStatement || s instanceof ForStatement) {
            arrayElemGamma.clear()                          // loop bodies re-run: positions are uncertain (see above)
            return walkLoop(s, env, pc, lat, outLevel, node)
        }
        throw new UnsupportedConstructException(
            "a ${s.getClass().simpleName} is outside the information-flow fragment (straight-line + if/else + loops)")
    }

    /**
     * Information-flow over a loop. The security level of a variable assigned in the loop is raised to the join
     * of every tracked source the body (and guard) touches, plus the loop's PC — a sound <i>Γ-invariant</i>
     * inferred automatically (over the finite level lattice, the level of a loop-carried variable is bounded by
     * that join, an upper bound for every iteration, so no user-written invariant is needed). Obligations inside
     * the body are then discharged once under that raised environment, and the post-loop environment is it too.
     * Conservative but sound: a variable assigned only low values in a loop that <i>also</i> touches a secret is
     * raised — a per-variable fixpoint would be tighter, a later refinement. A {@code for}-each over a collection
     * (element labels not yet modelled) skips loudly.
     */
    private Map<String, Expression> walkLoop(Statement s, Map<String, Expression> env, Expression pc,
                                             ClassNode lat, String outLevel, MethodNode node) {
        if (s instanceof ForStatement && !(((ForStatement) s).collectionExpression instanceof ClosureListExpression)) {
            throw new UnsupportedConstructException("a for-each loop is outside the information-flow fragment")
        }
        Statement body = ((LoopingStatement) s).loopBlock
        Expression guard = loopGuard(s)
        checkCallSinks(guard, env, pc, lat, node)
        Expression pcLoop = pcJoin(pc, gammaExpr(guard, env, lat))   // the guard raises the PC inside the loop

        // The loop's Γ-effect: which variables it assigns, and the join of every tracked level it touches.
        Set<String> assigned = new LinkedHashSet<String>()
        List<Expression> srcLevels = new ArrayList<Expression>()
        collectLoopEffect(body, env, assigned, srcLevels)
        Expression bodyLevel = pcLoop
        for (Expression lvl : srcLevels) bodyLevel = pcJoin(bodyLevel, lvl)

        Map<String, Expression> newEnv = copyEnv(env)
        for (String a : assigned) {
            if (bodyLevel == null) newEnv.remove(a)             // a loop over no tracked data → assigned vars untracked
            else newEnv.put(a, pcJoin(newEnv.get(a), bodyLevel))
        }

        // One obligation-emitting pass over the body under the raised (invariant) environment; the loop guard
        // holds inside, so push it as a path condition for value-dependent classifications.
        boolean pushed = guard != null
        if (pushed) ifFacts.add([guard, Boolean.TRUE] as Object[])
        try {
            ifWalk(body, newEnv, pcLoop, lat, outLevel, node)
        } finally {
            if (pushed) ifFacts.remove(ifFacts.size() - 1)
        }
        return newEnv                                           // post-loop: the loop may have run any number of times
    }

    /** The loop guard: the {@code while}/{@code do-while} condition, or the {@code cond} of a C-style {@code for}; null otherwise. */
    private static Expression loopGuard(Statement s) {
        if (s instanceof WhileStatement) return ((WhileStatement) s).booleanExpression
        if (s instanceof DoWhileStatement) return ((DoWhileStatement) s).booleanExpression
        if (s instanceof ForStatement) {
            Expression col = ((ForStatement) s).collectionExpression
            if (col instanceof ClosureListExpression) {
                List<Expression> parts = ((ClosureListExpression) col).expressions
                if (parts.size() == 3) return parts.get(1)
            }
        }
        null
    }

    /** Collect the names a loop body assigns, and the (entry) Γ levels of every tracked variable it mentions. */
    private void collectLoopEffect(Statement body, Map<String, Expression> env,
                                   Set<String> assigned, List<Expression> srcLevels) {
        Set<String> mentioned = new LinkedHashSet<String>()
        body.visit(new CodeVisitorSupport() {
            @Override void visitVariableExpression(VariableExpression v) { mentioned.add(v.name) }
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                for (VariableExpression v : declaredTargets(de)) assigned.add(v.name)
                super.visitDeclarationExpression(de)
            }
            @Override void visitBinaryExpression(BinaryExpression be) {
                if (be.operation.type == Types.ASSIGN && be.leftExpression instanceof VariableExpression) {
                    assigned.add(((VariableExpression) be.leftExpression).name)
                }
                super.visitBinaryExpression(be)
            }
        })
        for (String n : mentioned) {
            Expression lvl = env.get(n)
            if (lvl != null) srcLevels.add(lvl)
        }
    }

    /**
     * §III-A secure-update obligation. When {@code assignedName := rhs} assigns a **control variable** — one
     * read by some parameter's value-dependent classification {@code @Label(by = 'm')} — every variable it
     * controls must still hold data within its <i>new</i> classification: {@code leq( Γ(y), L_y[control := rhs] )},
     * where {@code L_y[control := rhs]} is the classification method called with {@code rhs} substituted for the
     * control argument. This catches "flip the flag to make a field public while it still holds a secret": the
     * classification becomes lower while the held data does not, so a value previously legitimately High is
     * suddenly over a Low classification. Discharged under the path conditions, like the other obligations.
     */
    private void checkSecureUpdate(String assignedName, Expression rhs, Map<String, Expression> env,
                                   ClassNode lat, MethodNode node) {
        ClassNode dc = node.declaringClass
        if (dc == null) return
        for (Parameter y : node.parameters) {
            String by = labelBy(y)
            if (by == null) continue
            Expression gammaY = env.get(y.name)
            if (gammaY == null) continue                    // the controlled variable is untracked → nothing to check
            for (MethodNode m : dc.getMethods(by)) {        // its classification method (first overload)
                boolean controls = false
                List<Expression> args = new ArrayList<Expression>()
                for (Parameter cp : m.parameters) {
                    if (cp.name == assignedName) { controls = true; args.add(rhs) }   // the new control value
                    else args.add(new VariableExpression(cp.name))
                }
                if (controls) {
                    Expression newClass = new MethodCallExpression(new VariableExpression('this'), by, new ArgumentListExpression(args))
                    dischargeSecureUpdate(node, assignedName, y.name, rhs, sameClassCall('leq', gammaY, newClass))
                }
                break
            }
        }
    }

    /** Record the data classification of the value stored by an array element write {@code arr[idx] = x} into
     *  {@link #arrayElemGamma}, keyed {@code "arr[idxText]"}. Returns true iff {@code e} is such a store. */
    private boolean recordArrayStore(Expression e, Map<String, Expression> env, Expression pc, ClassNode lat) {
        if (!(e instanceof BinaryExpression) || ((BinaryExpression) e).operation.type != Types.ASSIGN) return false
        BinaryExpression asgn = (BinaryExpression) e
        if (!(asgn.leftExpression instanceof BinaryExpression)) return false
        BinaryExpression lhs = (BinaryExpression) asgn.leftExpression
        if (lhs.operation.type != Types.LEFT_SQUARE_BRACKET || !(lhs.leftExpression instanceof VariableExpression)) return false
        String key = ((VariableExpression) lhs.leftExpression).name + '[' + lhs.rightExpression.text + ']'
        Expression gx = gammaExpr(asgn.rightExpression, env, lat)
        arrayElemGamma.put(key, gx == null ? null : pcJoin(gx, pc))
        return true
    }

    /**
     * §III-A secure-update over array elements. When {@code control := rhs} bumps a control field that some
     * array's element label {@code @Label(by = 'm')} reads, the element at position {@code control} (the boundary
     * slot — e.g. {@code values[tail]} as {@code tail} advances) is reclassified. It is secure only if the value
     * it holds is within its NEW level: {@code leq( Γ(arr[control]), m(control, …, rhs) )}. The held level is what
     * a preceding {@code arr[control] = x} wrote (tracked in {@link #arrayElemGamma}); with no tracked write, the
     * slot's data is within its CURRENT label level {@code m(control, …current…)} (the info-flow invariant — every
     * slot satisfies its own label), so that is the sound fallback. This makes a control-advance that pushes the
     * slot to a HIGHER level (e.g. consuming: {@code head++} sends {@code values[head]} from Low to High) verify
     * without a write, while still refuting a real downgrade of an unwritten (conservatively classified) slot.
     */
    private void checkArraySecureUpdate(String control, Expression rhs, ClassNode lat, MethodNode node) {
        ClassNode dc = node.declaringClass
        if (dc == null) return
        for (FieldNode arr : dc.fields) {
            String by = labelBy(arr)
            if (by == null) continue
            for (MethodNode m : dc.getMethods(by)) {
                if (m.parameters.length < 1) break
                boolean controls = false                                  // a non-index param named `control`?
                for (int k = 1; k < m.parameters.length; k++) if (m.parameters[k].name == control) controls = true
                if (!controls) break
                String key = arr.name + '[' + control + ']'
                // the boundary slot's new classification: m(control, …, rhs) — control param ↦ rhs (the post value)
                Expression newClass = labelCallAt(m, by, control, rhs)
                // its held level: a tracked write, else its current label level m(control, …current…) (pre-update)
                Expression gammaElem = arrayElemGamma.get(key)
                if (gammaElem == null) gammaElem = labelCallAt(m, by, control, new VariableExpression(control))
                dischargeSecureUpdate(node, control, key, rhs, sameClassCall('leq', gammaElem, newClass))
                break
            }
        }
    }

    /**
     * Account for a synthesised {@code @UnderRely} rely-step call {@code $rely$Role()} in the info-flow walk. The
     * step models the environment's interference: it havocs its {@code @Modifies} fields (subject to the rely
     * relation). Any array slot we are tracking whose key references a havoced field could now denote a *different*
     * slot, so forget it — sound under interference. Fields the rely pins ({@code f == old.f} in its {@code @Ensures},
     * e.g. the producer's {@code tail}) are preserved, so {@code values[tail]} survives. Returns true iff a rely-step.
     */
    private boolean handleRelyStep(Expression stmtExpr, MethodNode node) {
        String mname = (stmtExpr instanceof MethodCallExpression) ? ((MethodCallExpression) stmtExpr).methodAsString : null
        if (mname == null || !mname.startsWith('$rely$')) return false
        ClassNode dc = node.declaringClass
        List<MethodNode> steps = (dc != null) ? dc.getMethods(mname) : null
        if (steps == null || steps.isEmpty()) { arrayElemGamma.clear(); return true }   // unknown frame → forget all
        Set<String> modified = modifiedNames(steps.get(0))
        if (modified == null) { arrayElemGamma.clear(); return true }
        Set<String> havoced = new HashSet<String>(modified)
        havoced.removeAll(pinnedFields(steps.get(0)))                  // a pinned field (f == old.f) is not really havoced
        if (havoced.isEmpty()) return true
        Iterator<Map.Entry<String, Expression>> it = arrayElemGamma.entrySet().iterator()
        while (it.hasNext()) {
            String k = it.next().key
            for (String f : havoced) if (k =~ ('\\b' + java.util.regex.Pattern.quote(f) + '\\b')) { it.remove(); break }
        }
        return true
    }

    /** Fields a rely-step's {@code @Ensures} pins unchanged — every {@code f == old.f} conjunct (either order). */
    private Set<String> pinnedFields(MethodNode step) {
        Set<String> out = new HashSet<String>()
        Expression ens = contractAstFor(step, 'ensures')
        if (ens == null) return out
        ens.visit(new CodeVisitorSupport() {
            @Override void visitBinaryExpression(BinaryExpression b) {
                if (b.operation.type == Types.COMPARE_EQUAL) {
                    String f = pinnedPair(b.leftExpression, b.rightExpression)
                    if (f == null) f = pinnedPair(b.rightExpression, b.leftExpression)
                    if (f != null) out.add(f)
                }
                super.visitBinaryExpression(b)
            }
        })
        out
    }

    /** If {@code a} is a bare name {@code f} and {@code b} is {@code old.f}, that field name; else null. */
    private static String pinnedPair(Expression a, Expression b) {
        if (!(a instanceof VariableExpression) || !(b instanceof PropertyExpression)) return null
        String name = ((VariableExpression) a).name
        PropertyExpression p = (PropertyExpression) b
        (p.objectExpression instanceof VariableExpression && ((VariableExpression) p.objectExpression).name == 'old'
            && p.propertyAsString == name) ? name : null
    }

    /** A value-dependent label call {@code m(control, …)} over the boundary slot at index {@code control}; the
     *  control param is bound to {@code controlVal} (the post value {@code rhs} for the new level, or the field
     *  itself for the current level), every other control param to its own field name. */
    private Expression labelCallAt(MethodNode m, String by, String control, Expression controlVal) {
        List<Expression> args = new ArrayList<Expression>()
        args.add(new VariableExpression(control))                         // index = boundary position (the control value)
        for (int k = 1; k < m.parameters.length; k++) {
            args.add(m.parameters[k].name == control ? controlVal : new VariableExpression(m.parameters[k].name))
        }
        new MethodCallExpression(new VariableExpression('this'), by, new ArgumentListExpression(args))
    }

    /** Refute the secure-update obligation; VERIFIED ⇒ the control-variable assignment is secure, else a leak. */
    private void dischargeSecureUpdate(MethodNode node, String controlVar, String controlled, Expression rhs, Expression goal) {
        SmtSession session = backend.session()
        try {
            Encoder enc = mkEncoder(session)
            // The secure-update level may depend on the method's @Requires / class invariant (e.g. a buffer's
            // `head <= tail` makes the boundary element's new level Low); assume them, plus the branch conditions.
            assumePreAndInvariants(session, enc, node)
            assumeIfFacts(session, enc)
            Object g = enc.translateGoal(goal)
            if (g == null) {
                addStaticTypeError(Reporter.formatLeakSkipped(node.name,
                    "secure-update obligation '${goal.text}' is outside fragment"), anchorOf(rhs, node))
                return
            }
            session.assertExpr(session.not(g))
            CheckResult r = shown(session.check())
            if (r.status == CheckResult.Status.VERIFIED) return
            addStaticTypeError(
                Reporter.formatSecureUpdate(node.name, controlVar, controlled, r), anchorOf(rhs, node))
        } finally {
            try { session.close() } catch (Throwable ignored) {}
        }
    }

    /** Emit the no-leak obligation for a {@code return e} under environment {@code env} and program counter {@code pc}. */
    private void emitReturnLeak(MethodNode node, Expression e, Map<String, Expression> env, Expression pc,
                               ClassNode lat, String outLevel) {
        Expression gamma = gammaExpr(e, env, lat)
        if (gamma == null) {
            addStaticTypeError(Reporter.formatLeakSkipped(node.name,
                "return expression '${e.text}' draws on an unlabelled or unsupported source"), anchorOf(e, node))
            return
        }
        Expression level = pcJoin(gamma, pc)               // the returned value is observed under the PC
        Expression goal = sameClassCall('leq', level, enumConstExpr(lat, outLevel))
        dischargeLeak(node, e, goal, outLevel)
    }

    /**
     * Interprocedural sink check (Phase L1, interprocedural slice). For every same-class call inside {@code e},
     * each argument flowing to a {@code @Label}-classified parameter must not exceed that parameter's
     * classification: {@code leq( join(ΓE(arg), PC), L(param) )}. This is the "a secret reaching a public sink"
     * shape (a query/log/response argument) — the dual of a taint checker's "tainted value reaching an
     * untrusted sink". Calls with no labelled parameter (e.g. the lattice's own {@code leq}/{@code join}) are
     * ignored; a labelled sink fed an untracked argument skips loudly.
     */
    private void checkCallSinks(Expression e, Map<String, Expression> env, Expression pc, ClassNode lat, MethodNode node) {
        if (e == null) return
        List<Expression> calls = new ArrayList<Expression>()
        e.visit(new CodeVisitorSupport() {
            @Override void visitMethodCallExpression(MethodCallExpression c) { calls.add(c); super.visitMethodCallExpression(c) }
            @Override void visitStaticMethodCallExpression(StaticMethodCallExpression c) { calls.add(c); super.visitStaticMethodCallExpression(c) }
        })
        for (Expression c : calls) {
            MethodNode callee = resolveSinkCallee(c, node)
            if (callee == null) continue                   // not a resolvable call → nothing to check
            List<Expression> args = callArgs(c)
            Parameter[] ps = callee.parameters
            if (args == null || ps.length != args.size()) continue   // arity mismatch / varargs → skip
            for (int i = 0; i < ps.length; i++) {
                String plabel = labelValue(ps[i])
                if (plabel == null) continue               // unlabelled parameter — not a sink
                Expression arg = args.get(i)
                Expression argGamma = gammaExpr(arg, env, lat)
                if (argGamma == null) {
                    addStaticTypeError(Reporter.formatLeakSkipped(node.name,
                        "argument '${arg.text}' to the '${plabel}' parameter '${ps[i].name}' of ${callee.name} " +
                        "draws on an unlabelled or unsupported source"), anchorOf(arg, node))
                    continue
                }
                Expression level = pcJoin(argGamma, pc)    // the argument is passed under the current PC
                Expression goal = sameClassCall('leq', level, enumConstExpr(lat, plabel))
                dischargeSinkLeak(node, arg, callee.name, ps[i].name, plabel, goal)
            }
        }
    }

    /** Refute the no-leak obligation for one sink argument; VERIFIED ⇒ secure, else a leak into the sink parameter. */
    private void dischargeSinkLeak(MethodNode node, Expression arg, String callee, String paramName,
                                   String paramLevel, Expression goal) {
        SmtSession session = backend.session()
        try {
            Encoder enc = mkEncoder(session)
            assumePreAndInvariants(session, enc, node)      // @Requires + class invariant (e.g. head <= tail makes the slot Low)
            assumeIfFacts(session, enc)                     // assume the enclosing branch conditions (value-dependent levels)
            Object g = enc.translateGoal(goal)
            if (g == null) {
                addStaticTypeError(Reporter.formatLeakSkipped(node.name,
                    "sink obligation '${goal.text}' is outside fragment"), anchorOf(arg, node))
                return
            }
            session.assertExpr(session.not(g))
            CheckResult r = shown(session.check())
            if (r.status == CheckResult.Status.VERIFIED) return
            addStaticTypeError(
                Reporter.formatSinkLeak(node.name, arg.text, callee, paramName, paramLevel, r), anchorOf(arg, node))
        } finally {
            try { session.close() } catch (Throwable ignored) {}
        }
    }

    /** Assume the method's {@code @Requires} and the class invariant into an info-flow discharge session. A
     *  value-dependent classification (e.g. a buffer's region label {@code level(i, head, tail)}) is often only
     *  resolvable under them — `head <= tail` is what makes the boundary slot {@code Low}. Best-effort. */
    private void assumePreAndInvariants(SmtSession session, Encoder enc, MethodNode node) {
        Expression reqAst = findRequires(node) != null ? contractAstFor(node, 'requires') : null
        if (reqAst != null) { Object pre = enc.translateBool(reqAst); if (pre != null) { session.assertExpr(pre); captureExplain(session, enc, reqAst, pre) } }
        assumeClassInvariants(session, enc)
    }

    /** Assume each enclosing path condition (a guard, possibly negated) into the discharge session, so a
     *  value-dependent classification {@code L_x(controls…)} resolves under the branch it sits in. Best-effort:
     *  a guard the encoder can't translate is simply not assumed (sound — fewer assumptions, never a false pass). */
    private void assumeIfFacts(SmtSession session, Encoder enc) {
        for (Object[] fact : ifFacts) {
            Object c = enc.translate((Expression) fact[0])
            if (c == null) continue
            session.assertExpr(((Boolean) fact[1]) ? c : session.not(c))
        }
    }

    /**
     * Resolve a call to its callee {@link MethodNode} — same-class (implicit-{@code this} / {@code this.m(…)})
     * or **cross-class**. The receiver determines the target type: a {@code ClassExpression} ({@code Foo.m(…)}
     * post-resolution) or a {@link StaticMethodCallExpression} gives the owner directly; a bare
     * {@code VariableExpression} receiver is either an object parameter of known type ({@code log.m(…)}) or — in
     * the pre-resolution body snapshot — a class *name* ({@code Foo.m(…)} parses as {@code Var(Foo).m}), looked
     * up among the compilation unit's classes. A receiver that is none of these (an external/precompiled type we
     * can't resolve off the snapshot) returns null → the call is skipped.
     */
    private MethodNode resolveSinkCallee(Expression c, MethodNode caller) {
        ClassNode self = caller?.declaringClass
        if (self == null) return null
        ClassNode targetType = null
        String name
        if (c instanceof MethodCallExpression) {
            MethodCallExpression mce = (MethodCallExpression) c
            Expression recv = mce.objectExpression
            name = mce.methodAsString
            if (mce.implicitThis || (recv instanceof VariableExpression && ((VariableExpression) recv).name == 'this')) {
                targetType = self
            } else if (recv instanceof ClassExpression) {
                targetType = ((ClassExpression) recv).type
            } else if (recv instanceof VariableExpression) {
                String rn = ((VariableExpression) recv).name
                ClassNode pt = paramType(caller, rn)           // an instance receiver: the parameter's declared type
                targetType = (pt != null) ? pt : lookupClassInModule(self, rn)   // else a class name
            }
        } else if (c instanceof StaticMethodCallExpression) {
            StaticMethodCallExpression sce = (StaticMethodCallExpression) c
            targetType = sce.ownerType
            name = sce.method
        } else {
            return null
        }
        if (targetType == null || name == null) return null
        int arity = callArgs(c).size()
        for (MethodNode m : targetType.getMethods(name)) {
            if (m.parameters.length == arity) return m
        }
        null
    }

    /** The declared type of the parameter named {@code name} on {@code m}, or null. */
    private static ClassNode paramType(MethodNode m, String name) {
        if (m == null || name == null) return null
        for (Parameter p : m.parameters) {
            if (p.name == name) return p.type
        }
        null
    }

    /** A class with the given simple name in {@code from}'s compilation unit (same source / module), or null. */
    private static ClassNode lookupClassInModule(ClassNode from, String simpleName) {
        if (from == null || simpleName == null) return null
        if (from.nameWithoutPackage == simpleName) return from
        if (from.module != null) {
            for (ClassNode cn : from.module.classes) {
                if (cn.nameWithoutPackage == simpleName) return cn
            }
        }
        null
    }

    /** The positional argument expressions of a call (empty for none / non-positional). */
    private static List<Expression> callArgs(Expression c) {
        Expression a = (c instanceof MethodCallExpression) ? ((MethodCallExpression) c).arguments :
                       (c instanceof StaticMethodCallExpression) ? ((StaticMethodCallExpression) c).arguments : null
        (a instanceof ArgumentListExpression) ? ((ArgumentListExpression) a).expressions :
            Collections.<Expression> emptyList()
    }

    /** Lattice join of two levels, with null treated as ⊥ (identity): {@code a ⊔ b}. */
    private Expression pcJoin(Expression a, Expression b) {
        if (a == null) return b
        if (b == null) return a
        sameClassCall('join', a, b)
    }

    private static Map<String, Expression> copyEnv(Map<String, Expression> env) {
        new LinkedHashMap<String, Expression>(env)
    }

    /** Merge two branch environments: a variable defined (and tracked) on both arms takes the join of its levels;
     *  a variable tracked on only one arm becomes untracked after the join. */
    private Map<String, Expression> mergeEnvs(Map<String, Expression> a, Map<String, Expression> b) {
        Map<String, Expression> out = new LinkedHashMap<String, Expression>()
        for (Map.Entry<String, Expression> en : a.entrySet()) {
            Expression bv = b.get(en.key)
            if (bv == null) continue
            Expression av = en.value
            out.put(en.key, av.is(bv) ? av : sameClassCall('join', av, bv))
        }
        out
    }

    /** If {@code e} is {@code name = rhs} or {@code Type name = rhs}, set {@code holder[0]=name} and return the
     *  RHS; otherwise {@code holder[0]=null}. */
    private static Expression assignTarget(Expression e, String[] holder) {
        holder[0] = null
        if (e instanceof DeclarationExpression) {
            DeclarationExpression de = (DeclarationExpression) e
            if (de.leftExpression instanceof VariableExpression) {
                holder[0] = ((VariableExpression) de.leftExpression).name
                return de.rightExpression
            }
        } else if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.ASSIGN) {
            BinaryExpression be = (BinaryExpression) e
            if (be.leftExpression instanceof VariableExpression) {
                holder[0] = ((VariableExpression) be.leftExpression).name
                return be.rightExpression
            }
        }
        null
    }

    /** Refute {@code ¬goal} (the no-leak obligation) for one return path; VERIFIED ⇒ secure, else a leak. */
    private void dischargeLeak(MethodNode node, Expression returnExpr, Expression goal, String outLevel) {
        SmtSession session = backend.session()
        try {
            Encoder enc = mkEncoder(session)
            assumeIfFacts(session, enc)                    // assume the enclosing branch conditions (value-dependent levels)
            Object g = enc.translateGoal(goal)
            if (g == null) {
                addStaticTypeError(Reporter.formatLeakSkipped(node.name,
                    "security obligation '${goal.text}' is outside fragment"), anchorOf(returnExpr, node))
                return
            }
            session.assertExpr(session.not(g))
            CheckResult r = shown(session.check())
            if (r.status == CheckResult.Status.VERIFIED) return
            addStaticTypeError(
                Reporter.formatInformationLeak(node.name, returnExpr.text, outLevel, r),
                anchorOf(returnExpr, node))
        } finally {
            try { session.close() } catch (Throwable ignored) {}
        }
    }

    /** The security level of an expression, {@code ΓE(e)}, as a lattice AST — or null (skip) if any leaf source
     *  is unlabelled / unsupported. A variable contributes its current Γ from {@code gammaEnv} (a parameter's
     *  label or a local's threaded level); a compound expression joins its operands' levels. (Slice 1: literals
     *  yield null — a constant source is ⊥, deferred until the lattice's bottom is identified.) */
    private Expression gammaExpr(Expression e, Map<String, Expression> gammaEnv, ClassNode lat) {
        if (e instanceof BooleanExpression) {                     // an `if` guard arrives wrapped
            return gammaExpr(((BooleanExpression) e).expression, gammaEnv, lat)
        }
        String dLevel = declassifyLevel(e)                        // §III-E — an explicit `Declassify.to('Low', …)` release
        if (dLevel != null) return enumConstExpr(lat, dLevel)
        if (e instanceof VariableExpression) {
            return gammaEnv.get(((VariableExpression) e).name)   // null ⇒ untracked source
        }
        if (e instanceof BinaryExpression &&
            ((BinaryExpression) e).operation.type == Types.LEFT_SQUARE_BRACKET) {
            // An array access `arr[idx]`: its element classification is value-dependent on the POSITION and the
            // control fields — `@Label(by = 'm')` on the array, where `m`'s first parameter is the index and the
            // rest bind by name to the control fields (the array analogue of the scalar `@Label(by=)`). So
            // L(arr[idx]) = m(idx, <controls>); not a join of the array's and the index's own levels.
            BinaryExpression acc = (BinaryExpression) e
            if (acc.leftExpression instanceof VariableExpression) {
                MethodNode by = arrayElementLabelMethod(((VariableExpression) acc.leftExpression).name)
                if (by != null && by.parameters.length >= 1) {
                    List<Expression> args = new ArrayList<Expression>()
                    args.add(acc.rightExpression)                            // the index
                    for (int k = 1; k < by.parameters.length; k++) {
                        args.add(new VariableExpression(by.parameters[k].name))   // control fields by name
                    }
                    return new MethodCallExpression(new VariableExpression('this'), by.name, new ArgumentListExpression(args))
                }
            }
            return null                                              // unlabelled array access → untracked
        }
        if (e instanceof BinaryExpression) {
            BinaryExpression b = (BinaryExpression) e
            Expression gl = gammaExpr(b.leftExpression, gammaEnv, lat)
            Expression gr = gammaExpr(b.rightExpression, gammaEnv, lat)
            if (gl == null || gr == null) return null
            return sameClassCall('join', gl, gr)
        }
        null
    }

    /** For an array named {@code arrName} carrying {@code @Label(by = 'm')} (a position-dependent element label),
     *  the classification method {@code m}; null otherwise. Looks at the current method's parameters then its
     *  declaring class's fields. {@code m}'s first parameter is the index; the rest are control vars bound by name. */
    private MethodNode arrayElementLabelMethod(String arrName) {
        if (currentMethod == null) return null
        org.codehaus.groovy.ast.AnnotatedNode decl = null
        for (Parameter p : currentMethod.parameters) if (p.name == arrName) { decl = p; break }
        ClassNode dc = currentMethod.declaringClass
        if (decl == null && dc != null) for (FieldNode f : dc.fields) if (f.name == arrName) { decl = f; break }
        if (decl == null || dc == null) return null
        String by = labelBy(decl)
        if (by == null) return null
        List<MethodNode> ms = dc.getMethods(by)
        ms.isEmpty() ? null : ms.get(0)
    }

    /** If {@code e} is an explicit declassification {@code Declassify.to('Level', value)}, the released level
     *  name {@code 'Level'}; otherwise null. The released value's own level is deliberately discarded — that is
     *  the controlled release (§III-E). */
    private static String declassifyLevel(Expression e) {
        if (!(e instanceof MethodCallExpression)) return null
        MethodCallExpression mce = (MethodCallExpression) e
        if (mce.methodAsString != 'to') return null
        Expression recv = mce.objectExpression
        String rn = (recv instanceof VariableExpression) ? ((VariableExpression) recv).name :
                    (recv instanceof ClassExpression) ? recv.type?.nameWithoutPackage : null
        if (rn != 'Declassify') return null
        List<Expression> args = callArgs(mce)
        if (args.size() == 2 && args.get(0) instanceof ConstantExpression) {
            Object v = ((ConstantExpression) args.get(0)).value
            return v != null ? v.toString() : null
        }
        null
    }

    /** {@code @Label('X')} on a parameter/method/field → {@code 'X'}, or null. */
    /** The constant lattice-level name of a {@code @Label}'s {@code value} member, or null (absent/empty). */
    private static String labelValue(org.codehaus.groovy.ast.AnnotatedNode n) {
        return labelMember(n, 'value')
    }

    /** The classification-method name of a {@code @Label}'s {@code by} member (value-dependent), or null. */
    private static String labelBy(org.codehaus.groovy.ast.AnnotatedNode n) {
        return labelMember(n, 'by')
    }

    private static String labelMember(org.codehaus.groovy.ast.AnnotatedNode n, String member) {
        List<AnnotationNode> anns = n.getAnnotations(LABEL_TYPE)
        if (anns == null || anns.isEmpty()) return null
        Expression m = anns.get(0).getMember(member)
        if (m instanceof ConstantExpression) {
            Object v = ((ConstantExpression) m).value
            String s = v != null ? v.toString() : null
            return (s != null && !s.isEmpty()) ? s : null
        }
        null
    }

    /**
     * The classification of a labelled parameter as a lattice-level AST: a constant ({@code @Label('High')} →
     * {@code Lattice.High}) or a **value-dependent** call ({@code @Label(by = 'm')} → {@code m(controls…)}, where
     * each control argument is the in-scope variable matching the classification method's parameter name). Null
     * for an unlabelled parameter or an unresolvable {@code by} method.
     */
    private Expression paramClassification(Parameter p, MethodNode enclosing, ClassNode lat) {
        String v = labelValue(p)
        if (v != null) return enumConstExpr(lat, v)
        String by = labelBy(p)
        if (by == null) return null
        ClassNode dc = enclosing.declaringClass
        if (dc == null) return null
        for (MethodNode m : dc.getMethods(by)) {            // the classification method: control vars by parameter name
            List<Expression> ctrlArgs = new ArrayList<Expression>()
            for (Parameter cp : m.parameters) ctrlArgs.add(new VariableExpression(cp.name))
            return new MethodCallExpression(new VariableExpression('this'), by, new ArgumentListExpression(ctrlArgs))
        }
        null
    }

    /** The security lattice in scope: the (enum) type the class's binary {@code leq} ranges over, or null. */
    private static ClassNode latticeEnumOf(MethodNode node) {
        ClassNode dc = node.declaringClass
        if (dc == null) return null
        for (MethodNode m : dc.getMethods('leq')) {
            if (m.parameters.length == 2) {
                ClassNode t = m.parameters[0].type
                if (t != null && t.isEnum()) return t
            }
        }
        null
    }

    /** {@code Lattice.CONST} as a post-resolution property access (interns to the enum constant). */
    private static Expression enumConstExpr(ClassNode lat, String constName) {
        new PropertyExpression(new ClassExpression(lat), constName)
    }

    /** A same-class call {@code name(a, b)} (implicit-{@code this}), as the encoder's pure-function path expects. */
    private static Expression sameClassCall(String name, Expression a, Expression b) {
        new MethodCallExpression(new VariableExpression('this'), name,
            new ArgumentListExpression([a, b] as List<Expression>))
    }

    /** Anchor a diagnostic on a positioned expression when available, else the method node. */
    private static ASTNode anchorOf(Expression e, MethodNode node) {
        (e != null && e.lineNumber > 0) ? (ASTNode) e : (ASTNode) node
    }

    // ---- Phase 122: verify a trait's concrete default methods against the implementing class ----

    /**
     * A trait's *default* method is woven into a synthetic helper, never type-checked when only the
     * implementing class carries {@code @TypeChecked} — so its contract / invariant preservation went
     * unverified (a broken default method passed silently). Here, when visiting an implementing class, we
     * recover each trait default method's body from the CONVERSION snapshot stored on the trait method, rewrite
     * the woven field accessors (`((FieldHelper) $self).Trait__field$get()/$set(v)`) back to plain field
     * reads/writes, and verify the result *in the implementing class's context* — its fields and its effective
     * class invariant (which already includes the trait's, via the Phase-121 interface walk). The rewritten
     * body is exactly what the same logic written as a class method would be, so it rides the normal machinery.
     */
    private void verifyTraitDefaultMethods(ClassNode classNode) {
        if (classNode == null || classNode.isInterface() || classNode.interfaces == null) return
        for (ClassNode itf : classNode.interfaces) {
            if (!org.codehaus.groovy.transform.trait.Traits.isTrait(itf)) continue
            for (MethodNode m : itf.methods) {
                if (m.isStatic()) continue
                Statement snap = (Statement) m.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
                if (snap == null) continue                 // generated accessors / abstract methods: no snapshot
                Statement clean
                try {
                    clean = desugarTraitBody(snap)
                } catch (Throwable ignored) { continue }   // unsupported weaving shape → leave it alone
                if (clean == null) continue
                MethodNode synth = new MethodNode(m.name,
                    m.modifiers & ~Opcodes.ACC_ABSTRACT,
                    m.returnType, m.parameters, m.exceptions, clean)
                synth.declaringClass = classNode           // verify in the implementer's context
                synth.addAnnotations(m.getAnnotations())   // carry @ContractSource / @Requires / @Ensures
                synth.putNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY, clean)
                // A diagnostic anchored on a position-less MethodNode is silently dropped by STC; anchor the
                // synthetic node at the implementing class so a refutation actually surfaces.
                synth.setSourcePosition(classNode)
                try {
                    beforeVisitMethod(synth)
                    afterVisitMethod(synth)
                } catch (Throwable ignored) {
                }
            }
        }
    }

    /** Rewrite a woven trait-method body (`((FieldHelper) $self).Trait__f$get()` / `…$set(v)`) into plain
     *  `this`-relative field reads/writes the verifier already understands. */
    private static Statement desugarTraitBody(Statement body) {
        if (body instanceof BlockStatement) {
            List<Statement> out = new ArrayList<Statement>()
            for (Statement st : ((BlockStatement) body).statements) {
                Statement r = rewriteTraitStmt(st)
                if (r == null) return null
                out.add(r)
            }
            return new BlockStatement(out, ((BlockStatement) body).variableScope)
        }
        rewriteTraitStmt(body)
    }

    private static Statement rewriteTraitStmt(Statement st) {
        if (st instanceof BlockStatement) return desugarTraitBody(st)
        if (st instanceof ReturnStatement) {
            Expression r = ((ReturnStatement) st).expression
            return new ReturnStatement(r == null ? r : rewriteTraitGets(r))
        }
        if (st instanceof IfStatement) {
            IfStatement ifs = (IfStatement) st
            Expression cond = rewriteTraitGets(ifs.booleanExpression instanceof BooleanExpression ?
                ((BooleanExpression) ifs.booleanExpression).expression : ifs.booleanExpression)
            return new IfStatement(new BooleanExpression(cond),
                rewriteTraitStmt(ifs.ifBlock),
                ifs.elseBlock == null || ifs.elseBlock instanceof EmptyStatement ? ifs.elseBlock : rewriteTraitStmt(ifs.elseBlock))
        }
        if (st instanceof ExpressionStatement) {
            Expression e = ((ExpressionStatement) st).expression
            Expression u = unwrapCast(e)
            String[] setF = traitSetField(u)              // [fieldName] if a `…$set(v)` on $self
            if (setF != null) {
                Expression arg = traitSetArg(u)
                return new ExpressionStatement(bin(new VariableExpression(setF[0]), Types.ASSIGN, rewriteTraitGets(arg)))
            }
            return new ExpressionStatement(rewriteTraitGets(e))
        }
        st
    }

    /** Rewrite every `…$get()` field-accessor call on `$self` (possibly cast) to a bare field read. */
    private static Expression rewriteTraitGets(Expression e) {
        if (e == null) return e
        ExpressionTransformer t = new ExpressionTransformer() {
            @Override Expression transform(Expression expr) {
                String f = traitGetField(unwrapCast(expr))
                if (f != null) return new VariableExpression(f)
                expr.transformExpression(this)
            }
        }
        t.transform(e)
    }

    private static Expression unwrapCast(Expression e) {
        Expression x = e
        while (x instanceof CastExpression) x = ((CastExpression) x).expression
        x
    }

    /** True receiver of a trait field accessor: `$self`, possibly behind a cast. */
    private static boolean isSelfReceiver(Expression objExpr) {
        Expression o = unwrapCast(objExpr)
        o instanceof VariableExpression && ((VariableExpression) o).name == '$self'
    }

    /** The source field name for a `Trait__field$get`/`$set` accessor method name (drops the `Trait__` prefix). */
    private static String accessorField(String method, String suffix) {
        if (!method.endsWith(suffix)) return null
        String base = method.substring(0, method.length() - suffix.length())   // e.g. Counter__count
        int us = base.lastIndexOf('__')
        us >= 0 ? base.substring(us + 2) : base
    }

    /** If {@code e} is `$self.Trait__f$get()` (no args), the source field name {@code f}; else null. The woven
     *  accessor call carries a plain {@link TupleExpression} argument list (not an {@code ArgumentListExpression}). */
    private static String traitGetField(Expression e) {
        if (!(e instanceof MethodCallExpression)) return null
        MethodCallExpression m = (MethodCallExpression) e
        if (!isSelfReceiver(m.objectExpression)) return null
        if (!(m.arguments instanceof TupleExpression) || !((TupleExpression) m.arguments).expressions.isEmpty()) return null
        accessorField(m.methodAsString, '$get')
    }

    /** If {@code e} is `$self.Trait__f$set(v)`, the source field name (wrapped so callers can null-test); else null. */
    private static String[] traitSetField(Expression e) {
        if (!(e instanceof MethodCallExpression)) return null
        MethodCallExpression m = (MethodCallExpression) e
        if (!isSelfReceiver(m.objectExpression)) return null
        if (!(m.arguments instanceof TupleExpression) || ((TupleExpression) m.arguments).expressions.size() != 1) return null
        String f = accessorField(m.methodAsString, '$set')
        f != null ? ([f] as String[]) : null
    }

    private static Expression traitSetArg(Expression e) {
        ((TupleExpression) ((MethodCallExpression) e).arguments).expressions.get(0)
    }

    // ---- Phase 121: trait machinery recognition ----

    /** True for a synthetic trait-weaving method the verifier should leave alone: a static helper on a
     *  `…$Trait$Helper` class (carrying a `$self` receiver), or an implementing class's generated bridge that
     *  just delegates to one. These are produced after the clean-body snapshot, so they only yield noise. */
    private static boolean isTraitMachineryMethod(MethodNode node) {
        if (node == null) return false
        ClassNode dc = node.declaringClass
        if (dc != null && dc.name != null && dc.name.contains('$Trait$Helper')) return true
        Parameter[] ps = node.parameters
        if (ps != null && ps.length > 0 && ps[0].name == '$self') return true
        // An implementing class's trait bridge is synthetic and its source is a trait, not the class itself.
        if (node.isSynthetic() && dc != null && dc.interfaces != null) {
            for (ClassNode itf : dc.interfaces) {
                if (org.codehaus.groovy.transform.trait.Traits.isTrait(itf) &&
                    itf.getDeclaredMethod(node.name, node.parameters) != null) return true
            }
        }
        false
    }

    // ---- Phase 120: behavioral subtyping (Liskov substitution) ----

    /** The contracted method this one overrides, walking the superclass chain by name + parameter types. */
    private static MethodNode overriddenSuperMethod(MethodNode node) {
        if (node == null || node.isStatic() || node instanceof ConstructorNode) return null
        ClassNode dc = node.declaringClass
        if (dc == null) return null
        ClassNode sc = dc.superClass
        while (sc != null && sc != ClassHelper.OBJECT_TYPE) {
            MethodNode m = sc.getDeclaredMethod(node.name, node.parameters)
            if (m != null) return m
            sc = sc.superClass
        }
        null
    }

    /** Rename a parent contract's formal-parameter references to the child's names, by position (so both
     *  contracts read over one shared namespace). Returns null if the arities differ. */
    private static Expression alignParentParams(Expression parentContract, MethodNode parent, MethodNode child) {
        if (parentContract == null) return null
        Parameter[] pp = parent.parameters, cp = child.parameters
        if (pp.length != cp.length) return null
        Expression e = parentContract
        for (int i = 0; i < pp.length; i++) {
            if (pp[i].name != cp[i].name) e = renameVariable(e, pp[i].name, cp[i].name)
        }
        e
    }

    /**
     * Phase 120 — prove an override is a behavioral subtype of the method it overrides. Fires only when the
     * child *redeclares* a contract (an omitted clause is inherited verbatim, so it's trivially compatible).
     * Two SMT implication checks over the shared parameter/result namespace, independent of either body:
     *   - precondition weakening: pre_parent ⟹ pre_child   (the child must accept every call the parent did)
     *   - postcondition strengthening: (pre_parent ∧ post_child) ⟹ post_parent   (the child must promise ≥)
     * A satisfiable negation is a concrete substitutability counterexample.
     */
    private void verifyBehavioralSubtyping(MethodNode node) {
        MethodNode parent = overriddenSuperMethod(node)
        if (parent == null) return

        if (!node.getAnnotations(REQUIRES_TYPE).isEmpty()) {
            Expression childReq = contractAstFor(node, 'requires')
            // parent's effective precondition (null ⇒ `true`, i.e. accepts everything)
            Expression parentReq = parent.getAnnotations(REQUIRES_TYPE).isEmpty() ? null :
                alignParentParams(contractAstFor(parent, 'requires'), parent, node)
            if (childReq != null) {
                checkLspImplication(node, parentReq == null ? Collections.<Expression>emptyList() : [parentReq],
                    childReq, 'precondition', '@Requires must be weakened (or kept), never strengthened, in an override')
            }
        }

        if (!node.getAnnotations(ENSURES_TYPE).isEmpty() && !parent.getAnnotations(ENSURES_TYPE).isEmpty()) {
            Expression childEns = contractAstFor(node, 'ensures')
            Expression parentEns = alignParentParams(contractAstFor(parent, 'ensures'), parent, node)
            Expression parentReq = parent.getAnnotations(REQUIRES_TYPE).isEmpty() ? null :
                alignParentParams(contractAstFor(parent, 'requires'), parent, node)
            if (childEns != null && parentEns != null) {
                List<Expression> assume = new ArrayList<Expression>()
                if (parentReq != null) assume.add(parentReq)
                assume.add(childEns)
                checkLspImplication(node, assume, parentEns, 'postcondition',
                    '@Ensures must be strengthened (or kept), never weakened, in an override')
            }
        }
    }

    /** Assert the assumptions and the negated goal in a fresh session; a model (REFUTED) is an LSP violation. */
    private void checkLspImplication(MethodNode node, List<Expression> assume, Expression goal,
                                     String kind, String detail) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            for (Expression a : assume) {
                Object h = enc.translate(a)
                if (h == null) return            // outside fragment → can't judge soundly; stay silent
                s.assertExpr(h)
            }
            Object g = enc.translate(goal)
            if (g == null) return
            s.assertExpr(s.not(g))
            CheckResult r = shown(s.check())
            if (r.status == CheckResult.Status.REFUTED) {
                ConstantExpression proxy = new ConstantExpression(node.name)
                proxy.setSourcePosition((ASTNode) node)
                addStaticTypeError(Reporter.formatLspViolation(node.name, kind, detail, r), (ASTNode) proxy)
            }
        } catch (Throwable ignored) {
        } finally { try { s.close() } catch (Throwable ignored) {} }
    }

    /**
     * Drop class invariants that don't translate into the encoder fragment, emitting a single
     * "skipped" diagnostic per dropped clause. Sound: a missing entry-assumption only weakens
     * the context, and a missing exit-obligation makes one less thing to prove. Returns the
     * encodable subset, preserving order.
     */
    private List<Expression> filterEncodableInvariants(List<Expression> invs, MethodNode node) {
        if (invs == null || invs.isEmpty()) return invs ?: Collections.<Expression> emptyList()
        List<Expression> ok = new ArrayList<Expression>()
        SmtSession probe = backend.session()
        try {
            Encoder probeEnc = mkEncoder(probe)
            for (Expression inv : invs) {
                if (probeEnc.translate(inv) == null) {
                    addStaticTypeError(
                        Reporter.formatClassInvariantSkipped(node.name, inv.text), node)
                } else {
                    ok.add(inv)
                }
            }
        } finally {
            try { probe.close() } catch (Throwable ignored) {}
        }
        ok
    }

    /** Collect every variable name mentioned in {@code e} into {@code into}. */
    private static void collectVarNames(Expression e, Set<String> into) {
        if (e == null) return
        try {
            e.visit(new CodeVisitorSupport() {
                @Override void visitVariableExpression(VariableExpression v) { into.add(v.name) }
            })
        } catch (Throwable ignored) { }
    }

    /**
     * Phase 194 — demote-to-skip at the no-aliasing boundary (arrays). The model gives each array
     * parameter its own store: sound per-array, but a store through one parameter with ANOTHER
     * same-element-type array parameter read on the path (or in the postcondition) is proved under
     * "they are distinct arrays" — unsound for aliased actuals (`f(x, x)`), and invisible to the runtime
     * rung (its grid never aliases two actuals). Reads of the *stored* array itself stay sound (same
     * name, exact store model); a same-type sibling that is never read is unaffected. Loud skip.
     */
    private static void guardArrayAliasHazard(MethodNode node, Path p, Expression postAst) {
        Map<String, String> arrays = new LinkedHashMap<String, String>()   // array param -> element type
        for (Parameter par : node.parameters) {
            if (par.type != null && par.type.isArray()) arrays.put(par.name, par.type.componentType?.name)
        }
        if (arrays.size() < 2) return
        Set<String> stored = new LinkedHashSet<String>()
        for (Object st : p.steps) {
            if (st instanceof ArrayStore && arrays.containsKey(((ArrayStore) st).arr)) stored.add(((ArrayStore) st).arr)
        }
        if (stored.isEmpty()) return
        Set<String> mentioned = new HashSet<String>()
        collectVarNames(postAst, mentioned)
        collectVarNames(p.result, mentioned)
        for (Object st : p.steps) {
            if (st instanceof Assign) collectVarNames(((Assign) st).rhs, mentioned)
            else if (st instanceof Guard) collectVarNames(((Guard) st).cond, mentioned)
            else if (st instanceof ArrayStore) { collectVarNames(((ArrayStore) st).index, mentioned); collectVarNames(((ArrayStore) st).value, mentioned) }
            else if (st instanceof LemmaCall) collectVarNames(((LemmaCall) st).call, mentioned)
            else if (st instanceof AssertAssume) collectVarNames(((AssertAssume) st).cond, mentioned)
        }
        for (String pn : stored) {
            for (Map.Entry<String, String> other : arrays.entrySet()) {
                if (other.key != pn && other.value == arrays.get(pn) && mentioned.contains(other.key)) {
                    throw new UnsupportedConstructException(
                        "array parameters '${pn}' and '${other.key}' may alias — a store through '${pn}' " +
                        "with '${other.key}' read on the path is modelled as independent (heap aliasing is a non-goal)")
                }
            }
        }
    }

    private void checkPath(MethodNode node, Path p, Expression postAst, Expression reqAst,
                           List<Expression> classInvs) {
        SmtSession session = backend.session()
        try {
            guardArrayAliasHazard(node, p, postAst)
            Encoder enc = mkEncoder(session)
            int ssaVersion = 0   // mints fresh versions for re-assigned names (SSA, see the Assign step)

            if (reqAst != null) {
                Object pre = enc.translateBool(reqAst)
                if (pre == null) {
                    throw new UnsupportedConstructException(
                        "precondition '${reqAst.text}' is outside fragment")
                }
                session.assertExpr(pre)
                captureExplain(session, enc, reqAst, pre)
            }

            // Phase 15a — class invariants are assumed at method entry (and re-proved at exit
            // below). The list was pre-filtered for encodability in beforeVisitMethod. For
            // constructors, assumeClassInvariants is a no-op (the invariant is the goal, not a
            // precondition); instead we initialise Int-like fields to their JVM default (0) so a
            // constructor with an empty body whose invariant trivially holds at default values
            // verifies, matching runtime semantics.
            assumeIntJvmBounds(session, enc)
            assumeClassInvariants(session, enc)
            if (currentIsConstructor) initFieldDefaults(session, enc, node)

            // old(...) snapshots: pin each `old.field` referenced by @Ensures to the field's value
            // *now* (method entry), before the body's writes SSA-rebind it forward. Both the scalar
            // (old$f) and array (old$f contents) views are pinned; the unused one is harmless.
            for (String fld : oldFieldNames(postAst)) {
                enc.bind('old$' + fld, enc.varFor(fld))
                enc.bindArray('old$' + fld, enc.arrayFor(fld))
                // Phase 40 — pin the entry-time size of fld so {@code old.fld.size()} survives
                // size-changing list mutations in the body. The bind is harmless for non-sized
                // fields (their sizeOf is just an unrelated int variable, unaffected by anyone).
                enc.bindSize('old$' + fld, enc.sizeOf(fld))
                // A set field's entry snapshot too, so `old.s.size()` / `x in old.s` read the value at entry.
                if (currentSetElementTypes.containsKey(fld)) enc.bindSet('old$' + fld, enc.setFor(fld))
                // A map field's entry snapshot — both value array and key-set — for `old.m[k]` / `old.m.size()`.
                if (currentMapTypes.containsKey(fld)) {
                    enc.putMapVals('old$' + fld, enc.mapValsFor(fld))
                    enc.putMapKeys('old$' + fld, enc.mapKeysFor(fld))
                }
            }

            // Permutation: the values the postcondition counts (`xs.count(v)`). Each array store
            // below maintains count(·, v) for these v via the per-store update law, so a swap (two
            // stores) leaves every count unchanged → the array stays a permutation of its entry value.
            List<Object> countVals = new ArrayList<Object>()
            for (Expression vArg : countValueArgs(postAst)) {
                Object h = enc.translate(vArg)
                if (h != null) countVals.add(h)
            }
            // Phase 69 — arrays whose whole-array sum a contract references; each store maintains it.
            Set<String> sumArrays = sumArrayNames(postAst)
            sumArrays.addAll(sumArrayNames(reqAst))
            // The `k` bounds of any Sets.boundedCount(_, k) in the postcondition drive the bcount per-add law.
            currentBcountKExprs = bcountKArgs(postAst)

            for (Object step : p.steps) {
                if (step instanceof AssertAssume) {
                    // Phase 8b (step 3) — assume a user `assert P` downstream, so an @Ensures may use it. Sound
                    // only because the implicit-obligation pass discharged it (assume/enforce); when that pass
                    // bailed (currentAssertsTrusted == false) the step is a no-op, so the @Ensures is checked
                    // without the unproven fact. An unencodable P simply isn't assumed (weaker, still sound).
                    if (currentAssertsTrusted) {
                        Object c = enc.translate(((AssertAssume) step).cond)
                        if (c != null) session.assertExpr(c)
                    }
                } else if (step instanceof SoftAssume) {
                    // Phase 223 — catch-entry fact: assumed when expressible, dropped (soundly) when not.
                    Object c = enc.translate(((SoftAssume) step).cond)
                    if (c != null) {
                        session.assertExpr(c)
                        if (Reporter.EXPLAIN) {
                            session.explainNoteFact("TRUSTED catch-entry fact (${((SoftAssume) step).cond.text.replaceAll(/\s+/, ' ')}) — registry arms".toString(), c)
                        }
                    }
                } else if (step instanceof Guard) {
                    Guard g = (Guard) step
                    Object c = enc.translate(g.cond)
                    if (c == null) {
                        throw new UnsupportedConstructException(
                            "guard '${g.cond.text}' is outside fragment")
                    }
                    session.assertExpr(g.positive ? c : session.not(c))
                } else if (step instanceof Havoc) {
                    // Phase 192 — catch-entry state: the try block may have executed any prefix before
                    // throwing, so the name's value is unknown here. Rebind to a fresh UNCONSTRAINED
                    // handle in the name's sort (mirroring Assign's sort selection, minus the equality);
                    // reference types also forget their nullity. Weakest-possible knowledge = sound
                    // over-approximation of every partial execution.
                    Havoc h = (Havoc) step
                    ClassNode hType = currentScalarTypes.get(h.name)
                    Object hFresh
                    if (enc.isDecimalName(h.name)) {
                        hFresh = session.realVar(h.name + '#' + (++ssaVersion))
                    } else if (hType != null && !isIntElement(hType)) {
                        hFresh = session.varOfSort(h.name + '#' + (++ssaVersion), enc.sortForType(hType))
                    } else if (currentBooleanLocals.contains(h.name)) {
                        hFresh = session.boolVar(h.name + '#' + (++ssaVersion))
                    } else {
                        hFresh = session.intVar(h.name + '#' + (++ssaVersion))
                    }
                    enc.bind(h.name, hFresh)
                    if (hType != null && !isIntElement(hType) && !enc.isDecimalName(h.name)) {
                        enc.bindNullity(h.name, session.boolVar(h.name + '?null#' + ssaVersion))
                    }
                } else if (step instanceof Assign) {
                    Assign a = (Assign) step
                    // Phase 35 — Set<X> u = a + b / Set<X> u = a.intersect(b): if the RHS is a
                    // recognised set union/intersection over a single element sort, the encoder
                    // materialises u as a first-class set with the membership iff axiom, skipping
                    // the int-SSA path entirely. currentSetElementTypes is shared by reference with
                    // the encoder's setElementTypes, so the new local becomes visible to subsequent
                    // expressions (including applySetMutation's containsKey check below) automatically.
                    if (enc.tryMaterialiseSetBinopAssign(a.name, a.rhs)) {
                        continue
                    }
                    // Phase 38b — xs = List.of(args) / [a, b, c] / Map.of(…) / Set.of(…): if the
                    // RHS is a recognised immutable-container factory, record the local so
                    // subsequent receiver lookups fold the same way as the factory itself would.
                    // Short-circuit the int-SSA path — a list/set/map local isn't an int and the
                    // factory's size/contents are statically known.
                    if (enc.tryRecordFactoryAssign(a.name, a.rhs)) {
                        continue
                    }
                    // Phase 35b — `Set u = a & b` / `a | b` / …: record the local as that set binop so a
                    // later `x in u` folds inline (the materialised quantifier form needs a bound; this
                    // point-wise form doesn't).
                    if (enc.tryRecordSetBinopAssign(a.name, a.rhs)) {
                        continue
                    }
                    // EncodingPack scope hook (Phases 152/188) — a pack-domain local (`def d = 1.m`): a
                    // pack-claimed value has no scalar handle, so alias the local to its RHS *expression*
                    // (the same source-alias mechanism `result` uses), letting the claiming pack's readers
                    // resolve it later. Short-circuits the int-SSA path, which would mis-model the value
                    // as an int shadow.
                    if (enc.packsClaimSource(a.rhs)) {
                        enc.registerSourceAlias(a.name, a.rhs)
                        continue
                    }
                    // Phase 153 — `def fa = async { e }` (lowered to AsyncSupport.async({ e })): alias the local to the
                    // closure's value-expression `e`, so a later `await fa` reads it out (Encoder.awaitedBody). An
                    // Awaitable has no scalar handle; this short-circuits the int-SSA path. Sound for a *safe* (pure
                    // value) async closure — observationally just its value; a mutating closure is the structural case.
                    if (Encoder.isAsyncCall(a.rhs) && Encoder.asyncBodyExpr(a.rhs) != null) {
                        enc.registerAsyncSource(a.name, Encoder.asyncBodyExpr(a.rhs))
                        continue
                    }
                    // Phase 154 — `r = await(a, b, c)` (lowered to AsyncSupport.await(Awaitable.all(a,b,c))): the
                    // gather-all over safe async tasks is the value LIST [a-body, b-body, c-body], order-independent
                    // because `all` waits for every task. Register r as that list factory so r[i]/r.size() fold; the
                    // racing any/first combinators aren't safe values and fall through to a loud skip.
                    if (enc.tryRecordAwaitAll(a.name, a.rhs)) {
                        continue
                    }
                    // Phase 155 — `a = await Awaitable.any(t1, t2)` / first(...): the racing winner is one of the task
                    // values, nondeterministically — an if/else over an unknown selector. Bind a to a fresh value
                    // disjoined over the winners, so the postcondition must hold for EVERY one (prove all branches).
                    if (enc.tryBindAwaitAny(a.name, a.rhs)) {
                        continue
                    }
                    // SSA: each assignment binds the name to a *fresh* version. The rhs is evaluated
                    // against the current binding (the pre-assignment value), so a mutation like
                    // `count = count + 1` becomes `count#1 == count + 1` (not the false `count == count + 1`)
                    // — and a method's @Requires (asserted above) saw the entry version, its @Ensures the
                    // final one. This is what makes re-assignable state, incl. instance fields, sound.
                    //
                    // Phase 47h — fresh-handle sort matches the variable's declared scalar type so a
                    // {@code String name = "world"} or similar non-Int local doesn't crash at
                    // {@code eq(intFresh, stringRhs)}. The {@link Encoder#bind} hook also populates
                    // {@code sortedEnv} for non-Int names, completing the round-trip.
                    // Phase 67 — a decimal (BigDecimal/Double/Float) field/local is bound through the
                    // Real path: the RHS via asReal and a Real fresh handle, so the SSA equality is
                    // sort-matched (an intVar fresh + a Real rhs silently mis-modelled the write — a
                    // syphon `b = b + amt - 0.01` could then "verify" conservation it actually breaks).
                    boolean isDecimal = enc.isDecimalName(a.name)
                    // Phase 133 — `s = a + b` over carrier operands becomes `s = a.plus(b)` (only when `plus` has no
                    // @Requires — see carrierOperatorCall), so the call path below discharges it via the operator's
                    // @Ensures. No-op for everything else; the call paths still see `rhsE`.
                    Expression rhsE = carrierOperatorCall(a.rhs, node)
                    assertSurvivalFacts(session, enc, a.rhs, node)   // Phase 222 — executed call ⟹ no arm held
                    Object rhs = isDecimal ? enc.asRealValue(a.rhs) : enc.translate(a.rhs)
                    // Phase 146 — a decimal local read out of a carrier chain (`BigDecimal v = km(1).plus(mile(1)).value`):
                    // hoist the chain call to a temp carrier local so the `.value` read resolves, then retry the Real path.
                    if (rhs == null && isDecimal) {
                        rhs = enc.asRealValue(hoistCarrierCalls(a.rhs, enc, session, node))
                    }
                    ClassNode declaredType = currentScalarTypes.get(a.name)
                    Object fresh
                    if (isDecimal) {
                        fresh = session.realVar(a.name + '#' + (++ssaVersion))
                    } else if (declaredType != null && !isIntElement(declaredType)) {
                        fresh = session.varOfSort(a.name + '#' + (++ssaVersion), enc.sortForType(declaredType))
                    } else if (currentBooleanLocals.contains(a.name)) {
                        // Phase 48b — boolean locals get a boolVar fresh handle so the
                        // {@code eq(fresh, rhs)} assertion matches sorts.
                        fresh = session.boolVar(a.name + '#' + (++ssaVersion))
                    } else {
                        fresh = session.intVar(a.name + '#' + (++ssaVersion))
                    }
                    if (rhs != null) {
                        session.assertExpr(session.eq(fresh, rhs))
                        enc.bind(a.name, fresh)
                        // Phase 132 — flow nullity through the write of a reference-typed name (field or local), so
                        // `name = n` under `@Requires({ n != null })` establishes a `name != null` invariant, and a
                        // later `name = <nullable>` correctly *forgets* the old non-null fact. Known nullity binds
                        // directly; an unknown RHS havocs to a fresh free flag (sound — never retains a stale fact).
                        if (declaredType != null && !isIntElement(declaredType) && !enc.isDecimalName(a.name)) {
                            Object rhsNull = enc.nullityOfExpr(a.rhs)
                            enc.bindNullity(a.name, rhsNull != null ? rhsNull : session.boolVar(a.name + '?null#' + ssaVersion))
                        }
                    } else if (a.rhs instanceof ConstantExpression && ((ConstantExpression) a.rhs).value == null &&
                               declaredType != null && !isIntElement(declaredType)) {
                        // Phase 132 — `name = null` on a reference field/local: the value isn't modelled (null has no
                        // sort handle), but the nullity is *definitely* null — so a `name != null` invariant refutes
                        // preservation here. Havoc the value, pin the nullity flag to true.
                        enc.bind(a.name, fresh)
                        enc.bindNullity(a.name, session.boolLit(true))
                    } else if (isCallExpr(rhsE) && currentTupleTypes.get(a.name) != null) {
                        // Phase 113 — `Tuple2 r = callee(...)`: a tuple-returning call. Register r as a tuple
                        // local and constrain its slots by the callee's @Ensures (with `result` renamed to r),
                        // so `r.vN` resolves in the body. Must precede the scalar-call branch below, which
                        // would mis-model the tuple as a single Int handle (sortForType(TupleN) → Int).
                        enc.registerTupleLocal(a.name, currentTupleTypes.get(a.name))
                        if (!assumeCalleeEnsures(session, enc, rhsE, node, null, hasDecreases(node), a.name)) {
                            throw new UnsupportedConstructException(
                                "assignment '${a.name} = ${a.rhs.text}' is outside fragment")
                        }
                    } else if (isCallExpr(rhsE) && calleeReturnsList(rhsE, node) &&
                               listLocalFromCall(session, enc, a.name, rhsE, node)) {
                        // Phase 225 — `List l = callee(...)`: establish l's fresh list oracles, then
                        // instantiate the callee's @Ensures with `result` RENAMED to the local (the tuple
                        // route, generalised), so `result != null` / `result.size() == n` constrain them —
                        // the fresh-handle path below can't carry reference-oracle facts across.
                    } else if (isCallExpr(rhsE) &&
                               assumeCalleeEnsures(session, enc, rhsE, node, fresh, hasDecreases(node))) {
                        enc.bind(a.name, fresh)
                        // s = f(args): s is constrained by f's @Ensures (result ↦ s,
                        // formals ↦ actuals) — Phase 7 inter-procedural reasoning. The
                        // callee's @Requires is discharged separately at the call site.
                        // A self-recursive call is the inductive hypothesis, enabled only when
                        // the method declares a @Decreases measure (termination checked separately).
                    } else {
                        throw new UnsupportedConstructException(
                            "assignment '${a.name} = ${a.rhs.text}' is outside fragment")
                    }
                } else if (step instanceof PropStore) {
                    // Phase 89 slice 2 — obj.field = v: store into the identity-keyed heap map so a
                    // subsequent read of obj.field (or other.field when other === obj) sees it.
                    PropStore ps = (PropStore) step
                    Object val = enc.translate(ps.value)
                    if (val == null || !enc.storeField(ps.obj, ps.field, val)) {
                        throw new UnsupportedConstructException(
                            "field write '${ps.obj}.${ps.field} = ${ps.value.text}' is outside fragment")
                    }
                } else if (step instanceof ArrayStore) {
                    ArrayStore st = (ArrayStore) step
                    // A Groovy Range is immutable: `(4..8)[2] = -1` throws UnsupportedOperationException at
                    // runtime, so the verifier refuses the store rather than modelling a successful mutation
                    // (the mutable copies `[*range]` / `range.toList()` are fine — they aren't ranges).
                    if (enc.isImmutableRange(st.arr)) {
                        throw new UnsupportedConstructException(
                            "element assignment '${st.arr}[${st.index.text}] = ${st.value.text}' to a range — " +
                            "ranges are immutable (UnsupportedOperationException at runtime); use [*range] or range.toList()")
                    }
                    // Phase 27 — index/value sorts depend on the receiver kind: map key/value
                    // sorts for a map put, or Int-index + list-element sort for a list/array
                    // store. Routing the translations through translateInSort lets a
                    // Map<String,Integer>'s m["k"] = 5 land cleanly, and a List<String>'s
                    // xs[i] = "abc" likewise.
                    boolean isMap = currentMapTypes.containsKey(st.arr)
                    Object idxSort = isMap ? enc.mapKeySort(st.arr) : session.intSort()
                    Object valSort = isMap ? enc.mapValueSort(st.arr) : enc.listElementSort(st.arr)
                    Object idx = enc.translateInSort(st.index, idxSort)
                    Object val = enc.translateInSort(st.value, valSort)
                    if (idx == null || val == null) {
                        throw new UnsupportedConstructException(
                            "array store '${st.arr}[${st.index.text}] = ${st.value.text}' is outside fragment")
                    }
                    if (isMap) {
                        // m[k] = v on a map: value store + key-set add + cardinality law.
                        doMapPut(session, enc, st.arr, idx, val)
                    } else {
                        // a := (store a idx val): subsequent reads of a see the update.
                        Object oldA = enc.arrayFor(st.arr)
                        Object newA = session.store(oldA, idx, val)
                        // Per-store count law: count(newA, v) = count(oldA, v) - [oldA[idx]==v] + [val==v].
                        // Only applies for Int-valued arrays (the count theory is Int-keyed); skipped
                        // for non-Int element lists where countVals is irrelevant anyway (Phase 27).
                        // Phase 41 — for List receivers the law fires on bcount (bounded by [0, size))
                        // instead of count: the runtime's xs.count(v) is bounded, and the unbounded
                        // count would conflict with the bcount-based @Ensures translation. Arrays
                        // keep using count (fixed size, no semantic mismatch).
                        enc.emitStoreCountLaw(st.arr, oldA, newA, idx, val, valSort, countVals)
                        // Phase 69/70 — per-store SUM law (the additive analogue of the count law): for
                        // the array's whole-range sum, 0 <= idx < N ⟹ sum(newA,0,N) == sum(oldA,0,N) -
                        // oldA[idx] + val (== sum(oldA) otherwise). Int elements use `sum`, decimal (Real)
                        // elements `sumReal`; both make two compensating stores conserve the total — "no
                        // money lost". Gated to arrays whose .sum() a contract references, so ordinary
                        // stores pay nothing.
                        boolean realElem = (valSort == session.realSort())
                        if (sumArrays.contains(st.arr) && (valSort == session.intSort() || realElem)) {
                            Object zeroI = session.intLit(0L)
                            Object n = enc.sizeOf(st.arr)
                            Object oldSum = realElem ? session.sumReal(oldA, zeroI, n) : session.sum(oldA, zeroI, n)
                            Object newSum = realElem ? session.sumReal(newA, zeroI, n) : session.sum(newA, zeroI, n)
                            Object inRange = session.and([session.le(zeroI, idx), session.lt(idx, n)])
                            Object updated = session.plus(session.minus(oldSum, session.select(oldA, idx)), val)
                            session.assertExpr(session.implies(inRange, session.eq(newSum, updated)))
                            session.assertExpr(session.implies(session.not(inRange), session.eq(newSum, oldSum)))
                        }
                        enc.bindArray(st.arr, newA)
                    }
                } else if (step instanceof LemmaCall) {
                    Expression call = ((LemmaCall) step).call
                    // A set mutation `s.add(x)` / `s.remove(x)` threads the set (a store on its
                    // characteristic array) and asserts the per-mutation cardinality law — the set
                    // analogue of the per-store count law above. A list mutation (Phase 40 —
                    // xs.add/clear/removeLast/pop) threads array + size. Otherwise it's a lemma-style
                    // call: assume the callee's @Ensures (a self-call is the inductive hypothesis,
                    // enabled by @Decreases). An unmodelled effect with no usable @Ensures is outside
                    // the fragment.
                    // Phase 237 — a survived non-null asserter: assert the target's non-nullity and move
                    // on (the call has no other modelled effect). Previously this fell through the whole
                    // cascade to the loud "no usable @Ensures" bail — the fact now replaces the failure.
                    // An untranslatable target just loses the fact, sound.
                    Expression nnt = nonNullAssertedTarget(call)
                    Object[] atom = nnt == null ? atomicCellUpdate(enc, session, call) : null
                    if (nnt != null) {
                        Object f = enc.translate(nonNullFact(nnt))
                        if (f != null) {
                            session.assertExpr(f)
                            if (Reporter.EXPLAIN) {
                                session.explainNoteFact("TRUSTED survival fact (${nnt.text.replaceAll(/\s+/, ' ')} != null) — statement-position non-null asserter".toString(), f)
                            }
                        }
                    } else if (atom != null) {
                        // AtomicInteger/AtomicLong mutator on a known cell: rebind the cell to its post-mutation
                        // value via the same SSA discipline a plain `count = count + 1` field write uses, so the
                        // exit @Invariant sees the updated value. (See Encoder.atomicNames / CONCURRENCY.md.)
                        Object fresh = session.intVar(((String) atom[0]) + '#' + (++ssaVersion))
                        session.assertExpr(session.eq(fresh, atom[1]))
                        enc.bind((String) atom[0], fresh)
                    } else if (Encoder.isAwaitDelayCall(call)) {
                        // Phase 153 — `await Awaitable.delay(ms)` is a non-blocking pause: no value, no state effect,
                        // a no-op for a logic proof (timing isn't modelled). Ignore the statement.
                    } else if (Encoder.isMemoryFenceCall(call)) {
                        // Phase 235 — a VarHandle memory fence has no sequential semantics at all: no value, no
                        // state, it constrains only reordering, which this engine deliberately doesn't model.
                        // Ignore the statement — a fenced body proves exactly as its unfenced twin does.
                    } else if (!applySetMutation(session, enc, call) &&
                        !applyMapPut(session, enc, call) &&
                        !applyListMutation(session, enc, call, countVals) &&
                        !applyCrossClassCall(session, enc, call) &&
                        !assumeCalleeEnsures(session, enc, call, node, null, hasDecreases(node))) {
                        throw new UnsupportedConstructException(
                            "standalone call '${call.text}' has no usable @Ensures")
                    }
                }
            }

            // A void method (e.g. a lemma) has no result; its postcondition is over parameters.
            if (p.result != null) {
                // Phase 78 — a list-literal (or List.of/map/set factory) return binds result's CONTENTS:
                // `result` is recorded as a factory container, so `result.size()` and a *constant-index*
                // `result[k]` fold to the k-th returned element (size + nullity pinned). This lets a method
                // return e.g. `[sum, product]` and have `@Ensures({ result[0] == … && result[1] == … })`
                // resolve, where a bare scalar handle couldn't. No scalar result binding is needed.
                if (enc.tryRecordFactoryAssign('result', p.result) ||
                    enc.tryRecordSetBinopAssign('result', p.result)) {
                    // result registered as a factory or a set binop — fall through to the check.
                } else {
                    // Phase 61 — a BigDecimal-valued return narrowed into a non-decimal result (e.g.
                    // `int f() { a / b }`, Groovy truncating the quotient) can't be bound as a Real
                    // without a sort mismatch; skip loudly, as the bare-`/` int case always has.
                    if (enc.isDecimalValued(p.result) && !enc.isDecimalName('result')) {
                        throw new UnsupportedConstructException(
                            "return expression '${p.result.text}' is BigDecimal but the method's return type is not decimal")
                    }
                    // Phase 67 — a decimal-valued return (a `-2.5` literal, a bare decimal variable) is
                    // bound through the Real path; `translate` alone leaves a decimal constant unmodelled
                    // (null) and a decimal variable an int shadow.
                    // Phase 73 — a double/float return is bound through the FP path (Z3 IEEE-754).
                    // Phase 145/146 — model carrier-returning calls in the return expression by hoisting each
                    // maximal one to a temp local bound to its modelled value, so a chain that RETURNS the carrier
                    // (`Quantity.km(1).plus(Quantity.mile(1))`) OR a READ-OUT in the same expression
                    // (`…​.plus(…​).value`) both translate — the latter then an ordinary component read off the temp.
                    Expression retExpr = hoistCarrierCalls(p.result, enc, session, node)
                    Object resHandle = enc.isFpValued(retExpr) ? enc.asFp(retExpr)
                                     : enc.isDecimalValued(retExpr) ? enc.asRealValue(retExpr)
                                     : enc.translate(retExpr)
                    if (resHandle == null && !enc.isFpValued(retExpr) && !enc.isDecimalValued(retExpr)) {
                        // A contracted/self call sitting in the return expression — `return f(args)` or
                        // `return n * f(args)` — isn't itself a fragment expression, so translate() bailed.
                        // Hoist each such call into an implicit single-assignment local bound by the
                        // callee's @Ensures (the inductive hypothesis, for a self-call with @Decreases),
                        // exactly as the `T t = f(args); return … t …` path does, then retry. This is purely
                        // additive: it fires only where we would otherwise skip. assumeCalleeEnsures returns
                        // false (no hoist) if the callee has no usable/sort-matching @Ensures, so a return
                        // whose call can't be faithfully modelled still skips loudly rather than mis-binds.
                        // The callee's @Requires is still discharged by the obligation pass over the original
                        // return expression, so soundness of the precondition check is unaffected.
                        boolean[] hoistedAny = [false]
                        ExpressionTransformer tr = null
                        tr = { Expression e ->
                            if (isCallExpr(e)) {
                                // Phase 206 — mint the hoist local in the CALLEE's return sort: a String- (or
                                // otherwise non-Int-) returning recursive call previously got an Int handle,
                                // and the callee's @Ensures over result.length() crashed the seq sort
                                // ("seq.len: given domain Int") — the functional-leftpad shape.
                                MethodNode hoistCallee = (e instanceof MethodCall) ? resolveContractedCallee(node,
                                    ((MethodCall) e).methodAsString,
                                    collectArgumentExpressions((MethodCall) e)?.size() ?: -1,
                                    hasDecreases(node), null) : null
                                ClassNode hrt = hoistCallee?.returnType
                                Object hSort = (hrt != null && !isIntElement(hrt)) ? enc.sortForType(hrt) : null
                                Object fresh = hSort != null ?
                                    session.varOfSort('ret$call$' + (++ssaVersion), hSort) :
                                    session.intVar('ret$call$' + (++ssaVersion))
                                if (assumeCalleeEnsures(session, enc, e, node, fresh, hasDecreases(node))) {
                                    String nm = 'ret$call$local$' + ssaVersion
                                    enc.bind(nm, fresh)
                                    hoistedAny[0] = true
                                    return new VariableExpression(nm)
                                }
                                return e
                            }
                            return e.transformExpression(tr)
                        } as ExpressionTransformer
                        Expression rewritten = tr.transform(retExpr)
                        if (hoistedAny[0]) resHandle = enc.translate(rewritten)
                    }
                    if (resHandle == null && p.result instanceof ConstantExpression &&
                        ((ConstantExpression) p.result).value == null) {
                        // Phase 149 — `return null` from a reference-typed method (e.g. `Integer poll()` returning
                        // null on the empty path). The value isn't an Int, but the method's @Invariant / @Ensures
                        // over OTHER state (head/tail) is still checkable: bind `result` to a fresh unconstrained
                        // handle with nullity = null, so any value-claim over result stays unprovable (sound),
                        // `result == null` proves and `result != null` refutes — the method verifies instead of
                        // skipping wholesale on the null path.
                        resHandle = session.intVar('result$null$' + (++ssaVersion))
                        enc.bind('result', resHandle)
                        enc.bindNullity('result', session.boolLit(true))
                    } else if (resHandle == null && enc.packsClaimSource(p.result)) {
                        // EncodingPack scope hook (Phases 151/188) — a pack-domain-returning method (e.g. a
                        // Quantity `squareKm() { 1.km * 1.km }`). A pack-claimed value has no scalar Z3 handle,
                        // so instead of binding a value we alias `result` to the return EXPRESSION: the claiming
                        // pack's readers resolve it (`@Ensures({ result == 1.km })` reasons about both layers).
                        // Bind a placeholder handle marked non-null (a pack-claimed construction never is).
                        resHandle = session.intVar('result$qty$' + (++ssaVersion))
                        enc.registerSourceAlias('result', p.result)
                        enc.bind('result', resHandle)
                        enc.bindNullity('result', session.boolLit(false))
                    } else {
                        if (resHandle == null) {
                            throw new UnsupportedConstructException(
                                "return expression '${p.result.text}' is outside fragment")
                        }
                        enc.bind('result', resHandle)
                        // Phase 131 — flow the return value's nullity onto `result`, so an @Ensures({ result != null })
                        // (or an implicit @NonNull-return obligation) can be *proven* — `return "x"`, `return new T()`,
                        // `return x + y`, or `return x` for a @Requires-known-non-null `x` all establish non-nullness.
                        enc.bindNullity('result', enc.nullityOfExpr(p.result))
                    }
                    // Phase 45b — when the return expression is a list-typed local, also alias the
                    // size/array oracles so {@code result.size()} and {@code result[i]} in @Ensures
                    // resolve to the same threaded state the local carries. Without this, the result
                    // is a bare Int handle that doesn't connect to the size/contents oracles —
                    // postconditions about a returned collection couldn't reference its shape.
                    aliasResultToReturnedListLocal(session, enc, p.result)
                }
            }

            // Exit obligation: postcondition (if any) AND each class invariant. A single
            // combined check keeps the body-replay cost flat; refutation diagnostic picks
            // the message based on which obligations are in play.
            List<Object> conjuncts = new ArrayList<Object>()
            if (postAst != null) {
                Object post = enc.translateGoal(postAst)
                if (post == null) {
                    throw new UnsupportedConstructException(
                        "postcondition '${postAst.text}' is outside fragment")
                }
                conjuncts.add(post)
            }
            for (Expression inv : classInvs) {
                Object h = enc.translate(inv)
                if (h != null) conjuncts.add(h)
            }
            if (conjuncts.isEmpty()) return   // nothing to prove on this path

            Object goal = conjuncts.size() == 1 ?
                conjuncts.get(0) : session.and(conjuncts)
            session.assertExpr(session.not(goal))

            CheckResult r = session.check()
            if (r.status == CheckResult.Status.REFUTED && postAst != null) {
                appendOffendingElements(r, enc, session, [postAst])
            }
            r = shown(r)
            if (r.status == CheckResult.Status.VERIFIED) return

            // Anchor the diagnostic on a positioned *expression* node. A value-returning method uses its
            // return expression. A void method (a lemma — its @Ensures is over parameters/fields) has no
            // return expression, so mint a positioned proxy Expression at the method's real declaration
            // position. History: Phase 94 found the MethodNode-anchored diagnostic being silently dropped
            // (a false void @Ensures passed cleanly); a re-audit against Groovy 6.0.0-alpha-2 could NOT
            // reproduce the drop — user MethodNodes stay positioned through gc weaving and STC surfaces
            // MN-anchored errors — so the proxy is retained as zero-cost insurance across Groovy versions,
            // not as a live workaround. (The class-invariant-only path keeps the {@code node} fallback.)
            ASTNode anchor
            if (p.result != null && p.result.lineNumber > 0) {
                anchor = (ASTNode) p.result
            } else if (postAst != null) {
                ConstantExpression proxy = new ConstantExpression(node.name)
                proxy.setSourcePosition((ASTNode) node)
                anchor = (ASTNode) proxy
            } else {
                anchor = (ASTNode) node
            }
            // Phase 62 — when the solver could not *decide* a postcondition (a quantifier/recurrence
            // timeout, the weak refutation direction), fall back to bounded property-based testing of
            // the executable contract: a concrete failing input turns an honest UNKNOWN into a repro.
            // Phase 130 — a synthesized @Reducer/@Associative law lemma carries this metadata; report it with
            // law-and-combiner wording (and skip the body-based PBT fallback — the lemma has no executable body).
            String[] redLaw = (String[]) node.getNodeMetaData(REDUCER_LAW_KEY)
            if (redLaw != null) {
                addStaticTypeError(Reporter.formatReducerLawFailure(redLaw[0], redLaw[1], postAst?.text, r), anchor)
                return
            }
            String[] monLaw = (String[]) node.getNodeMetaData(MONADIC_LAW_KEY)
            if (monLaw != null) {
                addStaticTypeError(Reporter.formatMonadicLawFailure(monLaw[0], monLaw[1], postAst?.text, r), anchor)
                return
            }
            String[] rgLaw = (String[]) node.getNodeMetaData(RG_LAW_KEY)
            if (rgLaw != null) {
                addStaticTypeError(Reporter.formatRelyGuaranteeFailure(rgLaw[0], r), anchor)
                return
            }
            if (r.status == CheckResult.Status.UNKNOWN && postAst != null) {
                String failing = pbtFailingCall(node, postAst, reqAst)
                if (failing != null) {
                    addStaticTypeError(
                        Reporter.formatPostconditionRefutedByTesting(node.name, postAst.text, failing), anchor)
                    return
                }
            }
            if (postAst != null) {
                // Combined or pure @Ensures failure — keep the existing message; the
                // counterexample distinguishes whether the @Ensures or an invariant clause
                // broke (a per-clause attribution is a future polish).
                addStaticTypeError(
                    withRepro(Reporter.formatPostconditionFailure(node.name, postAst.text, r), r, 'AssertionError'), anchor)
            } else {
                // Phase 15a — no @Ensures present; the obligation is purely the class invariant.
                String invText = classInvs.collect { it.text }.join(' && ')
                addStaticTypeError(
                    Reporter.formatClassInvariantViolation(node.name, invText, r), anchor)
            }
        } finally {
            currentBcountKExprs = Collections.<Expression> emptyList()
            try { session.close() } catch (Throwable ignored) {}
        }
    }

    /**
     * Phase 62 — run bounded property-based testing of a method's postcondition over a small grid of
     * integer inputs, returning a {@code name(args)} repro string for the first failing input, or null
     * if none is found / the method is outside the concrete-evaluable fragment. Best-effort: any
     * failure is swallowed so the fallback can never break the build.
     */
    private static String pbtFailingCall(MethodNode node, Expression postAst, Expression reqAst) {
        try {
            ClassNode dc = node.declaringClass
            if (dc == null) return null
            List<Long> args = new ContractTester(dc).findCounterexample(node, reqAst, postAst)
            if (args == null) return null
            StringBuilder sb = new StringBuilder(node.name).append('(')
            for (int i = 0; i < args.size(); i++) {
                if (i > 0) sb.append(', ')
                sb.append(args.get(i))
            }
            sb.append(')').toString()
        } catch (Throwable ignored) {
            null
        }
    }

    /**
     * Apply a set mutation {@code s.add(x)} / {@code s.remove(x)} on a known set-typed receiver,
     * threading the set as a store on its characteristic array and asserting the per-mutation
     * cardinality law — the set analogue of the per-store {@code count} law:
     * {@code card(add(s,x)) = card(s) + (x in s ? 0 : 1)}, {@code card(remove(s,x)) = card(s) - (x in s ? 1 : 0)}.
     * Membership reads of the post-state ride Z3's array theory directly. Returns false (so the caller
     * falls through to lemma handling) when this is not a recognised set mutation.
     */
    /**
     * If {@code call} is a modelled mutator on an {@code AtomicInteger}/{@code AtomicLong} cell, returns
     * {@code [cellName, newValueTerm]} (the post-mutation value as an SMT int term); else null. The caller
     * performs the SSA rebind. The atomics are treated as a single mutable int — exactly the wrapped-integer
     * view that holds at rung 1, where atomicity is transparent (see CONCURRENCY.md):
     * <ul>
     *   <li>{@code incrementAndGet}/{@code getAndIncrement} → cell + 1; {@code decrementAndGet}/{@code getAndDecrement} → cell − 1</li>
     *   <li>{@code addAndGet(d)}/{@code getAndAdd(d)} → cell + d</li>
     *   <li>{@code set(x)}/{@code getAndSet(x)}/{@code lazySet(x)} → x</li>
     *   <li>{@code compareAndSet(e, n)}/{@code weakCompareAndSet(e, n)} → (cell == e ? n : cell) — as a statement, the success flag is dropped</li>
     * </ul>
     */
    private static Object[] atomicCellUpdate(Encoder enc, SmtSession s, Expression call) {
        if (!(call instanceof MethodCallExpression)) return null
        MethodCallExpression mce = (MethodCallExpression) call
        String cell = enc.atomicCellNameOf(mce.objectExpression)
        if (cell == null) return null
        String m = mce.methodAsString
        List<Expression> args = (mce.arguments instanceof ArgumentListExpression) ?
            ((ArgumentListExpression) mce.arguments).expressions : Collections.<Expression>emptyList()
        Object cur = enc.atomicCellRead(cell)
        Object nv
        if (args.isEmpty() && (m == 'incrementAndGet' || m == 'getAndIncrement')) {
            nv = s.plus(cur, s.intLit(1L))
        } else if (args.isEmpty() && (m == 'decrementAndGet' || m == 'getAndDecrement')) {
            nv = s.minus(cur, s.intLit(1L))
        } else if (args.size() == 1 && (m == 'addAndGet' || m == 'getAndAdd')) {
            Object d = enc.translate(args.get(0)); nv = (d == null) ? null : s.plus(cur, d)
        } else if (args.size() == 1 && (m == 'set' || m == 'getAndSet' || m == 'lazySet')) {
            nv = enc.translate(args.get(0))
        } else if (args.size() == 2 && (m == 'compareAndSet' || m == 'weakCompareAndSet' || m == 'weakCompareAndSetPlain')) {
            Object e0 = enc.translate(args.get(0)); Object n0 = enc.translate(args.get(1))
            nv = (e0 == null || n0 == null) ? null : s.ite(s.eq(cur, e0), n0, cur)
        } else {
            return null
        }
        return (nv == null) ? null : ([cell, nv] as Object[])
    }

    private boolean applySetMutation(SmtSession s, Encoder enc, Expression call) {
        if (!(call instanceof MethodCallExpression)) return false
        MethodCallExpression mce = (MethodCallExpression) call
        Expression recv = mce.objectExpression
        if (!(recv instanceof VariableExpression)) return false
        String name = ((VariableExpression) recv).name
        if (!currentSetElementTypes.containsKey(name)) return false
        String m = mce.methodAsString
        if (m != 'add' && m != 'remove') return false
        List<Expression> args = collectArgumentExpressions(mce)
        if (args == null || args.size() != 1) return false
        Object elemSort = enc.setElementSort(name)
        Object elem = enc.translateInSort(args.get(0), elemSort)
        if (elem == null) return false

        Object oldS = enc.setFor(name)
        Object one = s.intLit(1L), zero = s.intLit(0L)
        boolean adding = (m == 'add')
        Object newS = s.store(oldS, elem, adding ? one : zero)
        Object memOld = enc.member(oldS, elem)
        Object delta = adding ? s.ite(memOld, zero, one) : s.ite(memOld, one, zero)
        Object newCard = adding ? s.plus(enc.cardOf(oldS), delta) : s.minus(enc.cardOf(oldS), delta)
        s.assertExpr(s.eq(enc.cardOf(newS), newCard))

        // bcount per-add law (Phase 21): for each Sets.boundedCount(_, k) the postcondition/measure tracks,
        //   add:    bcount(s', k) = bcount(s, k) + (0 <= elem < k ∧ elem ∉ s ? 1 : 0)
        //   remove: bcount(s', k) = bcount(s, k) - (0 <= elem < k ∧ elem ∈ s ? 1 : 0)
        // The mutation only changes the count at the slot `elem`, and only when that slot is in [0, k).
        // Skipped for non-Int element sets (Phase 27): the law's `0 <= elem < k` is meaningless when
        // `elem` is a String/Enum constant — Sets.boundedCount is honestly out of fragment for those.
        if (elemSort == s.intSort()) {
            for (Expression kExpr : currentBcountKExprs) {
                Object kH = enc.translate(kExpr)
                if (kH == null) continue
                Object inDomain = s.and([s.le(zero, elem), s.lt(elem, kH)])
                Object cond = adding ? s.and([inDomain, s.not(memOld)]) : s.and([inDomain, memOld])
                Object cDelta = s.ite(cond, one, zero)
                Object newCount = adding ?
                    s.plus(enc.setCountOf(oldS, kH), cDelta) : s.minus(enc.setCountOf(oldS, kH), cDelta)
                s.assertExpr(s.eq(enc.setCountOf(newS, kH), newCount))
            }
        }

        enc.bindSet(name, newS)
        return true
    }

    /**
     * Phase 45 — apply the effect of a cross-class method call {@code b.method(...)} on a
     * class-typed parameter {@code b}: havoc {@code b}'s declared fields (the callee may have
     * mutated any of them) and re-assume {@code b}'s class invariants under the receiver
     * context (the callee's exit obligation preserves them). The callee's @Requires is
     * discharged separately by {@link #verifyCallSite} via {@link #onMethodSelection}; the
     * callee's @Ensures is currently not assumed cross-class (a known limit — the invariant
     * is what most cross-class contracts actually rely on).
     *
     * Returns false (so the caller falls through to {@link #assumeCalleeEnsures}) if the call
     * isn't of the cross-class shape. Returns true on success, including for calls whose
     * receiver type has no invariants (the havoc still happens — it's the conservative
     * effect of "we don't know what the callee did to b's fields").
     */
    private boolean applyCrossClassCall(SmtSession s, Encoder enc, Expression call) {
        if (!(call instanceof MethodCallExpression)) return false
        MethodCallExpression mce = (MethodCallExpression) call
        Expression recv = mce.objectExpression
        if (!(recv instanceof VariableExpression)) return false
        String recvName = ((VariableExpression) recv).name
        if (!currentObjectParams.containsKey(recvName)) return false
        ClassNode recvType = currentObjectParams.get(recvName)

        // Phase 194 — demote-to-skip at the no-aliasing boundary: with ANOTHER parameter of the same
        // class in scope, the per-name havoc below misses the (possibly aliased) sibling — a field read
        // through it after this call would be proved from stale pre-call state, unsound for f(x, x)
        // actuals. The Phase 89 identity model covers field reads/writes but not call effects, and the
        // runtime rung can never catch this (its grid never aliases two actuals). Throw, not `return
        // false`: falling through to assumeCalleeEnsures would assume the callee's effects un-havocked.
        for (Map.Entry<String, ClassNode> e : currentObjectParams.entrySet()) {
            if (e.key != recvName && e.value?.name == recvType?.name) {
                throw new UnsupportedConstructException(
                    "call through '${recvName}' — parameter '${e.key}' of the same class may alias the receiver, " +
                    "and the per-name field model would miss the shared mutation (heap aliasing is a non-goal)")
            }
        }

        // Step 1 — havoc every declared instance field of the receiver: rebind {@code b$field}
        // to a fresh SMT constant. Subsequent reads of {@code b.field} pick up the fresh value,
        // so the caller can no longer assume the pre-call state was preserved unless the
        // invariant (re-asserted below) implies it.
        Set<String> fields = new LinkedHashSet<String>()
        List<FieldNode> fs = recvType.fields
        if (fs != null) for (FieldNode f : fs) {
            if (f.isStatic()) continue
            String key = recvName + '$' + f.name
            enc.bind(key, s.intVar('havoc$' + key + '$' + (havocCounter++)))
            fields.add(f.name)
        }

        // Step 2 — re-assume the receiver's class invariants under the receiver context. The
        // callee maintained the invariants on exit (verified by Phase 15a/b when the callee's
        // class was compiled), so this is the sound caller-side companion to that proof.
        List<Expression> invs = classInvariantTexts(recvType)
        for (Expression inv : invs) {
            Object h = enc.translateUnderReceiver(inv, recvName, fields)
            if (h != null) s.assertExpr(h)
        }

        true
    }

    /**
     * Phase 40 — size-changing list mutation: {@code xs.add(v)}, {@code xs.clear()},
     * {@code xs.removeLast()} / {@code xs.pop()}. Threads the size and array oracles SSA-style:
     *
     * - **add(v)**: {@code newSize = oldSize + 1}; {@code newArr = store(oldArr, oldSize, v)} — a
     *   single store at the new last index, so subsequent reads of {@code xs[i]} for
     *   {@code i < newSize} see the right values (the prefix unchanged, the new tail = v).
     *   The per-store {@code count} update law fires for each {@code v} the postcondition tracks.
     * - **clear()**: {@code newSize = 0}; array left as-is (no in-bounds read survives).
     * - **removeLast() / pop()**: {@code newSize = oldSize - 1}; array left as-is (prefix
     *   unchanged). The implicit precondition {@code oldSize > 0} is checked via a synthesised
     *   {@code IndexSite(xs, 0)} in {@link ObligationCollector} — refutes pop-on-empty with the
     *   bounds-check diagnostic shape.
     *
     * Returns false (fall through to lemma handling) when the call isn't a recognised list
     * mutation. Sets and maps are guarded out via {@code currentSetElementTypes} / {@code
     * currentMapTypes} so their own dispatch handles those.
     */
    private boolean applyListMutation(SmtSession s, Encoder enc, Expression call, List<Object> countVals) {
        if (!(call instanceof MethodCallExpression)) return false
        MethodCallExpression mce = (MethodCallExpression) call
        Expression recv = mce.objectExpression
        if (!(recv instanceof VariableExpression)) return false
        String name = ((VariableExpression) recv).name
        // Sets and maps are owned by their own dispatch — bail.
        if (currentSetElementTypes.containsKey(name) || currentMapTypes.containsKey(name)) return false
        String m = mce.methodAsString
        List<Expression> args = collectArgumentExpressions(mce)
        if (args == null) return false

        // Direct SMT-expression rebinding (no SSA naming needed): newSize/newArr are computed
        // expressions, not named constants. Two adds in a row chain via expression composition —
        // oldSize after the first add is {@code oldSize0 + 1}, etc. — so size/contents stay
        // sound across consecutive mutations.
        Object zero = s.intLit(0L), one = s.intLit(1L)
        if (m == 'add' && args.size() == 1) {
            Object x = enc.translate(args.get(0))
            if (x == null) return false
            Object oldSize = enc.sizeOf(name)
            Object oldArr = enc.arrayFor(name)
            Object newArr = s.store(oldArr, oldSize, x)
            Object newSize = s.plus(oldSize, one)
            enc.bindArray(name, newArr)
            enc.bindSize(name, newSize)
            // Phase 38d — invalidate any factory record on the local: post-mutation, the literal
            // args no longer describe xs's contents, and factoryContainerFor lookups should fall
            // through to the threaded size/array oracles instead of folding to the stale literals.
            enc.clearFactoryRecord(name)
            // Phase 41 — bcount boundary law: bcount(newArr, w, 0, newSize) =
            //   bcount(oldArr, w, 0, oldSize) + (x == w ? 1 : 0). The prefix [0, oldSize) is
            //   unchanged by the store at oldSize, and the new tail-slot value is x.
            for (Object w : countVals) {
                Object delta = s.ite(s.eq(x, w), one, zero)
                Object lhs = s.bcount(newArr, w, zero, newSize)
                Object rhs = s.plus(s.bcount(oldArr, w, zero, oldSize), delta)
                s.assertExpr(s.eq(lhs, rhs))
            }
            return true
        }
        if (m == 'clear' && args.isEmpty()) {
            // Array left as-is — no in-bounds read survives a clear, so the prior contents are
            // irrelevant. (Modelling clear as a havoc'd fresh array would be sounder against an
            // out-of-bounds read, but we already model that case via the bounds-check obligation.)
            enc.bindSize(name, zero)
            enc.clearFactoryRecord(name)
            // Phase 41 — bcount over the empty range is 0 by definition; assert per tracked v
            // so the user's @Ensures({ xs.count(v) == 0 }) discharges trivially after clear.
            Object arr = enc.arrayFor(name)
            for (Object w : countVals) {
                s.assertExpr(s.eq(s.bcount(arr, w, zero, zero), zero))
            }
            return true
        }
        if ((m == 'removeLast' || m == 'pop') && args.isEmpty()) {
            // The "oldSize > 0" check is emitted as a synthesised IndexSite by ObligationCollector,
            // so pop-on-empty refutes with the standard bounds-check diagnostic (Possible
            // IndexOutOfBoundsException, fails on: f([])). Threading still proceeds — the
            // body-replay path is best-effort even when an implicit obligation didn't discharge.
            Object oldSize = enc.sizeOf(name)
            Object newSize = s.minus(oldSize, one)
            Object arr = enc.arrayFor(name)
            enc.bindSize(name, newSize)
            enc.clearFactoryRecord(name)
            // Phase 41 — bcount boundary law: bcount(arr, w, 0, oldSize) =
            //   bcount(arr, w, 0, newSize) + (arr[newSize] == w ? 1 : 0). Equivalently, the
            //   new bcount is the old bcount minus the contribution of the dropped tail element.
            for (Object w : countVals) {
                Object dropped = s.ite(s.eq(s.select(arr, newSize), w), one, zero)
                Object lhs = s.bcount(arr, w, zero, newSize)
                Object rhs = s.minus(s.bcount(arr, w, zero, oldSize), dropped)
                s.assertExpr(s.eq(lhs, rhs))
            }
            return true
        }
        return false
    }

    /**
     * Thread a map put {@code m[k] = v} / {@code m.put(k, v)}: store {@code v} into the value array, add
     * {@code k} to the key-set, and assert the key-set cardinality law — so {@code m.size()} grows by one
     * exactly when {@code k} is a new key. A later {@code m[k]} read sees {@code v}, and {@code m[j]} for
     * {@code j != k} is unchanged, both via Z3's array theory. Shared by the {@code m.put} (lemma) and
     * {@code m[k] = v} (array-store) spellings.
     */
    private void doMapPut(SmtSession s, Encoder enc, String logical, Object key, Object val) {
        // The put semantics live in Encoder.mapPut (shared with the loop-body executor — Phase 186).
        enc.mapPut(logical, key, val)
    }

    /** Apply a {@code m.put(k, v)} call as a map mutation; false (fall through to lemma handling) if not one. */
    private boolean applyMapPut(SmtSession s, Encoder enc, Expression call) {
        if (!(call instanceof MethodCallExpression)) return false
        MethodCallExpression mce = (MethodCallExpression) call
        Expression recv = mce.objectExpression
        if (!(recv instanceof VariableExpression)) return false
        String name = ((VariableExpression) recv).name
        if (!currentMapTypes.containsKey(name) || mce.methodAsString != 'put') return false
        List<Expression> args = collectArgumentExpressions(mce)
        if (args == null || args.size() != 2) return false
        // Phase 27 — route key and value through the map's declared sorts so a String-keyed
        // / Enum-keyed map's `put("admin", 5)` lands as a constant of the right element sort.
        Object key = enc.translateInSort(args.get(0), enc.mapKeySort(name))
        Object val = enc.translateInSort(args.get(1), enc.mapValueSort(name))
        if (key == null || val == null) return false
        doMapPut(s, enc, name, key, val)
        return true
    }

    private static AnnotationNode findEnsures(MethodNode m) {
        List<AnnotationNode> direct = m.getAnnotations(ENSURES_TYPE)
        if (direct != null && !direct.isEmpty()) return direct[0]
        List<AnnotationNode> str = m.getAnnotations(VERIFY_ENSURES_TYPE)
        return (str != null && !str.isEmpty()) ? str[0] : null
    }

    // ---- Loops (@Invariant / @Decreases) ----

    /**
     * A body shaped as: straight-line prefix; one annotated loop; straight-line suffix.
     * Phase 49 (Slice A) — the prefix/suffix may include "early-exit" if-statements whose
     * then-branch ends with a {@code return} (and whose else-branch is absent or empty).
     * Each such if becomes an {@link EarlyExit} entry; the surrounding statements that run
     * unconditionally before the loop end up in {@link #prefix} (or {@link #suffix}). All
     * exit guards' negations are assumed when verifying the loop establishment / use, so the
     * loop machinery only fires on the "no early-exit taken" path.
     */
    @CompileStatic
    // ── Phase 213 — @ThrowsIf: the universal exceptional contract ───────────────────────────────
    // `@ThrowsIf(value = { C }, type = E)` asserts the method throws (a subtype of) E exactly when C
    // holds at entry. Two directions, each checked per execution path of the (guard/throw/return)
    // fragment: MUST-THROW — no normal-return path is satisfiable together with C; ONLY-WHEN — no
    // E-throwing path is satisfiable together with ¬C. SAT gives the concrete witness input.

    /** One parsed @ThrowsIf instance: condition AST, declared exception, mode flags, anchor. */
    @CompileStatic
    private static class TiInstance {
        Expression cond
        ClassNode exception     // null = untyped (any throwable)
        boolean woven = true        // upstream default: the guard is GENERATED at entry (by construction)
        boolean direct = true       // metadata: false = the throw arises from invoked code (trusted claim)
        boolean exhaustive = true   // false = one-directional (signals-style): must-throw only
        Expression anchor
        /** Specification-only: not woven and not in this body — take on trust, vacuity-check, ledger. */
        boolean trusted() { !woven && !direct }
        /** Must-throw needs a body proof only when the throw is claimed to be IN the body. */
        boolean bodyChecked() { !woven && direct }
    }

    /** All @ThrowsIf annotation nodes (direct repeats and/or the @ThrowsIfConditions container). */
    private static List<AnnotationNode> tiAnnotations(MethodNode node) {
        List<AnnotationNode> out = new ArrayList<AnnotationNode>()
        for (AnnotationNode an : node.getAnnotations()) {
            String n = an.classNode.nameWithoutPackage
            if (n == 'ThrowsIf') out.add(an)
            else if (n == 'ThrowsIfConditions' && an.getMember('value') instanceof ListExpression) {
                for (Expression e : ((ListExpression) an.getMember('value')).expressions) {
                    if (e instanceof AnnotationConstantExpression &&
                        ((AnnotationConstantExpression) e).value instanceof AnnotationNode) {
                        out.add((AnnotationNode) ((AnnotationConstantExpression) e).value)
                    }
                }
            }
        }
        out
    }

    private void verifyThrowsIf(MethodNode node, Statement body) {
        List<AnnotationNode> anns = tiAnnotations(node)
        if (anns.isEmpty()) return
        Set<String> paramNames = node.parameters.collect { it.name } as Set

        // parse every instance first (a malformed one is its own loud skip, others proceed)
        List<TiInstance> instances = new ArrayList<TiInstance>()
        for (AnnotationNode ann : anns) {
            Expression member = ann.getMember('value')
            if (!(member instanceof ClosureExpression)) continue
            Statement cc = ((ClosureExpression) member).code
            List<Statement> cs = cc instanceof BlockStatement ? ((BlockStatement) cc).statements :
                Collections.<Statement> singletonList(cc)
            if (cs.size() != 1 || !(cs.get(0) instanceof ExpressionStatement)) {
                addStaticTypeError(Reporter.formatThrowsIfSkipped(node.name, 'condition is not a single expression'), (ASTNode) member)
                continue
            }
            TiInstance ti = new TiInstance()
            ti.cond = ((ExpressionStatement) cs.get(0)).expression
            ti.anchor = member
            Expression excMember = ann.getMember('exception')
            ti.exception = excMember instanceof ClassExpression ? ((ClassExpression) excMember).type : null
            Expression wv = ann.getMember('woven')
            ti.woven = !(wv instanceof ConstantExpression && ((ConstantExpression) wv).value == false)
            Expression dr = ann.getMember('direct')
            ti.direct = !(dr instanceof ConstantExpression && ((ConstantExpression) dr).value == false)
            Expression ex = ann.getMember('exhaustive')
            ti.exhaustive = !(ex instanceof ConstantExpression && ((ConstantExpression) ex).value == false)
            // condition scope: the (transform-normalised) closure params + method params
            Set<String> condVars = new LinkedHashSet<String>()
            collectVariableNames(ti.cond, condVars)
            if (!paramNames.containsAll(condVars)) {
                addStaticTypeError(Reporter.formatThrowsIfSkipped(node.name,
                    "condition references non-parameters: ${(condVars - paramNames).join(', ')}"), (ASTNode) member)
                continue
            }
            instances.add(ti)
        }
        if (instances.isEmpty()) return

        Expression reqAst = findRequires(node) != null ? contractAstFor(node, 'requires') : null

        // trusted instances (woven = false, direct = false): specification-only — vacuity-checked (a
        // contradictory trusted spec poisons every caller), then assumed without proof or warning. The
        // rung still monitors them, and the ledger records them (Phase 216 — quiet at the use site,
        // visible in the inventory).
        for (TiInstance ti : instances.findAll { it.trusted() }) {
            TrustLedger.record('in-place @ThrowsIf', "${node.declaringClass.name}#${node.name}",
                "throws ${ti.exception != null ? ti.exception.nameWithoutPackage : 'Throwable'} iff ${ti.cond.text}")
            SmtSession s = backend.session()
            try {
                Encoder enc = mkEncoder(s)
                if (reqAst != null) { Object pre = enc.translateBool(reqAst); if (pre != null) s.assertExpr(pre) }
                Object ch = enc.translateBool(ti.cond)
                if (ch != null) {
                    s.assertExpr(ch)
                    if (s.check().status == CheckResult.Status.VERIFIED) {   // UNSAT — condition can never hold
                        addStaticTypeError(Reporter.formatThrowsIfRefuted(node.name,
                            'the TRUSTED condition is unsatisfiable — the contract is vacuous', null), (ASTNode) ti.anchor)
                    }
                }
            } catch (Throwable ignored) {
            } finally { try { s.close() } catch (Throwable ignored) {} }
        }
        // Phase 224 — upstream weaving changes what needs a body proof. A WOVEN arm's must-throw holds
        // BY CONSTRUCTION (groovy.contracts generates the entry guard at SEMANTIC_ANALYSIS — after the
        // clean-body snapshot this walk sees, which is precisely why it must not be re-proved here).
        // Only a BODY arm (woven = false, direct = true) claims a throw this walk can find. The
        // only-when direction still walks whenever any non-trusted arm exists: the body may throw a
        // matching type for unlisted reasons regardless of who implements the guards.
        List<TiInstance> walked = instances.findAll { !it.trusted() }
        List<TiInstance> bodyChecked = instances.findAll { it.bodyChecked() }
        if (walked.isEmpty()) return

        List<Object[]> paths = new ArrayList<Object[]>()
        try {
            tiWalk(body instanceof BlockStatement ? ((BlockStatement) body).statements :
                Collections.<Statement> singletonList(body), 0, new ArrayList<Expression>(), paramNames, paths)
        } catch (UnsupportedConstructException e) {
            addStaticTypeError(Reporter.formatThrowsIfSkipped(node.name, e.message), (ASTNode) walked.get(0).anchor)
            return
        }
        for (Object[] path : paths) {
            List<Expression> guards = (List<Expression>) path[0]
            ClassNode thrown = (ClassNode) path[1]
            if (thrown == null) {
                // MUST-THROW, per body-checked instance: no normal return is satisfiable with its condition.
                for (TiInstance ti : bodyChecked) {
                    if (tiCheckSat(node, reqAst, guards, Collections.singletonList(ti.cond),
                            'the method can return normally although the condition holds', ti.anchor)) return
                }
            } else {
                // ONLY-WHEN: a throw of T must be justified by SOME instance matching T (trusted ones
                // included — a visible throw contradicting a trusted spec is evidence, not noise).
                // A one-directional arm (exhaustive = false) disclaims the exhaustiveness of the whole
                // arm-set, so the only-when direction is not an obligation (Phase 222).
                if (instances.any { !it.exhaustive }) continue
                List<Expression> matchConds = instances.findAll { TiInstance ti ->
                    ti.exception == null || thrown.equals(ti.exception) || thrown.isDerivedFrom(ti.exception)
                }*.cond
                if (matchConds.isEmpty()) continue      // outside every declared contract
                List<Expression> negs = matchConds.collect { Expression c ->
                    (Expression) new NotExpression(new BooleanExpression(c)) }
                if (tiCheckSat(node, reqAst, guards, negs,
                        "the method can throw ${thrown.nameWithoutPackage} although no @ThrowsIf condition holds",
                        walked.get(0).anchor)) return
            }
        }
        // all paths UNSAT in both directions: the contracts are verified, silently
    }

    /** Assert req + guards + extras; SAT ⟹ report the violation (with a null-aware counterexample) and
     *  return true; UNKNOWN ⟹ loud skip and return true; UNSAT ⟹ false (this check passed). */
    private boolean tiCheckSat(MethodNode node, Expression reqAst, List<Expression> guards,
                               List<Expression> extras, String direction, Expression anchor) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            boolean clean = true
            if (reqAst != null) {
                Object pre = enc.translateBool(reqAst)
                if (pre == null) clean = false else s.assertExpr(pre)
            }
            for (Expression g : (guards + extras)) {
                if (!clean) break
                Object gh = enc.translateBool(g)
                if (gh == null) clean = false else s.assertExpr(gh)
            }
            if (!clean) {
                addStaticTypeError(Reporter.formatThrowsIfSkipped(node.name,
                    'a path guard or condition is outside the fragment'), (ASTNode) anchor)
                return true
            }
            CheckResult r = s.check()
            if (r.status == CheckResult.Status.REFUTED) {
                String cex = r.counterexample.collect { k, v ->
                    k.endsWith('?null') ? "${k - '?null'} = ${v == 1L ? 'null' : 'non-null'}" : "${k} = ${v}"
                }.join(', ')
                addStaticTypeError(Reporter.formatThrowsIfRefuted(node.name, direction, cex), (ASTNode) anchor)
                return true
            }
            if (r.status == CheckResult.Status.UNKNOWN) {
                addStaticTypeError(Reporter.formatThrowsIfSkipped(node.name,
                    "solver could not decide: ${direction}"), (ASTNode) anchor)
                return true
            }
            return false
        } finally { try { s.close() } catch (Throwable ignored) {} }
    }

    /** Path enumeration for the @ThrowsIf fragment: guards + terminal per path. Continuation-style so
     *  a non-terminating branch flows into the statements after its `if`. */
    private void tiWalk(List<Statement> stmts, int i, List<Expression> guards,
                        Set<String> paramNames, List<Object[]> out) {
        if (i >= stmts.size()) { out.add([guards, null] as Object[]); return }
        Statement st = stmts.get(i)
        if (st instanceof BlockStatement) {
            List<Statement> merged = new ArrayList<Statement>(((BlockStatement) st).statements)
            merged.addAll(stmts.subList(i + 1, stmts.size()))
            tiWalk(merged, 0, guards, paramNames, out)
        } else if (st instanceof ThrowStatement) {
            Expression ex = ((ThrowStatement) st).expression
            if (!(ex instanceof ConstructorCallExpression)) throw new UnsupportedConstructException('non-constructor throw')
            out.add([guards, ((ConstructorCallExpression) ex).type] as Object[])
        } else if (st instanceof ReturnStatement) {
            // a call inside the returned expression can itself throw — treating it as a pure return
            // would be inconsistent with the loud-skip policy for call statements
            Expression re = ((ReturnStatement) st).expression
            if (re != null && containsCall(re)) {
                throw new UnsupportedConstructException("unmodelled call in return expression '${re.text}'")
            }
            out.add([guards, null] as Object[])
        } else if (st instanceof IfStatement) {
            IfStatement ifs = (IfStatement) st
            List<Statement> rest = stmts.subList(i + 1, stmts.size())
            List<Statement> thenList = new ArrayList<Statement>(); thenList.add(ifs.ifBlock); thenList.addAll(rest)
            List<Expression> tg = new ArrayList<Expression>(guards); tg.add(ifs.booleanExpression)
            tiWalk(thenList, 0, tg, paramNames, out)
            List<Expression> eg = new ArrayList<Expression>(guards); eg.add(new NotExpression(ifs.booleanExpression))
            if (ifs.elseBlock != null && !(ifs.elseBlock instanceof EmptyStatement)) {
                List<Statement> elseList = new ArrayList<Statement>(); elseList.add(ifs.elseBlock); elseList.addAll(rest)
                tiWalk(elseList, 0, eg, paramNames, out)
            } else {
                tiWalk(rest, 0, eg, paramNames, out)
            }
        } else if (st instanceof ExpressionStatement) {
            Expression e = ((ExpressionStatement) st).expression
            if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.ASSIGN) {
                Expression lhs = ((BinaryExpression) e).leftExpression
                if (lhs instanceof VariableExpression && paramNames.contains(((VariableExpression) lhs).name)) {
                    throw new UnsupportedConstructException("parameter '${((VariableExpression) lhs).name}' is reassigned")
                }
                tiWalk(stmts, i + 1, guards, paramNames, out)
            } else if (e instanceof DeclarationExpression) {
                tiWalk(stmts, i + 1, guards, paramNames, out)   // locals don't affect param-only guards
            } else if (isCallExpr(e)) {
                // Objects.requireNonNull(v) IS a guard-throw — model it as `if (v == null) throw NPE`.
                Expression rnnTarget = requireNonNullTarget(e)
                if (rnnTarget != null) {
                    Expression isNull = new BinaryExpression(rnnTarget,
                        Token.newSymbol(Types.COMPARE_EQUAL, st.lineNumber, st.columnNumber),
                        ConstantExpression.NULL)
                    List<Expression> tg = new ArrayList<Expression>(guards); tg.add(isNull)
                    out.add([tg, ClassHelper.make(NullPointerException)] as Object[])
                    List<Expression> eg = new ArrayList<Expression>(guards)
                    eg.add(new NotExpression(new BooleanExpression(isNull)))
                    tiWalk(stmts, i + 1, eg, paramNames, out)
                } else {
                    // any other call can throw or matter — silence would be unsound in either direction
                    throw new UnsupportedConstructException(
                        "unmodelled call '${e.text}' in the @ThrowsIf fragment")
                }
            } else {
                tiWalk(stmts, i + 1, guards, paramNames, out)
            }
        } else {
            throw new UnsupportedConstructException("statement ${st.class.simpleName} in the @ThrowsIf fragment")
        }
    }

    /** The argument of an {@code Objects.requireNonNull(v[, msg])} call (any receiver spelling), or null. */
    private static Expression requireNonNullTarget(Expression e) {
        if (!(e instanceof MethodCall)) return null
        if (((MethodCall) e).methodAsString != 'requireNonNull') return null
        List<Expression> args = e instanceof MethodCallExpression ?
            (((MethodCallExpression) e).arguments instanceof ArgumentListExpression ?
                ((ArgumentListExpression) ((MethodCallExpression) e).arguments).expressions : null) :
            (e instanceof StaticMethodCallExpression &&
             ((StaticMethodCallExpression) e).arguments instanceof ArgumentListExpression ?
                ((ArgumentListExpression) ((StaticMethodCallExpression) e).arguments).expressions : null)
        if (args == null || args.isEmpty() || args.size() > 2) return null
        args.get(0)
    }

    /**
     * Phase 237 — the target of a statement-position non-null ASSERTER, or null. Three spellings:
     * {@code Objects.requireNonNull(v[, msg])} (any receiver spelling — the same call the @ThrowsIf
     * walk above models as a guard-throw), JUnit's single-argument {@code assertNotNull(v)}, and
     * AssertJ/Truth's {@code assertThat(v).isNotNull()}. Matched by simple name — the trust model
     * NullChecker (GROOVY-12250) and the Jakarta-annotation matching already use; a user-defined
     * method merely NAMED {@code assertNotNull} that doesn't actually throw would be trusted
     * wrongly (documented in CAPABILITIES). The two-argument JUnit forms are deliberately NOT
     * matched: JUnit 4 puts the message first and JUnit 5 puts it last, so which argument is the
     * target is ambiguous by name alone — no fact beats a maybe-wrong fact.
     */
    private static Expression nonNullAssertedTarget(Expression e) {
        Expression t = requireNonNullTarget(e)
        if (t != null) return t
        if (!(e instanceof MethodCall)) return null
        String m = ((MethodCall) e).methodAsString
        if (m == 'assertNotNull') {
            List<Expression> args = collectArgumentExpressions((MethodCall) e)
            return args.size() == 1 ? args.get(0) : null
        }
        if (m == 'isNotNull' && e instanceof MethodCallExpression) {
            if (!collectArgumentExpressions((MethodCall) e).isEmpty()) return null
            Expression recv = ((MethodCallExpression) e).objectExpression
            // The receiver is `assertThat(v)` in either call shape — STC rewrites an implicit-this
            // call on a static helper to a StaticMethodCallExpression, so match the MethodCall
            // interface, not the concrete class.
            if (recv instanceof MethodCall && ((MethodCall) recv).methodAsString == 'assertThat') {
                List<Expression> rargs = collectArgumentExpressions((MethodCall) recv)
                return rargs.size() == 1 ? rargs.get(0) : null
            }
        }
        null
    }

    /** The `target != null` fact a survived non-null asserter establishes (Phase 237). */
    private static Expression nonNullFact(Expression target) {
        new BooleanExpression(new BinaryExpression(target,
            Token.newSymbol(Types.COMPARE_NOT_EQUAL, target.lineNumber, target.columnNumber),
            ConstantExpression.NULL))
    }

    /** True when the expression tree contains any method/constructor call. */
    private static boolean containsCall(Expression e) {
        boolean[] found = [false]
        e.visit(new org.codehaus.groovy.ast.CodeVisitorSupport() {
            @Override void visitMethodCallExpression(MethodCallExpression mce) { found[0] = true; super.visitMethodCallExpression(mce) }
            @Override void visitStaticMethodCallExpression(StaticMethodCallExpression sm) { found[0] = true; super.visitStaticMethodCallExpression(sm) }
            @Override void visitConstructorCallExpression(ConstructorCallExpression cce) { found[0] = true; super.visitConstructorCallExpression(cce) }
        })
        found[0]
    }

    private static void collectVariableNames(Expression e, Set<String> out) {
        e.visit(new org.codehaus.groovy.ast.CodeVisitorSupport() {
            @Override
            void visitVariableExpression(VariableExpression ve) {
                if (!(ve.name in ['true', 'false', 'this'])) out.add(ve.name)
            }
        })
    }

    // ── Phase 212 — shouldFail: the provable exceptional witness ────────────────────────────────
    // `shouldFail(E) { m(consts) }` is a closed claim: substitute the constants into the callee body,
    // walk the (if/throw/return) fragment deciding each guard by closed evaluation, and check which
    // throw the unique execution path reaches. Verified silently; refuted with the concrete reason
    // ("completes normally, returning 4" / "throws X, not the expected Y"); outside-fragment → loud
    // skip (groovy-test still checks the claim at runtime — graceful degradation as everywhere else).

    /** Closed-evaluation failure for the shouldFail walk (mirrors PureEvaluator's NotEvaluable). */
    @CompileStatic
    private static class SfNotClosed extends RuntimeException {
        SfNotClosed(String why) { super(why) }
    }

    private void verifyShouldFailClaims(MethodNode node, Statement body) {
        List<MethodCallExpression> claims = new ArrayList<MethodCallExpression>()
        collectShouldFailCalls(body, claims)
        for (MethodCallExpression mce : claims) {
            List<Expression> args = collectArgumentExpressions(mce)
            if (args == null || args.isEmpty()) continue
            ClassNode expected = null
            ClosureExpression block = null
            if (args.size() == 2 && args.get(0) instanceof ClassExpression && args.get(1) instanceof ClosureExpression) {
                expected = ((ClassExpression) args.get(0)).type
                block = (ClosureExpression) args.get(1)
            } else if (args.size() == 1 && args.get(0) instanceof ClosureExpression) {
                block = (ClosureExpression) args.get(0)
            } else {
                continue   // not a recognisable shouldFail shape — leave to runtime
            }
            try {
                Object outcome = shouldFailOutcome(node, block)
                if (outcome instanceof ClassNode) {
                    ClassNode thrown = (ClassNode) outcome
                    if (expected != null && !thrown.equals(expected) && !thrown.isDerivedFrom(expected)) {
                        addStaticTypeError(Reporter.formatShouldFailRefuted(
                            "the block throws ${thrown.nameWithoutPackage}, not the expected " +
                            "${expected.nameWithoutPackage} — shouldFail would rethrow at runtime"), mce)
                    }
                    // matching (or untyped) throw: claim verified, silently
                } else {
                    addStaticTypeError(Reporter.formatShouldFailRefuted(
                        "the block completes normally (returning ${outcome}) — it never throws, and " +
                        "shouldFail would fail at runtime"), mce)
                }
            } catch (SfNotClosed nc) {
                addStaticTypeError(Reporter.formatShouldFailSkipped(nc.message), mce)
            }
        }
    }

    private static void collectShouldFailCalls(Statement st, List<MethodCallExpression> out) {
        if (st instanceof BlockStatement) {
            for (Statement s : ((BlockStatement) st).statements) collectShouldFailCalls(s, out)
        } else if (st instanceof IfStatement) {
            collectShouldFailCalls(((IfStatement) st).ifBlock, out)
            if (((IfStatement) st).elseBlock != null) collectShouldFailCalls(((IfStatement) st).elseBlock, out)
        } else if (st instanceof ExpressionStatement) {
            Expression e = ((ExpressionStatement) st).expression
            if (e instanceof MethodCallExpression && ((MethodCallExpression) e).methodAsString == 'shouldFail') {
                out.add((MethodCallExpression) e)
            }
        }
    }

    /** The block's provable outcome: the thrown exception's ClassNode, or the (Long/String) value it
     *  returns / falls through with. Throws {@link SfNotClosed} when outside the closed fragment. */
    private Object shouldFailOutcome(MethodNode node, ClosureExpression block) {
        List<Statement> stmts = block.code instanceof BlockStatement ?
            ((BlockStatement) block.code).statements : Collections.<Statement> singletonList(block.code)
        // Canonical witness shape: a single same-class call with closed arguments — inline the callee.
        if (stmts.size() == 1 && stmts.get(0) instanceof ExpressionStatement) {
            Expression e = ((ExpressionStatement) stmts.get(0)).expression
            if (e instanceof MethodCallExpression || e instanceof StaticMethodCallExpression) {
                String name = ((MethodCall) e).methodAsString
                List<Expression> actuals = collectArgumentExpressions((MethodCall) e)
                MethodNode callee = node.declaringClass.getMethods(name).find {
                    it.parameters.length == (actuals?.size() ?: -1) && it.code != null
                }
                if (callee != null) {
                    Map<String, Object> env = new LinkedHashMap<String, Object>()
                    for (int i = 0; i < actuals.size(); i++) {
                        env.put(callee.parameters[i].name, sfEval(actuals.get(i), Collections.<String, Object> emptyMap()))
                    }
                    List<Statement> calleeStmts = callee.code instanceof BlockStatement ?
                        ((BlockStatement) callee.code).statements : Collections.<Statement> singletonList(callee.code)
                    Object r = sfWalk(calleeStmts, env)
                    return r == null ? 'void' : r   // fell through the callee → completes normally
                }
                throw new SfNotClosed("cannot resolve same-class callee '${name}'")
            }
        }
        // Direct statements (e.g. `shouldFail { throw new IllegalStateException('x') }`).
        Object r = sfWalk(stmts, new LinkedHashMap<String, Object>())
        return r == null ? 'void' : r
    }

    /** Walk a statement list under a closed environment. Returns the terminating outcome — the thrown
     *  ClassNode or the returned value — or null when the list falls through (normal completion). */
    private Object sfWalk(List<Statement> stmts, Map<String, Object> env) {
        for (Statement st : stmts) {
            if (st instanceof BlockStatement) {
                Object r = sfWalk(((BlockStatement) st).statements, env)
                if (r != null) return r
            } else if (st instanceof ThrowStatement) {
                Expression ex = ((ThrowStatement) st).expression
                if (ex instanceof ConstructorCallExpression) return ((ConstructorCallExpression) ex).type
                throw new SfNotClosed('throw of a non-constructor expression')
            } else if (st instanceof ReturnStatement) {
                Expression re = ((ReturnStatement) st).expression
                return (re == null || re instanceof org.codehaus.groovy.ast.expr.EmptyExpression) ? 'void' : sfEval(re, env)
            } else if (st instanceof IfStatement) {
                IfStatement ifs = (IfStatement) st
                Object c = sfEval(ifs.booleanExpression, env)
                if (!(c instanceof Boolean)) throw new SfNotClosed("guard '${ifs.booleanExpression.text}' is not a closed boolean")
                Statement branch = ((Boolean) c) ? ifs.ifBlock : ifs.elseBlock
                if (branch != null && !(branch instanceof EmptyStatement)) {
                    Object r = sfWalk(Collections.singletonList(branch), env)
                    if (r != null) return r
                }
            } else if (st instanceof ExpressionStatement &&
                       ((ExpressionStatement) st).expression instanceof DeclarationExpression) {
                DeclarationExpression de = (DeclarationExpression) ((ExpressionStatement) st).expression
                if (!(de.leftExpression instanceof VariableExpression)) throw new SfNotClosed('multi-target declaration')
                env.put(((VariableExpression) de.leftExpression).name, sfEval(de.rightExpression, env))
            } else {
                throw new SfNotClosed("statement ${st.class.simpleName} is outside the closed-witness fragment")
            }
        }
        null
    }

    /** Tiny closed evaluator: constants, env lookups, unary minus, int arithmetic, comparisons,
     *  boolean connectives, ternary. Throws {@link SfNotClosed} for anything else. */
    private Object sfEval(Expression e, Map<String, Object> env) {
        if (e instanceof NotExpression) {                                 // IS-A BooleanExpression: first
            Object v = sfEval(((NotExpression) e).expression, env)
            if (v instanceof Boolean) return !((Boolean) v)
            throw new SfNotClosed('! of a non-boolean')
        }
        if (e instanceof BooleanExpression) return sfEval(((BooleanExpression) e).expression, env)
        if (e instanceof ConstantExpression) {
            Object v = ((ConstantExpression) e).value
            if (v instanceof Number) return ((Number) v).longValue()
            if (v instanceof Boolean || v instanceof String) return v
            if (v == null) return null
            throw new SfNotClosed("literal ${v.class.simpleName} is outside the closed fragment")
        }
        if (e instanceof VariableExpression) {
            String n = ((VariableExpression) e).name
            if (n == 'true') return Boolean.TRUE
            if (n == 'false') return Boolean.FALSE
            if (env.containsKey(n)) return env.get(n)
            throw new SfNotClosed("'${n}' is not a closed value")
        }
        if (e instanceof UnaryMinusExpression) {
            Object v = sfEval(((UnaryMinusExpression) e).expression, env)
            if (v instanceof Long) return -((Long) v)
            throw new SfNotClosed('unary minus of a non-int')
        }
        if (e instanceof TernaryExpression) {
            TernaryExpression te = (TernaryExpression) e
            Object c = sfEval(te.booleanExpression, env)
            if (!(c instanceof Boolean)) throw new SfNotClosed('ternary condition not closed boolean')
            return sfEval(((Boolean) c) ? te.trueExpression : te.falseExpression, env)
        }
        if (e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e
            int op = be.operation.type
            if (op == Types.LOGICAL_AND) {
                Object l = sfEval(be.leftExpression, env)
                if (!(l instanceof Boolean)) throw new SfNotClosed('&& of non-boolean')
                return ((Boolean) l) ? sfEval(be.rightExpression, env) : Boolean.FALSE
            }
            if (op == Types.LOGICAL_OR) {
                Object l = sfEval(be.leftExpression, env)
                if (!(l instanceof Boolean)) throw new SfNotClosed('|| of non-boolean')
                return ((Boolean) l) ? Boolean.TRUE : sfEval(be.rightExpression, env)
            }
            Object l = sfEval(be.leftExpression, env)
            Object r = sfEval(be.rightExpression, env)
            if (l instanceof Long && r instanceof Long) {
                long a = (Long) l, b = (Long) r
                switch (op) {
                    case Types.PLUS: return a + b
                    case Types.MINUS: return a - b
                    case Types.MULTIPLY: return a * b
                    case Types.MOD: case Types.REMAINDER: return b == 0 ? sfDivZero() : a % b
                    case Types.INTDIV: return b == 0 ? sfDivZero() : a.intdiv(b)
                    case Types.COMPARE_LESS_THAN: return a < b
                    case Types.COMPARE_LESS_THAN_EQUAL: return a <= b
                    case Types.COMPARE_GREATER_THAN: return a > b
                    case Types.COMPARE_GREATER_THAN_EQUAL: return a >= b
                    case Types.COMPARE_EQUAL: return a == b
                    case Types.COMPARE_NOT_EQUAL: return a != b
                }
            }
            if (op == Types.COMPARE_EQUAL) return java.util.Objects.equals(l, r)
            if (op == Types.COMPARE_NOT_EQUAL) return !java.util.Objects.equals(l, r)
            throw new SfNotClosed("operator '${be.operation.text}' over non-int operands")
        }
        throw new SfNotClosed("expression ${e.class.simpleName} is outside the closed fragment")
    }

    private static Object sfDivZero() { throw new SfNotClosed('division by zero in closed evaluation') }

    private static class LoopSite {
        Statement loopStmt
        LoopSpec spec
        /** Non-exit prefix statements only — what {@link LoopEncoder#symExec} executes. For the 2nd+ of
         *  SEQUENTIAL annotated loops (Phase 207) this is the FULL preceding history including earlier
         *  loop statements, which the replay summarises (havoc writes, assume inv ∧ ¬guard). */
        List<Statement> prefix
        /** Phase 207 — the statements strictly between the PREVIOUS annotated loop (or method start)
         *  and this loop: the region whose obligations belong to this site. */
        List<Statement> segmentBefore
        /** Phase 207 — the statements strictly between this loop and the NEXT annotated loop (or method
         *  end): discharged under this loop's inv ∧ ¬guard. */
        List<Statement> segmentAfter
        /** Non-exit suffix statements only. */
        List<Statement> suffix
        /** Phase 49 — source-order prefix including early-exit if-statements. */
        List<Statement> originalPrefix
        /** Phase 49 — source-order suffix including early-exit if-statements. */
        List<Statement> originalSuffix
        /** Phase 49 — early-return paths in prefix and suffix, in source order. */
        List<EarlyExit> earlyExits = new ArrayList<EarlyExit>()
    }

    /**
     * Phase 49 — an early-return path through a loop's prefix / suffix region. {@code guard}
     * is the if-condition; {@code result} is the return-expression in the then-branch;
     * {@code priorStmts} captures the non-exit statements that ran before this guard in source
     * order; {@code priorGuards} are the earlier-exit guards (each negated when verifying this
     * exit — "we didn't take any earlier exit"). {@code beforeLoop} marks the region.
     */
    @CompileStatic
    private static class EarlyExit {
        Expression guard
        Expression result
        List<Statement> priorStmts
        List<Expression> priorGuards
        boolean beforeLoop    // legacy: true for prefix, false otherwise (kept for Slice A code)
        String region         // 'prefix' | 'inBody' (Slice B) — 'suffix' deferred
        Statement node
    }

    /**
     * Locate the single top-level annotated loop, returning its {@link LoopSpec}
     * plus the straight-line prefix/suffix around it, or null if there is none.
     * Raises {@link UnsupportedConstructException} (→ "skipped") if the body has
     * more than one — the spike models a single loop.
     */
    private static List<LoopSite> findLoopSites(Statement body) {
        List<Statement> top = topStatements(body)
        List<Integer> idxs = new ArrayList<Integer>()
        for (int i = 0; i < top.size(); i++) {
            if (top.get(i).getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY) != null) idxs.add(i)
        }
        if (idxs.isEmpty()) return Collections.<LoopSite> emptyList()
        List<LoopSite> sites = new ArrayList<LoopSite>()
        for (int s = 0; s < idxs.size(); s++) {
            LoopSite site = buildLoopSite(top, idxs.get(s))
            // Phase 207 — sequential loops: the trimmed segments (between neighbouring loops) own the
            // region obligations; the full prefix (earlier loops included, summarised by the replay)
            // carries establishment. Early exits with multiple sequential loops stay a loud skip (v1).
            int prevEnd = s == 0 ? 0 : idxs.get(s - 1) + 1
            site.segmentBefore = new ArrayList<Statement>(top.subList(prevEnd, idxs.get(s)))
            if (s == 0 && site.spec.init != null) site.segmentBefore.addAll(site.spec.init)
            int nextStart = s + 1 < idxs.size() ? idxs.get(s + 1) : top.size()
            site.segmentAfter = new ArrayList<Statement>(top.subList(idxs.get(s) + 1, nextStart))
            if (idxs.size() > 1 && !site.earlyExits.isEmpty()) {
                throw new UnsupportedConstructException(
                    "early exits combined with multiple sequential annotated loops")
            }
            sites.add(site)
        }
        sites
    }

    private static LoopSite buildLoopSite(List<Statement> top, int idx) {
        LoopSite site = new LoopSite()
        site.loopStmt = top.get(idx)
        site.spec = (LoopSpec) site.loopStmt.getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY)
        site.originalPrefix = new ArrayList<Statement>(top.subList(0, idx))
        // Phase 59 — a desugared for-loop's init runs immediately before the loop, after any
        // real pre-loop statements, so append it to the prefix (the value-flow/establishment
        // walks then see `int i = 0` exactly as they would for a while-shaped loop).
        if (site.spec.init != null) site.originalPrefix.addAll(site.spec.init)
        site.originalSuffix = new ArrayList<Statement>(top.subList(idx + 1, top.size()))
        // Phase 49 (Slice A) — prefix early-exits are partitioned and verified per-path;
        // suffix exits aren't yet supported (would need state-aware {@code ¬guard} interleaving
        // at the right point in the suffix walk; the existing {@code LoopEncoder.resultExpr}
        // will reject return-shaped if-statements with its standard "unsupported statement"
        // diagnostic, which is the right honest-skip behaviour for Slice A's scope).
        site.prefix = partitionEarlyExits(site.originalPrefix, 'prefix', site.earlyExits)
        site.suffix = new ArrayList<Statement>(site.originalSuffix)
        // Phase 49b (Slice B) — partition the loop body's top-level statements similarly,
        // collecting in-body early-exits into the same {@code earlyExits} list with region
        // {@code 'inBody'}. The body's preservation/progress walks then interleave
        // {@code ¬guard} for each exit (handled by {@link #symExecBodyWithExits}).
        if (site.spec.body != null) {
            // Phase 49c — first lift any `return` nested in a tail-position if/else chain into the
            // top-level `if (pathCond) return e` shape, so the binary-search idiom (`else return mid`)
            // is handled by the same Slice B machinery below.
            site.spec.body = desugarTailReturns(site.spec.body)
            partitionEarlyExits(site.spec.body, 'inBody', site.earlyExits)
        }
        return site
    }

    /**
     * Phase 49 (Slice A) — walk a region's top-level statements and split out
     * "early-exit if" shapes ({@code if (cond) return expr;} or
     * {@code if (cond) { return expr; }}, no else). Each such if becomes an
     * {@link EarlyExit} entry; the surrounding always-running statements form the returned
     * trimmed region. Other if-shapes (with non-trivial else, or with then-blocks that
     * don't end with a return) stay in the region as ordinary statements, and the existing
     * {@code LoopEncoder.symExec} path-fact handling (Phase 45c) covers them.
     */
    private static List<Statement> partitionEarlyExits(List<Statement> stmts, String region,
                                                       List<EarlyExit> out) {
        List<Statement> kept = new ArrayList<Statement>()
        List<Expression> priorGuards = new ArrayList<Expression>()
        for (Statement st : stmts) {
            Expression returnExpr = earlyExitReturnFor(st)
            if (returnExpr != null) {
                IfStatement ifs = (IfStatement) st
                EarlyExit ex = new EarlyExit()
                ex.guard = ifs.booleanExpression
                ex.result = returnExpr
                ex.priorStmts = new ArrayList<Statement>(kept)
                ex.priorGuards = new ArrayList<Expression>(priorGuards)
                ex.beforeLoop = (region == 'prefix')
                ex.region = region
                ex.node = st
                out.add(ex)
                priorGuards.add(ifs.booleanExpression)
                // The if-statement itself doesn't run on the no-exit path: don't add to kept.
            } else {
                kept.add(st)
            }
        }
        kept
    }

    /**
     * Phase 49 — return the early-exit return expression if {@code st} matches the
     * {@code if (cond) return e} shape (with no else or empty else, then-branch a single
     * return statement). Otherwise null. The check is deliberately strict: anything more
     * elaborate falls back to the existing path-fact route inside {@link LoopEncoder}.
     */
    private static Expression earlyExitReturnFor(Statement st) {
        if (!(st instanceof IfStatement)) return null
        IfStatement ifs = (IfStatement) st
        // Reject any else-branch (we'd need to model both branches as exits otherwise).
        if (ifs.elseBlock != null && !(ifs.elseBlock instanceof EmptyStatement)) return null
        Statement then = ifs.ifBlock
        // Unwrap a single-statement block.
        if (then instanceof BlockStatement) {
            List<Statement> ss = ((BlockStatement) then).statements
            if (ss.size() == 1) then = ss.get(0)
        }
        if (then instanceof ReturnStatement) {
            return ((ReturnStatement) then).expression
        }
        null
    }

    /**
     * Phase 49c — lift a `return` nested in an if/else(-if) chain in TAIL position of the loop body
     * into the top-level {@code if (pathCond) return e} shape Phase 49b ({@link #partitionEarlyExits})
     * already handles. The textbook binary search ends its body with
     * <pre>
     *   if (a[mid] &lt; value) low = mid + 1
     *   else if (value &lt; a[mid]) high = mid
     *   else return mid
     * </pre>
     * whose return is the deepest {@code else} — invisible to the simple {@code if (g) return e}
     * partition, so the whole loop was skipped loudly. We rewrite the final if-chain into a lifted
     * {@code if (pathCond) return e} per returning leaf ({@code pathCond} = the conjunction of branch
     * guards reaching it) followed by the same chain with each returning leaf replaced by an empty
     * statement (the residual the no-exit walks execute). Sound: the lifted exit fires under exactly the
     * leaf's path condition, and on that path the method has returned, so the residual's empty leaf
     * never runs. Conservative: only a tail-position chain whose returning leaves are <em>bare</em>
     * {@code return e} (no preceding statements in the leaf) is rewritten; any other shape is left
     * untouched so {@link LoopEncoder} still rejects it as an honest skip.
     */
    private static List<Statement> desugarTailReturns(List<Statement> body) {
        if (body == null || body.isEmpty()) return body
        Statement last = body.get(body.size() - 1)
        if (!(last instanceof IfStatement) || !statementContainsReturn(last)) return body
        List<Object[]> leaves = new ArrayList<Object[]>()   // [Expression pathCond, Expression retExpr|null]
        if (!enumerateChainLeaves((IfStatement) last, new ArrayList<Expression>(), leaves)) return body
        List<Statement> lifted = new ArrayList<Statement>()
        for (Object[] leaf : leaves) {
            Expression ret = (Expression) leaf[1]
            if (ret == null) continue   // a continuing leaf — stays only in the residual
            IfStatement liftedIf = new IfStatement(new BooleanExpression((Expression) leaf[0]),
                new ReturnStatement(ret), EmptyStatement.INSTANCE)
            // Stamp a real source position (the tail chain's) — a diagnostic anchored to a synthetic
            // node with no line info is silently dropped by the static type checker.
            liftedIf.setSourcePosition(ret instanceof ASTNode ? (ASTNode) ret : last)
            lifted.add(liftedIf)
        }
        if (lifted.isEmpty()) return body
        List<Statement> out = new ArrayList<Statement>(body.subList(0, body.size() - 1))
        out.addAll(lifted)
        out.add(stripReturns(last))
        out
    }

    /**
     * Walk an if/else chain collecting each leaf's path condition (conjoined) and, for a leaf that is a
     * <em>bare</em> {@code return e}, its return expression (else null for a continuing leaf). Returns
     * false — caller bails, leaving the body untouched — if any leaf that contains a return isn't a bare
     * return (statements precede it, or it's nested in a non-if block), which is outside this slice.
     */
    private static boolean enumerateChainLeaves(Statement stmt, List<Expression> accConds, List<Object[]> out) {
        if (stmt instanceof IfStatement) {
            IfStatement ifs = (IfStatement) stmt
            List<Expression> thenConds = new ArrayList<Expression>(accConds); thenConds.add(ifs.booleanExpression)
            if (!enumerateChainLeaves(ifs.ifBlock, thenConds, out)) return false
            List<Expression> elseConds = new ArrayList<Expression>(accConds)
            elseConds.add(new NotExpression(ifs.booleanExpression))
            Statement elseBlk = ifs.elseBlock
            if (elseBlk == null || elseBlk instanceof EmptyStatement) {
                out.add([conjoin(elseConds), null] as Object[])      // implicit empty else → continuing leaf
                return true
            }
            return enumerateChainLeaves(elseBlk, elseConds, out)
        }
        Statement leaf = stmt
        if (leaf instanceof BlockStatement) {
            List<Statement> ss = ((BlockStatement) leaf).statements
            if (ss.size() == 1) leaf = ss.get(0)              // unwrap `{ return e }` / `{ x = … }`
            else if (ss.any { statementContainsReturn(it) }) return false   // multi-stmt leaf with a return
        }
        if (leaf instanceof ReturnStatement) {
            out.add([conjoin(accConds), ((ReturnStatement) leaf).expression] as Object[])
            return true
        }
        if (statementContainsReturn(leaf)) return false       // a return buried somewhere unexpected
        out.add([conjoin(accConds), null] as Object[])         // ordinary continuing leaf
        true
    }

    /** Conjoin guards into {@code c1 && c2 && …} (left-folded); a single guard is returned as-is. */
    private static Expression conjoin(List<Expression> conds) {
        Expression acc = null
        for (Expression c : conds) {
            acc = (acc == null) ? c : new BinaryExpression(acc, Token.newSymbol(Types.LOGICAL_AND, -1, -1), c)
        }
        acc
    }

    /** Copy of an if/else chain with every bare-{@code return} leaf replaced by an empty statement. */
    private static Statement stripReturns(Statement stmt) {
        if (stmt instanceof IfStatement) {
            IfStatement ifs = (IfStatement) stmt
            Statement nElse = ifs.elseBlock == null ? null : stripReturns(ifs.elseBlock)
            return new IfStatement(ifs.booleanExpression, stripReturns(ifs.ifBlock),
                nElse == null ? EmptyStatement.INSTANCE : nElse)
        }
        if (stmt instanceof ReturnStatement) return EmptyStatement.INSTANCE
        if (stmt instanceof BlockStatement) {
            List<Statement> ss = ((BlockStatement) stmt).statements
            if (ss.size() == 1 && ss.get(0) instanceof ReturnStatement) return EmptyStatement.INSTANCE
        }
        stmt
    }

    /** True if {@code st} contains a {@code return} anywhere in its if/block structure. */
    private static boolean statementContainsReturn(Statement st) {
        if (st == null) return false
        if (st instanceof ReturnStatement) return true
        if (st instanceof IfStatement) {
            return statementContainsReturn(((IfStatement) st).ifBlock) ||
                   statementContainsReturn(((IfStatement) st).elseBlock)
        }
        if (st instanceof BlockStatement) {
            return ((BlockStatement) st).statements.any { statementContainsReturn(it) }
        }
        false
    }

    private static List<Statement> topStatements(Statement body) {
        if (body instanceof BlockStatement) {
            return new ArrayList<Statement>(((BlockStatement) body).statements)
        }
        return body != null ? ([body] as List<Statement>) : Collections.<Statement> emptyList()
    }

    /**
     * Discharge the inductive proof for an annotated loop: establishment,
     * preservation, optional progress (@Decreases), and — when the method has an
     * {@code @Ensures} — the use obligation that the post-loop state proves the
     * postcondition. Each is an independent solver context with a fresh
     * {@link Encoder}, so any variable a context does not bind is a fresh
     * unconstrained value: that is exactly "havoc the loop-modified variables".
     */
    private void verifyLoop(MethodNode node, LoopSite site, boolean tail = true) {
        Expression reqAst = findRequires(node) != null ? contractAstFor(node, 'requires') : null
        // Phase 207 — only the LAST of sequential annotated loops carries the @Ensures / early-exit /
        // post-loop-use checks; earlier sites verify establishment/preservation/progress only.
        Expression postAst = (tail && findEnsures(node) != null) ? contractAstFor(node, 'ensures') : null
        // Phase 65 — for a for-in, an invariant clause referencing the loop variable is checked at
        // body-entry (x bound to the current element), exactly as groovy-contracts does at runtime —
        // not at the loop head, where x is undefined (which spuriously "failed" on the empty
        // collection, the one case the runtime never checks). Partition such clauses out of the
        // classic VCs into a per-element check; the x-free clauses stay inductive as usual.
        List<Expression> perElement = partitionForInPerElement(site)
        // Phase 64 — the precondition conjuncts the loop body provably can't invalidate, sound to
        // assume in preservation/progress (computed once; establishment/use already see the full reqAst).
        List<Expression> stableReqs = loopStableRequires(reqAst, site)
        // The `.count(v)` values the loop tracks — from its @Invariant (where a permutation property lives) and
        // the method @Requires/@Ensures — so an inline array store in the body emits the per-store count law
        // (LoopEncoder reads this thread-local; held as AST since each VC translates in its own session).
        List<Expression> loopCountVals = new ArrayList<Expression>()
        loopCountVals.addAll(countValueArgs(postAst))
        loopCountVals.addAll(countValueArgs(reqAst))
        for (Expression inv : site.spec.invariants) loopCountVals.addAll(countValueArgs(inv))
        List<Expression> prevCountVals = LoopEncoder.countVals.get()
        LoopEncoder.countVals.set(loopCountVals)
        try {
            checkEstablishment(node, site, reqAst)
            checkPreservation(node, site, stableReqs)
            if (site.spec.variant != null) checkProgress(node, site, stableReqs)
            // Phase 91 — a nested annotated loop in the outer body: the outer VCs above already summarised
            // it; now discharge its own establish/preserve/progress (without which the summary is unsound).
            verifyNestedLoops(node, site, reqAst, postAst)
            if (!perElement.isEmpty()) checkForInElement(node, site, perElement, stableReqs)
            // A for-in / `.each` standing on the auto bounds invariant alone can prove the postcondition only
            // when the body accumulates nothing — `0 <= idx <= size` doesn't frame a variable the body writes,
            // so an accumulating body leaves it havoc'd and the postcondition would *spuriously* refute. Loud-skip
            // it instead (honest: such a loop needs an @Invariant, which `.each` can't carry — a parse error).
            if (postAst != null && autoOnlyBodyAccumulates(site)) {
                addStaticTypeError(Reporter.formatLoopSkipped(node.name,
                    'an auto-bounds-only for-in/.each whose body writes a variable the postcondition depends on ' +
                    'needs an @Invariant to frame it (not attachable to a `.each` statement)'), site.loopStmt)
            } else if (postAst != null) checkUse(node, site, reqAst, postAst)
            // Phase 49 — discharge each early-exit's @Ensures on its own path (only relevant
            // when the method has an @Ensures to prove).
            if (postAst != null) {
                for (EarlyExit ex : site.earlyExits) {
                    checkEarlyExit(node, site, ex, reqAst, postAst)
                }
            }
        } catch (UnsupportedConstructException e) {
            addStaticTypeError(Reporter.formatLoopSkipped(node.name, e.message), site.loopStmt)
        } finally {
            LoopEncoder.countVals.set(prevCountVals)
        }
    }

    // ── Phase 64 — loop-stable @Requires ───────────────────────────────────────────────────────
    // Preservation/progress deliberately omit @Requires (a precondition over mutable state goes stale
    // mid-loop). But a conjunct referencing only state the loop *doesn't* modify stays true on every
    // iteration and is sound to assume — which unlocks element reasoning over a collection the loop
    // merely reads (`xs.every { it >= 0 }` instantiated at the current element). Soundness rests on the
    // write-set being a sound *over*-approximation: a conjunct is dropped if any of its free names
    // might be written, and *all* conjuncts are dropped if the body has a construct whose writes can't
    // be bounded (an unrecognised call/statement → loopWriteSet returns null).

    private static final Set<String> LOOP_MUTATORS = [
        'add','remove','put','clear','set','addAll','removeAll','retainAll','putAll','push','pop',
        'poll','offer','removeLast','removeFirst','addFirst','addLast','removeAt','putIfAbsent'] as Set

    private static final Set<String> LOOP_PURE_READS = [
        'size','length','get','getAt','contains','containsKey','containsValue','isEmpty','indexOf',
        'lastIndexOf','charAt','substring','keySet','values','entrySet','sum','max','min','count',
        'every','any','find','findAll','collect','intdiv','mod','remainder','abs','compareTo','equals',
        'startsWith','endsWith','toUpperCase','toLowerCase','first','last','head','tail','of','range',
        'boundedBy','boundedCount','intValue','longValue','containsWithinBounds'] as Set

    /**
     * Phase 65 — for a for-in loop, split the invariant clauses that reference the loop variable out
     * of {@code spec.invariants} (mutating it to the x-free clauses the classic loop-head VCs use) and
     * return them for the per-element check. A no-op for non-for-in loops and for clauses that don't
     * mention the loop variable.
     */
    private static List<Expression> partitionForInPerElement(LoopSite site) {
        String x = site.spec.forInVar
        if (x == null) return Collections.<Expression>emptyList()
        // Split each invariant into top-level conjuncts first, so a mixed `s >= 0 && x >= 0` separates
        // its accumulator clause (inductive, loop-head) from its per-element clause (over the element).
        List<Expression> conjuncts = new ArrayList<Expression>()
        for (Expression inv : site.spec.invariants) splitConjuncts(inv, conjuncts)
        List<Expression> perElement = new ArrayList<Expression>()
        List<Expression> xFree = new ArrayList<Expression>()
        for (Expression c : conjuncts) {
            (freeNames(c).contains(x) ? perElement : xFree).add(c)
        }
        site.spec.invariants = xFree
        perElement
    }

    /**
     * Phase 65 — verify a for-in's per-element invariant clauses (those referencing the loop variable).
     * At an arbitrary valid iteration — the x-free invariants (including {@code 0 <= idx <= size}) and
     * the guard ({@code idx < size}, so {@code 0 <= idx < size}) hold, the loop-stable preconditions
     * hold, and {@code x = xs[idx]} — each clause must hold. On an empty collection the antecedent is
     * unsatisfiable, so the check is vacuous (matching the runtime, which never reaches the body).
     */
    private void checkForInElement(MethodNode node, LoopSite site, List<Expression> perElement,
                                   List<Expression> stableReqs) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            s.assertExpr(LoopEncoder.conj(enc, s, site.spec.invariants))   // x-free invariants + index bounds
            s.assertExpr(LoopEncoder.tr(enc, site.spec.guard, "guard"))    // idx < size
            assumeStableRequires(s, enc, stableReqs)
            assumeClassInvariants(s, enc)
            if (site.spec.forInBind != null) LoopEncoder.symExec([site.spec.forInBind], enc, s)  // x = xs[idx]
            s.assertExpr(s.not(LoopEncoder.conj(enc, s, perElement)))
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                String text = perElement.collect { it.text }.join(' && ')
                addStaticTypeError(Reporter.formatLoopPerElement(node.name, text, r), site.loopStmt)
            }
        } finally { try { s.close() } catch (Throwable ignored) {} }
    }

    /** The @Requires conjuncts referencing only loop-stable state — sound to assume mid-loop. */
    private static List<Expression> loopStableRequires(Expression reqAst, LoopSite site) {
        if (reqAst == null) return Collections.<Expression>emptyList()
        Set<String> writes = loopWriteSet(site)
        if (writes == null) return Collections.<Expression>emptyList()   // unbounded writes → assume nothing
        List<Expression> conjuncts = new ArrayList<Expression>()
        splitConjuncts(reqAst, conjuncts)
        List<Expression> stable = new ArrayList<Expression>()
        for (Expression c : conjuncts) {
            if (Collections.disjoint(freeNames(c), writes)) stable.add(c)
        }
        stable
    }

    private static void assumeStableRequires(SmtSession s, Encoder enc, List<Expression> stable) {
        for (Expression c : stable) {
            Object h = enc.translate(c)
            if (h != null) s.assertExpr(h)
        }
    }

    /** Split a (possibly nested) `a && b && c` into its conjuncts; anything else is a single conjunct. */
    private static void splitConjuncts(Expression e, List<Expression> out) {
        if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.LOGICAL_AND) {
            splitConjuncts(((BinaryExpression) e).leftExpression, out)
            splitConjuncts(((BinaryExpression) e).rightExpression, out)
        } else if (e instanceof BooleanExpression) {
            splitConjuncts(((BooleanExpression) e).expression, out)
        } else {
            out.add(e)
        }
    }

    /** Free variable / `this`-field names a contract clause references. Over-collects closure
     *  parameters (e.g. `it`), which is sound — it only makes a clause *more* likely to be dropped. */
    private static Set<String> freeNames(Expression e) {
        final Set<String> out = new HashSet<String>()
        if (e == null) return out
        e.visit(new ClassCodeVisitorSupport() {
            protected SourceUnit getSourceUnit() { null }
            @Override void visitVariableExpression(VariableExpression ve) {
                if (ve.name != 'this') out.add(ve.name)
            }
            @Override void visitPropertyExpression(PropertyExpression pe) {
                if (pe.objectExpression instanceof VariableExpression &&
                        ((VariableExpression) pe.objectExpression).name == 'this') {
                    out.add(pe.propertyAsString)   // this.field → field
                }
                super.visitPropertyExpression(pe)
            }
        })
        out
    }

    /**
     * Names the loop's prefix + body may write, or null when it contains a construct whose write
     * effects can't be bounded (→ the caller assumes no precondition, the always-sound default). A
     * sound over-approximation: surplus names only drop more conjuncts.
     */
    /**
     * True for an auto-bounds-only for-in / {@code .each} whose body writes a variable other than the loop
     * variable and the synthetic index — i.e. it accumulates. The auto invariant ({@code 0 <= idx <= size})
     * frames neither, so the post-loop value is havoc and any postcondition over it would spuriously refute;
     * the caller loud-skips the use check instead. A body whose writes can't be bounded (unknown call) is
     * treated as accumulating too — the sound default. The loop variable's {@code x = xs[idx]} binding and the
     * {@code idx = idx + 1} update (both synthetic) are excluded so a pure per-element body counts as empty.
     */
    private static boolean autoOnlyBodyAccumulates(LoopSite site) {
        if (!site.spec.autoInvariantOnly) return false
        Set<String> writes = new HashSet<String>()
        if (!collectWritesStmts(site.spec.body, writes)) return true   // unbounded body effect → treat as accumulating
        writes.remove(site.spec.forInVar)
        writes.remove(ContractExpansionTransform.FOR_IN_INDEX)
        return !writes.isEmpty()
    }

    private static Set<String> loopWriteSet(LoopSite site) {
        Set<String> ws = new HashSet<String>()
        if (!collectWritesStmts(site.prefix, ws)) return null
        if (!collectWritesStmts(site.spec.body, ws)) return null
        ws
    }

    private static boolean collectWritesStmts(List<Statement> stmts, Set<String> ws) {
        if (stmts == null) return true
        for (Statement st : stmts) if (!collectWritesStmt(st, ws)) return false
        true
    }

    private static boolean collectWritesStmt(Statement st, Set<String> ws) {
        if (st == null || st instanceof EmptyStatement) return true
        if (st instanceof BlockStatement) return collectWritesStmts(((BlockStatement) st).statements, ws)
        if (st instanceof IfStatement) {
            IfStatement ifs = (IfStatement) st
            return collectWritesExpr(ifs.booleanExpression, ws) &&
                   collectWritesStmt(ifs.ifBlock, ws) &&
                   (ifs.elseBlock == null || collectWritesStmt(ifs.elseBlock, ws))
        }
        if (st instanceof ExpressionStatement) return collectWritesExpr(((ExpressionStatement) st).expression, ws)
        // A `return e` exits the loop — it writes nothing for the next iteration beyond whatever `e`
        // evaluates (pure in-fragment). Recognising it keeps the write-set finite for bodies with
        // early returns (e.g. the desugared binary search), so loop-stable @Requires aren't dropped.
        if (st instanceof ReturnStatement) return collectWritesExpr(((ReturnStatement) st).expression, ws)
        // Phase 91 — a nested loop writes whatever its guard + body do; recurse so the outer write-set
        // stays a sound over-approximation (and the inner-loop case below isn't dropped as "unknown").
        if (st instanceof LoopingStatement) {
            LoopingStatement ls = (LoopingStatement) st
            Expression g = (ls instanceof WhileStatement) ? ((WhileStatement) ls).booleanExpression :
                           (ls instanceof DoWhileStatement) ? ((DoWhileStatement) ls).booleanExpression : null
            if (g != null && !collectWritesExpr(g, ws)) return false
            return collectWritesStmt(ls.loopBlock, ws)
        }
        false   // unknown statement → bail
    }

    private static boolean collectWritesExpr(Expression e, Set<String> ws) {
        if (e == null) return true
        if (e instanceof ConstantExpression || e instanceof VariableExpression ||
            e instanceof ClassExpression) return true
        if (e instanceof BooleanExpression) return collectWritesExpr(((BooleanExpression) e).expression, ws)
        if (e instanceof NotExpression) return collectWritesExpr(((NotExpression) e).expression, ws)
        if (e instanceof UnaryMinusExpression) return collectWritesExpr(((UnaryMinusExpression) e).expression, ws)
        if (e instanceof PropertyExpression) return collectWritesExpr(((PropertyExpression) e).objectExpression, ws)
        if (e instanceof TernaryExpression) {
            TernaryExpression te = (TernaryExpression) e
            return collectWritesExpr(te.booleanExpression, ws) &&
                   collectWritesExpr(te.trueExpression, ws) &&
                   collectWritesExpr(te.falseExpression, ws)
        }
        if (e instanceof PostfixExpression) return recordTarget(((PostfixExpression) e).expression, ws)
        if (e instanceof PrefixExpression)  return recordTarget(((PrefixExpression) e).expression, ws)
        if (e instanceof DeclarationExpression) {
            DeclarationExpression de = (DeclarationExpression) e
            if (!(de.leftExpression instanceof VariableExpression)) return false
            ws.add(((VariableExpression) de.leftExpression).name)
            return collectWritesExpr(de.rightExpression, ws)
        }
        if (e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e
            int t = be.operation.type
            if (Types.ofType(t, Types.ASSIGNMENT_OPERATOR)) {
                return recordTarget(be.leftExpression, ws) && collectWritesExpr(be.rightExpression, ws)
            }
            switch (t) {
                case Types.PLUS: case Types.MINUS: case Types.MULTIPLY: case Types.DIVIDE:
                case Types.MOD: case Types.LEFT_SQUARE_BRACKET:
                case Types.COMPARE_EQUAL: case Types.COMPARE_NOT_EQUAL:
                case Types.COMPARE_LESS_THAN: case Types.COMPARE_LESS_THAN_EQUAL:
                case Types.COMPARE_GREATER_THAN: case Types.COMPARE_GREATER_THAN_EQUAL:
                case Types.LOGICAL_AND: case Types.LOGICAL_OR:
                    return collectWritesExpr(be.leftExpression, ws) && collectWritesExpr(be.rightExpression, ws)
                default:
                    return false   // shift/power/membership/etc. → bail (could be a collection mutation)
            }
        }
        if (e instanceof MethodCallExpression) {
            MethodCallExpression mce = (MethodCallExpression) e
            String m = mce.methodAsString
            if (LOOP_MUTATORS.contains(m)) {
                if (!recordTarget(mce.objectExpression, ws)) return false
            } else if (!LOOP_PURE_READS.contains(m)) {
                return false   // unknown call → can't bound effects → bail
            } else {
                if (!collectWritesExpr(mce.objectExpression, ws)) return false
            }
            return collectWritesArgs(mce.arguments, ws)
        }
        false   // unknown expression kind → bail
    }

    private static boolean collectWritesArgs(Expression args, Set<String> ws) {
        if (!(args instanceof TupleExpression)) return true
        for (Expression a : ((TupleExpression) args).expressions) if (!collectWritesExpr(a, ws)) return false
        true
    }

    /** Record an assignment/mutation target's base name (a local, a `this.field`, or `a[i]`'s array). */
    private static boolean recordTarget(Expression lhs, Set<String> ws) {
        if (lhs instanceof VariableExpression) { ws.add(((VariableExpression) lhs).name); return true }
        if (lhs instanceof PropertyExpression) { ws.add(((PropertyExpression) lhs).propertyAsString); return true }
        if (lhs instanceof BinaryExpression &&
                ((BinaryExpression) lhs).operation.type == Types.LEFT_SQUARE_BRACKET) {
            Expression recv = ((BinaryExpression) lhs).leftExpression
            if (recv instanceof VariableExpression) { ws.add(((VariableExpression) recv).name); return true }
        }
        false   // unusual target → bail
    }

    /**
     * Phase 49 — verify the @Ensures on an early-exit path:
     * <ol>
     *   <li>Assume {@code @Requires} and class invariants.</li>
     *   <li>For a <b>prefix</b> exit: assume {@code ¬each-earlier-prefix-guard}, sym-exec the
     *       prefix priors (the non-exit statements that ran before this exit), assume this
     *       guard, bind {@code result} to the return expression.</li>
     *   <li>For a <b>suffix</b> exit: same as a prefix non-exit run (full prefix, assuming
     *       all prefix guards' negations), then assume the loop invariant and {@code ¬loop-guard},
     *       then sym-exec suffix priors with their earlier guards negated, assume this guard,
     *       bind {@code result}.</li>
     *   <li>Assert {@code ¬@Ensures}; check unsat.</li>
     * </ol>
     */
    private void checkEarlyExit(MethodNode node, LoopSite site, EarlyExit ex,
                                Expression reqAst, Expression postAst) {
        // The standard check: a prefix exit, or an in-body exit on *some* iteration (state = invariant ∧ guard).
        checkEarlyExitPath(node, site, ex, reqAst, postAst, false)
        // Phase 88b — a do-while (`do B while (G)` ≡ `B; while (G) B`) runs its body once before the first
        // guard/invariant, so an in-body exit can fire on the FIRST iteration from the *entry* state, where
        // the invariant isn't established and the guard isn't checked. The inBody path above assumes
        // (invariant ∧ guard); on a do-while's first pass that assumption can be false-at-entry and
        // *vacuously* prove a wrong exit @Ensures (a latent unsoundness). So check the exit again from
        // @Requires + the loop prefix, assuming NO invariant/guard — iter 1 here, iters ≥ 2 above.
        if (ex.region == 'inBody' && site.spec.isDoWhile) {
            checkEarlyExitPath(node, site, ex, reqAst, postAst, true)
        }
    }

    private void checkEarlyExitPath(MethodNode node, LoopSite site, EarlyExit ex,
                                    Expression reqAst, Expression postAst, boolean doWhileFirstIter) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            if (reqAst != null) s.assertExpr(LoopEncoder.tr(enc, reqAst, "precondition"))
            assumeIntJvmBounds(s, enc)
            assumeClassInvariants(s, enc)
            if (ex.region == 'prefix') {
                // Assume each earlier prefix-exit's guard is false (we got here, not there).
                for (Expression g : ex.priorGuards) {
                    Object gh = enc.translate(g)
                    if (gh != null) s.assertExpr(s.not(gh))
                }
                LoopEncoder.symExec(ex.priorStmts, enc, s)
            } else if (ex.region == 'inBody') {
                if (doWhileFirstIter) {
                    // First iteration of a do-while: the body-entry state is the loop-*entry* state
                    // (prefix-exit guards false, then the prefix), exactly as checkEstablishment sets up.
                    // The invariant isn't established yet and the guard isn't checked, so assume neither.
                    for (EarlyExit pe : site.earlyExits) {
                        if (pe.beforeLoop) {
                            Object gh = enc.translate(pe.guard)
                            if (gh != null) s.assertExpr(s.not(gh))
                        }
                    }
                    LoopEncoder.symExec(site.prefix, enc, s)
                } else {
                    // Phase 49b — in-body exit on *some* (non-first) iteration. The body-entry state is
                    // whatever satisfies the invariant — NOT the post-prefix state (the invariant is the
                    // abstraction that hides "how many iterations ran"). Mirrors checkPreservation/Progress.
                    s.assertExpr(LoopEncoder.conj(enc, s, site.spec.invariants))
                    s.assertExpr(LoopEncoder.tr(enc, site.spec.guard, "guard"))
                }
                // Walk the body up to ex.node, interleaving ¬each-prior-in-body-guard with
                // sym-exec of non-exit body statements:
                for (Statement st : site.spec.body) {
                    if (st === ex.node) break
                    Expression retExpr = earlyExitReturnFor(st)
                    if (retExpr != null) {
                        Object gh = enc.translate(((IfStatement) st).booleanExpression)
                        if (gh != null) s.assertExpr(s.not(gh))
                    } else {
                        LoopEncoder.symExec([st] as List<Statement>, enc, s)
                    }
                }
            } else {
                // 'suffix' region — deferred. Honest skip.
                return
            }
            // Assume the exit's own guard (we did take this exit).
            Object guardH = enc.translate(ex.guard)
            if (guardH != null) s.assertExpr(guardH)
            // Bind result to the return expression (factory-aware, mirroring checkUse): a tuple / list-literal
            // / map-literal return (`return Tuple.tuple(i, j)`) records result's slots so `result.v1`/`.v2`
            // (and `result.size()`/`result[k]`) fold in the @Ensures; otherwise the scalar-handle binding +
            // size/array alias. Phase 110 — the early-exit path previously bound only the scalar handle, so a
            // tuple-returning in-body/inner exit couldn't resolve its slot accessors.
            if (ex.result == null || (!enc.tryRecordFactoryAssign('result', ex.result) &&
                                      !enc.tryRecordSetBinopAssign('result', ex.result))) {
                Object resH = enc.translate(ex.result)
                if (resH != null) enc.bind('result', resH)
                aliasResultToReturnedListLocal(s, enc, ex.result)
            }
            Object post = enc.translateGoal(postAst)
            if (post == null) {
                addStaticTypeError(Reporter.formatPostconditionSkipped(node.name,
                    "early-exit postcondition is outside fragment"), ex.node)
                return
            }
            s.assertExpr(s.not(post))
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(
                    withRepro(Reporter.formatPostconditionFailure(node.name, postAst.text, r), r, 'AssertionError'), ex.node)
            }
        } finally { try { s.close() } catch (Throwable ignored) {} }
    }

    /**
     * Phase 15a — assume each pre-filtered class invariant as a method-entry fact in the given
     * session. Used by every loop VC and (in lifted form) by {@link #assumeContext} /
     * {@link #dischargeVfObligation} / {@link #dischargeSeeded}. Soundness in establishment / use:
     * direct (invariants are method-entry truths). In preservation / progress / body-internal
     * obligations: relies on the loop body not modifying invariant-referenced fields (a frame
     * property not yet checked here — a known unsoundness shared with how implicit obligations
     * inside the body assume invariants). Future frame analysis can tighten this.
     */
    /**
     * Phase 15b — at constructor entry, default-initialise Int-like instance fields to {@code 0}
     * to match JVM semantics ({@code int count} starts at 0 before any assignment). Without this,
     * an empty constructor on a class with {@code @Invariant({ count >= 0 })} would refute (the
     * field is unconstrained, so could be -1) — a false positive. Reference/Set/Map/array fields
     * are left unconstrained; the constructor body is expected to initialise them explicitly when
     * the invariant requires it. Static fields skipped.
     */
    private void initFieldDefaults(SmtSession s, Encoder enc, MethodNode node) {
        ClassNode dc = node?.declaringClass
        if (dc == null) return
        for (FieldNode f : dc.fields) {
            if (f.isStatic()) continue
            if (isIntElement(f.type)) {
                s.assertExpr(s.eq(enc.varFor(f.name), s.intLit(0L)))
            }
        }
    }

    private void assumeClassInvariants(SmtSession s, Encoder enc) {
        // Phase 15b — a constructor doesn't get to *assume* the invariant at entry; the invariant
        // hasn't been established yet. The exit obligation still proves it (handled directly in
        // checkPath when classInvs are conjoined into the goal).
        if (currentIsConstructor) return
        for (Expression inv : currentClassInvariants) {
            Object h = enc.translate(inv)
            if (h != null) {
                s.assertExpr(h)
                if (Reporter.EXPLAIN) s.explainNoteFact('@Invariant ' + inv.text, h)
            }
        }
        // Phase 45 — for each class-typed parameter, assume the parameter's class invariants under
        // a receiver context so {@code count >= 0} in Counter's invariant becomes {@code c$count >= 0}
        // when verifying a method that takes a {@code Counter c}. Sound: the caller's contract is
        // "if you give me a Counter, you give me one whose invariants hold"; that's the standard
        // OO contract every cross-class call site rests on.
        assumeForeignReceiverInvariants(s, enc)
    }

    /**
     * Phase 45 — walk {@link #currentObjectParams}, look up each receiver's class invariants, and
     * assume each one translated under that receiver context. No-op if no class-typed parameters
     * carry invariants. Sound under the no-aliasing assumption (a non-goal of this project).
     */
    private void assumeForeignReceiverInvariants(SmtSession s, Encoder enc) {
        for (Map.Entry<String, ClassNode> e : currentObjectParams.entrySet()) {
            String recvName = e.key
            ClassNode recvType = e.value
            List<Expression> invs = classInvariantTexts(recvType)
            if (invs.isEmpty()) continue
            Set<String> fields = new LinkedHashSet<String>()
            List<FieldNode> fs = recvType.fields
            if (fs != null) for (FieldNode f : fs) fields.add(f.name)
            for (Expression inv : invs) {
                Object h = enc.translateUnderReceiver(inv, recvName, fields)
                if (h != null) s.assertExpr(h)
            }
        }
    }

    /** Establishment: precondition ∧ class invariants ∧ prefix ⇒ invariant.
     *  Phase 49 — assume {@code ¬each prefix early-exit guard} (the loop is only reached on
     *  the no-exit-taken path). */
    private void checkEstablishment(MethodNode node, LoopSite site, Expression reqAst) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            if (reqAst != null) s.assertExpr(LoopEncoder.tr(enc, reqAst, "precondition"))
            assumeIntJvmBounds(s, enc)
            assumeClassInvariants(s, enc)
            for (EarlyExit ex : site.earlyExits) {
                if (ex.beforeLoop) {
                    Object gh = enc.translate(ex.guard)
                    if (gh != null) s.assertExpr(s.not(gh))
                }
            }
            LoopEncoder.symExec(site.prefix, enc, s)
            // Phase 88 — a do-while (`do B while (G)` ≡ `B; while (G) B`) runs its body once before the
            // first guard/invariant check, so the invariant must hold AFTER that first iteration, not at
            // loop entry. Execute the body once here (no guard assumed — the first pass is unconditional)
            // before checking the invariant. Without this, do-while was treated as while and a vacuously-
            // preserved false invariant could be "established" pre-body, silently proving a wrong spec.
            if (site.spec.isDoWhile) symExecBodyWithExits(site, enc, s)
            s.assertExpr(s.not(LoopEncoder.conj(enc, s, site.spec.invariants)))
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(
                    Reporter.formatLoopEstablishment(node.name, invText(site), r, site.spec.isDoWhile), site.loopStmt)
            }
        } finally { try { s.close() } catch (Throwable ignored) {} }
    }

    /** Preservation: invariant ∧ guard ∧ class invariants ∧ one body iteration ⇒ invariant still holds.
     *  Phase 49b — when the body has in-body early-exits, walk it interleaving sym-exec of
     *  non-exit statements with {@code ¬each-in-body-guard} (the preservation check fires
     *  only on the "no early-exit taken" path; each exit's @Ensures is verified separately). */
    private void checkPreservation(MethodNode node, LoopSite site, List<Expression> stableReqs) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            s.assertExpr(LoopEncoder.conj(enc, s, site.spec.invariants))
            s.assertExpr(LoopEncoder.tr(enc, site.spec.guard, "guard"))
            assumeStableRequires(s, enc, stableReqs)   // Phase 64 — loop-stable precondition facts
            assumeClassInvariants(s, enc)
            symExecBodyWithExits(site, enc, s)
            // Re-translating the invariant reads the post-body bindings → inv'.
            s.assertExpr(s.not(LoopEncoder.conj(enc, s, site.spec.invariants)))
            CheckResult r = s.check()
            // Phase 126 — surface the offending array element (post-body value vs the per-element spec) before
            // rendering; `enc` here holds the post-body array bindings.
            if (r.status == CheckResult.Status.REFUTED) appendOffendingElements(r, enc, s, site.spec.invariants)
            r = shown(r)
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(
                    Reporter.formatLoopPreservation(node.name, invText(site), r), site.loopStmt)
            }
        } finally { try { s.close() } catch (Throwable ignored) {} }
    }

    // ---- Phase 126: surface the offending array element for an element-wise refutation ----

    /**
     * For each invariant conjunct shaped {@code (range).every { p -> arr[p] == E }}, walk the (small) array in
     * the live model and append the first {@code arr[k]} whose current value disagrees with the per-element
     * spec {@code E[p := k]} — e.g. {@code r[0] = "🥤" — the spec requires "🐝"}. Best-effort: any failure
     * leaves the diagnostic untouched.
     */
    private void appendOffendingElements(CheckResult r, Encoder enc, SmtSession s, List<Expression> invariants) {
        if (r == null || r.status != CheckResult.Status.REFUTED) return
        try {
            List<Object[]> clauses = new ArrayList<Object[]>()
            for (Expression inv : invariants) collectEveryElementClauses(inv, clauses)
            for (Object[] c : clauses) {
                String arr = (String) c[0]; String param = (String) c[1]; Expression expected = (Expression) c[2]
                Long szL = r.counterexample.get(arr + '.size')
                if (szL == null) continue
                long sz = Math.min(szL, 16L)
                Object arrHandle
                try { arrHandle = enc.arrayFor(arr) } catch (Throwable ignored) { continue }
                if (arrHandle == null) continue
                for (long k = 0; k < sz; k++) {
                    Object idx = s.intLit(k)
                    String actual = s.evalDisplay(s.select(arrHandle, idx))
                    Object expH = enc.translateWith(expected, [(param): idx] as Map<String, Object>)
                    String exp = expH == null ? null : s.evalDisplay(expH)
                    if (actual != null && exp != null && actual != exp) {
                        r.notes.add("${arr}[${k}] = ${actual} — the spec requires ${exp}".toString())
                        break   // first offending element per clause is enough
                    }
                }
            }
        } catch (Throwable ignored) {
        }
    }

    /** Split a contract's top-level {@code &&} conjuncts, collecting each {@code .every}-element clause. */
    private static void collectEveryElementClauses(Expression e, List<Object[]> out) {
        if (e instanceof BooleanExpression) { collectEveryElementClauses(((BooleanExpression) e).expression, out); return }
        if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.LOGICAL_AND) {
            collectEveryElementClauses(((BinaryExpression) e).leftExpression, out)
            collectEveryElementClauses(((BinaryExpression) e).rightExpression, out)
            return
        }
        Object[] clause = asEveryElementClause(e)
        if (clause != null) out.add(clause)
    }

    /** If {@code e} is {@code (range).every { p -> arr[p] == E }}, returns {@code [arr, p, E]}; else null. */
    private static Object[] asEveryElementClause(Expression e) {
        if (!(e instanceof MethodCallExpression)) return null
        MethodCallExpression mc = (MethodCallExpression) e
        if (mc.methodAsString != 'every' || !(mc.arguments instanceof ArgumentListExpression)) return null
        List<Expression> args = ((ArgumentListExpression) mc.arguments).expressions
        if (args.size() != 1 || !(args.get(0) instanceof ClosureExpression)) return null
        ClosureExpression cl = (ClosureExpression) args.get(0)
        String param = (cl.parameters != null && cl.parameters.length > 0) ? cl.parameters[0].name : 'it'
        Expression body = closureSoleExpr(cl)
        if (body instanceof BooleanExpression) body = ((BooleanExpression) body).expression
        if (!(body instanceof BinaryExpression) || ((BinaryExpression) body).operation.type != Types.COMPARE_EQUAL) return null
        BinaryExpression cmp = (BinaryExpression) body
        String arr = subscriptArrayName(cmp.leftExpression, param)
        Expression expected = cmp.rightExpression
        if (arr == null) { arr = subscriptArrayName(cmp.rightExpression, param); expected = cmp.leftExpression }
        arr == null ? null : ([arr, param, expected] as Object[])
    }

    /** The array name of an {@code arr[param]} subscript; else null. */
    private static String subscriptArrayName(Expression e, String param) {
        if (!(e instanceof BinaryExpression)) return null
        BinaryExpression be = (BinaryExpression) e
        if (be.operation.type != Types.LEFT_SQUARE_BRACKET) return null
        if (!(be.leftExpression instanceof VariableExpression) || !(be.rightExpression instanceof VariableExpression)) return null
        ((VariableExpression) be.rightExpression).name == param ? ((VariableExpression) be.leftExpression).name : null
    }

    private static Expression closureSoleExpr(ClosureExpression cl) {
        if (!(cl.code instanceof BlockStatement)) return null
        List<Statement> ss = ((BlockStatement) cl.code).statements
        if (ss.size() != 1) return null
        Statement st = ss.get(0)
        if (st instanceof ExpressionStatement) return ((ExpressionStatement) st).expression
        if (st instanceof ReturnStatement) return ((ReturnStatement) st).expression
        null
    }

    /** Progress: invariant ∧ guard ∧ class invariants ⇒ the variant strictly decreases and stays ≥ 0.
     *  Phase 49b — same body-walk treatment as preservation: progress is checked on the
     *  "no early-exit taken" path. */
    private void checkProgress(MethodNode node, LoopSite site, List<Expression> stableReqs) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            s.assertExpr(LoopEncoder.conj(enc, s, site.spec.invariants))
            s.assertExpr(LoopEncoder.tr(enc, site.spec.guard, "guard"))
            assumeStableRequires(s, enc, stableReqs)   // Phase 64 — loop-stable precondition facts
            assumeClassInvariants(s, enc)
            Object oldV = LoopEncoder.tr(enc, site.spec.variant, "variant")
            symExecBodyWithExits(site, enc, s)
            Object newV = LoopEncoder.tr(enc, site.spec.variant, "variant")
            s.assertExpr(s.not(s.and([s.lt(newV, oldV), s.ge(newV, s.intLit(0L))])))
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(
                    Reporter.formatLoopProgress(node.name, site.spec.variant.text, r), site.loopStmt)
            }
        } finally { try { s.close() } catch (Throwable ignored) {} }
    }

    // ── Phase 91 — nested loops ─────────────────────────────────────────────────────────────────
    // An annotated loop inside the outer loop's body is verified compositionally. The outer VCs
    // (preservation/progress) summarise it via {@link #summarizeInnerLoop} — havoc its written vars,
    // assume `inner_inv ∧ ¬inner_guard`. Here we discharge the inner loop's *own* obligations, which is
    // what makes that summary sound:
    //   • establish — `outer_inv ∧ outer_guard ∧ ⟦outer-body stmts before the inner loop⟧ ⇒ inner_inv`
    //   • preserve  — `inner_inv ∧ inner_guard ⇒ inner_inv'` (self-contained — NOT under outer_inv, which
    //                  is generally false mid-inner-loop, e.g. `count == i*n` while count is changing)
    //   • progress  — the inner @Decreases strictly decreases and stays ≥ 0
    // Preserve/progress reuse the standard checks verbatim against an inner {@link LoopSite}.
    private void verifyNestedLoops(MethodNode node, LoopSite site, Expression reqAst, Expression postAst) {
        List<Statement> inners = annotatedInnerLoops(site.spec.body)
        if (inners.isEmpty()) return
        if (inners.size() > 1) {
            throw new UnsupportedConstructException(
                "more than one nested loop in the loop body — not yet supported")
        }
        Statement innerLoop = inners.get(0)
        LoopSpec innerSpec = (LoopSpec) innerLoop.getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY)
        // ≤ 2 levels for this slice: the inner body must not itself contain a loop we'd have to summarise.
        if (!annotatedInnerLoops(innerSpec.body).isEmpty()) {
            throw new UnsupportedConstructException("loops nested 3+ deep — not yet supported")
        }
        LoopSite innerSite = new LoopSite()
        innerSite.loopStmt = innerLoop
        innerSite.spec = innerSpec
        innerSite.prefix = Collections.<Statement> emptyList()
        innerSite.suffix = Collections.<Statement> emptyList()
        innerSite.originalPrefix = Collections.<Statement> emptyList()
        innerSite.originalSuffix = Collections.<Statement> emptyList()
        List<Statement> before = stmtsBefore(site.spec.body, innerLoop)
        checkNestedEstablishment(node, site, innerSite, before, reqAst)
        List<Expression> innerStable = loopStableRequires(reqAst, innerSite)
        checkPreservation(node, innerSite, innerStable)
        if (innerSpec.variant != null) checkProgress(node, innerSite, innerStable)
        // Phase 109 — an inner loop may carry its own early `return` (an in-inner-body exit). Collect those
        // exits and discharge each one's @Ensures with the inner loop's body-entry context (inner_inv ∧
        // inner_guard) — the regular Phase-49b in-body treatment, applied to the inner site. Sound because
        // inner_inv is established + preserved above, so it holds whenever the inner exit fires; the outer
        // summary already covers the no-return fall-through. Without this, an inner return would slip its
        // postcondition unchecked.
        if (postAst != null) {
            partitionEarlyExits(innerSpec.body, 'inBody', innerSite.earlyExits)
            for (EarlyExit ex : innerSite.earlyExits) checkEarlyExit(node, innerSite, ex, reqAst, postAst)
        }
    }

    /** Top-level statements of {@code body} that are loops carrying a captured {@link LoopSpec}. */
    private static List<Statement> annotatedInnerLoops(List<Statement> body) {
        List<Statement> out = new ArrayList<Statement>()
        if (body != null) for (Statement st : body) {
            if (st instanceof LoopingStatement &&
                ((Statement) st).getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY) != null) {
                out.add(st)
            }
        }
        out
    }

    /** The statements of {@code body} that precede {@code target} (by identity). */
    private static List<Statement> stmtsBefore(List<Statement> body, Statement target) {
        List<Statement> out = new ArrayList<Statement>()
        for (Statement st : body) { if (st.is(target)) break; out.add(st) }
        out
    }

    /** Inner establishment: `precondition ∧ class invariants ∧ outer_inv ∧ outer_guard ∧ ⟦before⟧ ⇒ inner_inv`,
     *  where {@code before} are the outer-body statements that run before the inner loop is reached. */
    private void checkNestedEstablishment(MethodNode node, LoopSite outer, LoopSite innerSite,
                                          List<Statement> before, Expression reqAst) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            if (reqAst != null) s.assertExpr(LoopEncoder.tr(enc, reqAst, "precondition"))
            assumeIntJvmBounds(s, enc)
            assumeClassInvariants(s, enc)
            s.assertExpr(LoopEncoder.conj(enc, s, outer.spec.invariants))
            s.assertExpr(LoopEncoder.tr(enc, outer.spec.guard, "guard"))
            LoopEncoder.symExec(before, enc, s)
            s.assertExpr(s.not(LoopEncoder.conj(enc, s, innerSite.spec.invariants)))
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(
                    Reporter.formatLoopEstablishment(node.name, invText(innerSite), r, false), innerSite.loopStmt)
            }
        } finally { try { s.close() } catch (Throwable ignored) {} }
    }

    /**
     * Phase 49b — walk the loop body's top-level statements, sym-executing each non-exit
     * via {@link LoopEncoder#symExec} and asserting {@code ¬guard} for each in-body
     * early-exit if-statement (we're on the "no exit fired" path here). The interleaving
     * keeps the guard's variable bindings consistent with whatever prior body statements
     * have done.
     */
    private void symExecBodyWithExits(LoopSite site, Encoder enc, SmtSession s) {
        for (Statement st : site.spec.body) {
            Expression retExpr = earlyExitReturnFor(st)
            if (retExpr != null) {
                IfStatement ifs = (IfStatement) st
                Object g = enc.translate(ifs.booleanExpression)
                if (g != null) s.assertExpr(s.not(g))
            } else {
                // A nested annotated loop is summarised by LoopEncoder.symExec (Phase 91 —
                // `summarizeInner`); an un-annotated one throws there → the whole loop skips loudly.
                LoopEncoder.symExec([st] as List<Statement>, enc, s)
            }
        }
    }

    /** Use: precondition ∧ class invariants ∧ invariant ∧ ¬guard ∧ suffix ⇒ postcondition. */
    private void checkUse(MethodNode node, LoopSite site, Expression reqAst, Expression postAst) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            if (reqAst != null) s.assertExpr(LoopEncoder.tr(enc, reqAst, "precondition"))
            assumeIntJvmBounds(s, enc)
            assumeClassInvariants(s, enc)
            // Phase 49 — assume no early-exit fired in either region (we reached the natural
            // return-after-loop path). Each early-exit's @Ensures is verified independently in
            // {@link #checkEarlyExit}.
            for (EarlyExit ex : site.earlyExits) {
                Object gh = enc.translate(ex.guard)
                if (gh != null) s.assertExpr(s.not(gh))
            }
            s.assertExpr(LoopEncoder.conj(enc, s, site.spec.invariants))
            s.assertExpr(s.not(LoopEncoder.tr(enc, site.spec.guard, "guard")))
            Expression resultExpr = LoopEncoder.resultExpr(site.suffix, enc, s)
            // Phase 78 — a list-literal return (e.g. `return [s, p]`) binds result's contents as a factory,
            // so result.size()/result[k] fold; otherwise the scalar-handle binding + size/array alias.
            if (resultExpr == null || (!enc.tryRecordFactoryAssign('result', resultExpr) &&
                                       !enc.tryRecordSetBinopAssign('result', resultExpr))) {
                enc.bind('result', LoopEncoder.tr(enc, resultExpr, "return expression"))
                // Phase 45b — alias result's size/array oracles to the returned list local so
                // {@code result.size()} in the postcondition resolves to the local's threaded state.
                aliasResultToReturnedListLocal(s, enc, resultExpr)
            }
            s.assertExpr(s.not(LoopEncoder.tr(enc, postAst, "postcondition")))
            CheckResult r = s.check()
            if (r.status == CheckResult.Status.REFUTED) appendOffendingElements(r, enc, s, [postAst])
            r = shown(r)
            if (r.status != CheckResult.Status.VERIFIED) {
                ASTNode anchor = (resultExpr != null && resultExpr.lineNumber > 0) ?
                    (ASTNode) resultExpr : (ASTNode) site.loopStmt
                addStaticTypeError(
                    withRepro(Reporter.formatPostconditionFailure(node.name, postAst.text, r), r, 'AssertionError'), anchor)
            }
        } finally { try { s.close() } catch (Throwable ignored) {} }
    }

    private static String invText(LoopSite site) {
        // Phase 63 — the for-in desugar's auto-injected index-bounds clause is internal; show only the
        // user-written invariant clauses so the diagnostic reads in source terms (the loop variable),
        // not the synthetic index.
        site.spec.invariants.collect { it.text }
            .findAll { !it.contains(ContractExpansionTransform.FOR_IN_INDEX) }
            .join(' && ')
    }

    @Override
    void onMethodSelection(Expression expression, MethodNode target) {
        // Phase 142b — a carrier operator (`a + b`) resolves to a method (`a.plus(b)`); rewrite it to that call
        // shape so its precondition is checked here, exactly as for an explicit call. (The value-flow assumes the
        // @Ensures separately.) Only when the left operand is carrier-typed, so a normal `int + int` is untouched.
        if (expression instanceof BinaryExpression && target != null &&
            carrierOperatorMethod(((BinaryExpression) expression).operation.text) == target.name &&
            carrierTypeOfExpr(((BinaryExpression) expression).leftExpression) != null) {
            BinaryExpression be = (BinaryExpression) expression
            MethodCallExpression call = new MethodCallExpression(
                be.leftExpression, target.name, new ArgumentListExpression(be.rightExpression))
            call.setImplicitThis(false)
            call.setSourcePosition(be)
            expression = call
        }
        // We only care about resolvable, method-call-shaped expressions.
        if (!(expression instanceof MethodCall)) return
        if (target == null) return

        // Find @Requires on the callee. Walk superclasses too — a child
        // can inherit a contract via overriding.
        AnnotationNode req = findRequires(target)
        if (req == null) {
            // Phase 215 — the external-spec registry: STC hands us the RESOLVED target (the real
            // java.lang.Math#abs), so a registered skeleton's @Requires becomes the call-site
            // obligation exactly as an in-code contract would.
            MethodNode spec = SpecRegistry.lookup(target.declaringClass?.name, target.name,
                target.parameters.length, target.parameters.collect { it.type.name })
            if (spec != null && contractAstFor(spec, 'requires') != null) {
                target = spec
            }
        }
        if (req == null && !(contractAstFor(target, 'requires') != null)) return

        Expression contractAst = contractAstFor(target, 'requires')
        if (contractAst == null) {
            addStaticTypeError(
                Reporter.formatSkipped(target.name,
                    "contract source was not captured by ContractExpansionTransform " +
                    "(producer may not have been recompiled with :verification on its classpath)"),
                expression as ASTNode)
            return
        }

        List<Expression> argExprs = collectArgumentExpressions((MethodCall) expression)
        if (argExprs == null) {
            addStaticTypeError(
                Reporter.formatSkipped(target.name,
                    "could not extract argument expressions at call site"),
                expression as ASTNode)
            return
        }

        Parameter[] formals = target.parameters
        if (formals.length != argExprs.size()) {
            // Varargs and default params: out of scope for the spike.
            addStaticTypeError(
                Reporter.formatSkipped(target.name,
                    "formal/actual arity mismatch (varargs not supported yet)"),
                expression as ASTNode)
            return
        }

        verifyCallSite(target, formals, argExprs, contractAst, expression)
    }

    /**
     * The innermost annotated loop ({@code LOOP_SPEC_KEY} present) whose body lexically contains {@code callExpr},
     * or null if the call isn't inside one. Lets {@link #verifyCallSite} discharge an in-loop call's precondition
     * against an *arbitrary* iteration — under the loop invariant + guard, the loop variables symbolic — instead of
     * the loop-entry / havoc'd state the straight-line prefix replay leaves them in. Matches the call by identity.
     */
    private LoopingStatement enclosingAnnotatedLoop(Expression callExpr) {
        if (currentMethod == null) return null
        Statement body = (Statement) currentMethod.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (body == null) body = currentMethod.code
        if (body == null) return null
        final LoopingStatement[] found = new LoopingStatement[1]
        final List<LoopingStatement> stack = new ArrayList<LoopingStatement>()
        body.visit(new CodeVisitorSupport() {
            private boolean annotated(LoopingStatement ls) {
                ((Statement) ls).getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY) != null
            }
            private void record(Expression call) {
                if (found[0] == null && call.is(callExpr) && !stack.isEmpty()) found[0] = stack.get(stack.size() - 1)
            }
            @Override void visitWhileLoop(WhileStatement loop) {
                boolean a = annotated(loop); if (a) stack.add(loop)
                super.visitWhileLoop(loop)
                if (a) stack.remove(stack.size() - 1)
            }
            @Override void visitForLoop(ForStatement loop) {
                boolean a = annotated(loop); if (a) stack.add(loop)
                super.visitForLoop(loop)
                if (a) stack.remove(stack.size() - 1)
            }
            @Override void visitDoWhileLoop(DoWhileStatement loop) {
                boolean a = annotated(loop); if (a) stack.add(loop)
                super.visitDoWhileLoop(loop)
                if (a) stack.remove(stack.size() - 1)
            }
            @Override void visitMethodCallExpression(MethodCallExpression call) {
                record(call); super.visitMethodCallExpression(call)
            }
            @Override void visitStaticMethodCallExpression(StaticMethodCallExpression call) {
                record(call); super.visitStaticMethodCallExpression(call)
            }
        })
        found[0]
    }

    private void verifyCallSite(MethodNode target,
                                Parameter[] formals,
                                List<Expression> argExprs,
                                Expression contractAst,
                                Expression callExpr) {

        SmtSession session = backend.session()
        try {
            Encoder enc = mkEncoder(session)
            // Phase 44c bounds apply at call sites too: without them the solver picks caller-parameter
            // values outside the JVM int range (a = MIN_VALUE - 1) that the runtime cannot exhibit —
            // surfaced by the external-spec registry's `a > Integer.MIN_VALUE` obligation (Phase 215).
            assumeIntJvmBounds(session, enc)

            Map<String, Object> formalBindings = [:]
            // Reference-typed formals bound to a named actual: candidates for
            // tying the size/nullity oracles across the boundary (see below).
            Map<String, String> oracleActuals = [:]
            // Reference-typed formals bound to a NON-variable actual with statically-known nullity (e.g.
            // `new X(…)` is non-null, a `null` literal is null): carry that onto the formal's nullity oracle so a
            // `@Requires({ o != null })` discharges even though there's no actual *name* to tie to (Phase 133).
            Map<String, Object> formalKnownNullity = [:]

            // The context (1b–2c) is built FIRST, against the caller's entry state, then the prefix is
            // replayed to the call site; only THEN are the actual arguments translated (step 1, below),
            // so an argument like `a[m]` reads the post-mutation array. This ordering — plus fresh callee
            // formals — is what makes a precondition over mutated state (or a recursive self-call) sound.

            // 1b. Assume the *enclosing* method's own @Requires, if any. A
            //     precondition is a given throughout the method body, so it may
            //     be used to discharge a call the body makes — exactly as the
            //     implicit-obligation checks already do (see assumeContext).
            //     The enclosing parameter names coincide with the actual-
            //     argument names in scope here, so the same SMT symbols (and
            //     their size/nullity oracles) are shared automatically.
            if (currentMethod != null && findRequires(currentMethod) != null) {
                Expression enclosingReq = contractAstFor(currentMethod, 'requires')
                if (enclosingReq != null) {
                    Object pre = enc.translate(enclosingReq)
                    if (pre != null) session.assertExpr(pre)
                }
            }

            // 2. Harvest path facts and assert them. Each fact is one
            //    enclosing if's condition (negated if we're in the
            //    else branch).
            List<IfFact> facts = currentFacts != null ?
                currentFacts.factsAt(callExpr as ASTNode) :
                Collections.<IfFact>emptyList()
            for (IfFact f : facts) {
                Object condExpr = enc.translate(f.condition)
                if (condExpr == null) {
                    // A fact we can't encode just becomes an unknown
                    // — drop it. Safe (it weakens our assumption set),
                    // and the spike stays honest.
                    continue
                }
                session.assertExpr(f.inThenBranch ? condExpr : session.not(condExpr))
            }

            // 2c. Early-return path narrowing: an `if (cond) return/throw` that *precedes* this call on its
            //     path means `cond` was false when we got here. Such a guard is not an *enclosing* `if`, so
            //     PathFacts misses it — yet it is a definite fact (e.g. `sumUp(n-1)` after `if (n==0) return 0`
            //     needs ¬(n==0) to show `n-1 >= 0`). Without it, fresh formals would leave these recursive
            //     preconditions unprovable (they pass vacuously today only via the name-conflation above).
            // 2e. The call lies inside an annotated loop body. Discharge its precondition against an ARBITRARY
            //     iteration, not the loop-entry state: seed the loop invariant + guard (the loop variables stay
            //     symbolic, constrained only by the invariant — not pinned to their pre-loop init values the way the
            //     straight-line prefix replay would leave them), then thread the IN-LOOP preceding statements to the
            //     call. This is the same context the loop's implicit obligations use (dischargeSeeded); without it,
            //     an in-loop call's precondition was checked with the loop variables havoc'd (so a `swap(lo, mid)`
            //     inside the loop saw `mid = -1` and spuriously refuted). The in-loop prefix is taken from the CLEAN
            //     loop body (`spec.body`, captured pre-instrumentation): the live body carries groovy-contracts'
            //     try/catch wrappers that symExec can't model, and the clean nodes aren't the live `callExpr` so they
            //     are located by source position (preserved through instrumentation), not identity. Only when the
            //     call is actually located do we seed the loop context; otherwise fall through to the straight-line
            //     path (no worse than before), so we never assume the invariant without the matching body replay.
            boolean handledInLoop = false
            LoopingStatement encLoop = (currentMethod != null && callExpr.lineNumber > 0) ?
                enclosingAnnotatedLoop(callExpr) : null
            if (encLoop != null) {
                LoopSpec spec = (LoopSpec) ((Statement) encLoop).getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY)
                if (spec != null) {
                    List<Statement> inLoopPrefix = new ArrayList<Statement>()
                    if (collectPrefix(new BlockStatement(spec.body, null),
                            callExpr.lineNumber, callExpr.columnNumber, inLoopPrefix)) {
                        for (Expression inv : spec.invariants) {
                            Object h = enc.translate(inv)
                            if (h != null) session.assertExpr(h)
                        }
                        if (spec.guard != null) {
                            Object g = enc.translate(spec.guard)
                            if (g != null) session.assertExpr(g)
                        }
                        try {
                            LoopEncoder.symExec(inLoopPrefix, enc, session)
                        } catch (Throwable ignored) {
                        }
                        handledInLoop = true
                    }
                }
            }
            if (!handledInLoop && currentMethod != null && callExpr.lineNumber > 0) {
                Statement encBody = (Statement) currentMethod.getNodeMetaData(
                    ContractExpansionTransform.ORIGINAL_BODY_KEY)
                if (encBody == null) encBody = currentMethod.code
                if (encBody != null) {
                    for (Expression g : earlyReturnGuards(encBody, callExpr.lineNumber, callExpr.columnNumber)) {
                        Object c = enc.translate(g)
                        if (c != null) session.assertExpr(session.not(c))
                    }
                    // 2d. Thread the intervening straight-line body mutations to the call site, so both the
                    //     precondition and the actual arguments (step 1, next) see the state *at the call*.
                    try {
                        replayPrefix(prefixStatements(encBody, callExpr.lineNumber, callExpr.columnNumber), enc, session)
                    } catch (Throwable ignored) {
                    }
                }
            }

            // 1. Translate each actual-argument expression — now against the post-replay state — and pin a
            //    FRESH formal to it. The formal must be distinct from any caller variable of the same name:
            //    on a recursive self-call (`visit(next[u])`) the callee formal `u` and the caller `u` would
            //    otherwise be the same constant, asserting the garbled `u == next[u]` (or `n == n-1` for
            //    `sumUp(n-1)`) and checking the precondition in a corrupt/vacuous context. The `#arg` keeps
            //    the fresh symbol out of the displayed counterexample (which filters `#`).
            for (int i = 0; i < formals.length; i++) {
                Object argHandle = enc.translate(argExprs[i])
                // Phase 145 — a carrier-typed argument that is itself a call (`plus(Quantity.mile(1))` in a chain):
                // model it as a value, so the guarded operator's precondition discharges over the real argument.
                if (argHandle == null && Encoder.isCarrier(formals[i].type)) {
                    argHandle = carrierValueOf(session, enc, argExprs[i], currentMethod)
                }
                if (argHandle == null) {
                    addStaticTypeError(
                        Reporter.formatSkipped(target.name,
                            "actual argument '${argExprs[i].text}' is outside fragment"),
                        callExpr as ASTNode)
                    return
                }
                // Phase 27 — pick the formal's sort from its declared type so a String/Enum actual
                // (translated to the right sort via scalarTypes routing) can be equated without a
                // sort mismatch. Int sort keeps the existing intVar storage (so it still shows up
                // in counterexample model walks).
                String formalName = formals[i].name + '#arg' + (havocCounter++)
                Object formalSort = enc.sortForType(formals[i].type)
                Object formalVar = (formalSort == session.intSort()) ?
                    session.intVar(formalName) :
                    session.varOfSort(formalName, formalSort)
                session.assertExpr(session.eq(formalVar, argHandle))
                formalBindings[formals[i].name] = formalVar
                if (argExprs[i] instanceof VariableExpression &&
                    !ClassHelper.isPrimitiveType(formals[i].type)) {
                    oracleActuals[formals[i].name] = ((VariableExpression) argExprs[i]).name
                } else if (!ClassHelper.isPrimitiveType(formals[i].type)) {
                    Object kn = enc.nullityOfExpr(argExprs[i])      // e.g. `new X(…)` → known non-null
                    if (kn != null) formalKnownNullity[formals[i].name] = kn
                }
                // Phase 185 — a Function-typed formal has no scalar handle to equate: its identity is the
                // uninterpreted `apply$<name>` symbol. Alias the formal to the named actual so the callee's
                // quantified @Requires over `g` translates onto the CALLER's `apply$csAF` facts (lemma reuse
                // without name-aligning the formals).
                if ((formals[i].type?.name == 'java.util.function.Function' ||
                        formals[i].type?.name == 'java.util.function.BiFunction') &&
                        argExprs[i] instanceof VariableExpression) {
                    enc.aliasFunction(formals[i].name, ((VariableExpression) argExprs[i]).name)
                }
            }

            // 3. Translate the contract and assert its NEGATION. We're
            //    asking: is there a model where the path is satisfiable
            //    AND the precondition fails? If yes, that model is the
            //    counterexample we report.
            formalBindings.each { name, handle -> enc.bind(name, handle) }
            // Phase 45 — cross-class precondition discharge. If the call is {@code b.method(...)}
            // for a class-typed parameter {@code b}, translate the callee's @Requires under the
            // receiver context so {@code count} in the contract resolves to {@code b$count}.
            String crossClassRecv = null
            Set<String> crossClassFields = Collections.<String>emptySet()
            if (callExpr instanceof MethodCallExpression) {
                Expression recvExpr = ((MethodCallExpression) callExpr).objectExpression
                if (recvExpr instanceof VariableExpression) {
                    String rn = ((VariableExpression) recvExpr).name
                    if (currentObjectParams.containsKey(rn)) {
                        crossClassRecv = rn
                        ClassNode rt = currentObjectParams.get(rn)
                        Set<String> fs = new LinkedHashSet<String>()
                        List<FieldNode> rfs = rt.fields
                        if (rfs != null) for (FieldNode f : rfs) fs.add(f.name)
                        crossClassFields = fs
                    }
                }
            }
            // Phase 142b — a CARRIER receiver (`a.plus(b)` from an operator, or an explicit instance call on a
            // record): bind `this` and each component field so the callee's bare `field` / `this.field`
            // precondition resolves to the receiver's value, and register the carrier types of `this` / the
            // formals so an `o.field` read resolves. (Distinct from the object-param `crossClassRecv` path above.)
            Map<String, ClassNode> typeReg = new LinkedHashMap<String, ClassNode>()
            if (crossClassRecv == null && callExpr instanceof MethodCallExpression) {
                Expression recvExpr = ((MethodCallExpression) callExpr).objectExpression
                ClassNode rct = recvExpr != null ? carrierTypeOfExpr(recvExpr) : null
                // Phase 145 — the receiver may itself be a carrier-returning call (`a.f().g()`).
                if (rct == null && recvExpr != null && !(recvExpr instanceof ClassExpression) && isCallExpr(recvExpr)) {
                    rct = carrierValueExprType(recvExpr)
                }
                if (rct != null) {
                    Object recvH = carrierValueOf(session, enc, recvExpr, currentMethod)
                    if (recvH != null) {
                        enc.bind('this', recvH)
                        typeReg.put('this', rct)
                        for (FieldNode f : instanceFields(rct)) {
                            Object fv = enc.carrierField(rct, f.name, recvH)
                            if (fv != null) enc.bind(f.name, fv)
                        }
                    }
                }
            }
            for (Parameter fp : formals) if (Encoder.isCarrier(fp.type)) typeReg.put(fp.name, fp.type)
            Map<String, ClassNode> savedTypes = enc.pushScalarTypes(typeReg)
            Object contractSmt
            try {
                contractSmt = crossClassRecv != null ?
                    enc.translateUnderReceiver(contractAst, crossClassRecv, crossClassFields) :
                    enc.translate(contractAst)
            } finally {
                enc.popScalarTypes(savedTypes)
            }
            if (contractSmt == null) {
                addStaticTypeError(
                    Reporter.formatSkipped(target.name,
                        "precondition contract is outside fragment"),
                    callExpr as ASTNode)
                return
            }
            // 3b. Tie the formal's size/nullity oracle to the actual's — but
            //     only for oracles the contract (or assumed context) actually
            //     minted on the formal. This carries a caller's knowledge
            //     (`xs.size() > 0`, `x != null`) across the boundary while
            //     keeping unused oracles out of the counterexample.
            oracleActuals.each { String formalName, String actualName ->
                if (enc.hasSizeOracle(formalName)) {
                    session.assertExpr(session.eq(
                        enc.sizeOf(formalName), enc.sizeOf(actualName)))
                }
                if (enc.hasNullityOracle(formalName)) {
                    session.assertExpr(session.eq(
                        enc.nullityOf(formalName), enc.nullityOf(actualName)))
                }
                // Phase 225 — tie the ELEMENT CONTENTS too: a contract quantifying over a list/array
                // formal (`list.indices.every { list[it - 1] <= list[it] }` — Collections#binarySearch's
                // sortedness) reads the formal's element array, which without this stays a fresh
                // unconstrained function and the caller's own sortedness can never discharge it.
                Object formalArr = enc.peekArray(formalName)
                Object actualArr = enc.peekArray(actualName)
                if (formalArr != null && actualArr != null) {
                    session.assertExpr(session.eq(formalArr, actualArr))
                } else if (formalArr == null && actualArr != null) {
                    enc.bindArray(formalName, actualArr)
                }
            }
            formalKnownNullity.each { String formalName, Object knownNull ->
                if (enc.hasNullityOracle(formalName)) {
                    session.assertExpr(session.eq(enc.nullityOf(formalName), knownNull))
                }
            }

            session.assertExpr(session.not(contractSmt))

            // 4. Check.
            CheckResult r = shown(session.check())
            switch (r.status) {
                case CheckResult.Status.VERIFIED:
                    return  // silent success
                case CheckResult.Status.REFUTED:
                    addStaticTypeError(
                        Reporter.formatPreconditionFailure(
                            target.name, contractAst.text, r),
                        callExpr as ASTNode)
                    return
                case CheckResult.Status.UNKNOWN:
                    addStaticTypeError(
                        Reporter.formatPreconditionFailure(
                            target.name, contractAst.text, r),
                        callExpr as ASTNode)
                    return
            }
        } finally {
            try { session.close() } catch (Throwable ignored) {}
        }
    }

    private static boolean isCallExpr(Expression e) {
        e instanceof MethodCallExpression || e instanceof StaticMethodCallExpression
    }

    /** Phase 133 — the Groovy operator-method a binary operator dispatches to (`a + b` is `a.plus(b)`), or null. */
    private static String carrierOperatorMethod(String op) {
        switch (op) {
            case '+': return 'plus'
            case '-': return 'minus'
            case '*': return 'multiply'
            case '/': return 'div'
            default:  return null
        }
    }

    /** The carrier (record/wrapper) ClassNode of {@code e}'s static type, or null. */
    private static ClassNode carrierTypeOfExpr(Expression e) {
        if (e == null) return null
        if (e instanceof ConstructorCallExpression) {
            ClassNode ct = ((ConstructorCallExpression) e).type
            if (ct != null && Encoder.isCarrier(ct)) return ct
        }
        ClassNode t = null
        try { t = e.getType() } catch (ignored) {}
        (t != null && Encoder.isCarrier(t)) ? t : null
    }

    /** Phase 145 — the carrier type an expression *evaluates to*: a carrier variable/constructor (via
     *  {@link #carrierTypeOfExpr}), or a contracted call returning a carrier (resolved on its instance-receiver
     *  or static-owner type, recursing through a chained call receiver so {@code a.f().g()} resolves). Null if not
     *  a carrier value. Threads {@link #currentMethod} as the caller for callee resolution. */
    private ClassNode carrierValueExprType(Expression e) {
        if (e == null) return null
        ClassNode direct = carrierTypeOfExpr(e)
        if (direct != null) return direct
        if (!isCallExpr(e)) return null
        ClassNode forResolve = receiverCarrierType(e) ?: ownerCarrierType(e)
        if (forResolve == null && e instanceof MethodCallExpression &&
            !(((MethodCallExpression) e).objectExpression instanceof ClassExpression)) {
            forResolve = carrierValueExprType(((MethodCallExpression) e).objectExpression)   // chained receiver
        }
        if (forResolve == null) return null
        MethodNode callee = resolveContractedCallee(currentMethod, ((MethodCall) e).methodAsString,
            collectArgumentExpressions((MethodCall) e).size(), true, forResolve)
        (callee != null && Encoder.isCarrier(callee.returnType)) ? callee.returnType : null
    }

    /** Phase 145 — evaluate a carrier-valued expression to an SMT handle, modelling a nested contracted call (a
     *  factory or instance call sitting as the receiver / argument of an outer call, or as a return value) by
     *  minting a fresh carrier-sorted handle constrained by the callee's {@code @Ensures}. This is what makes a
     *  *chain* — {@code Quantity.km(1).plus(Quantity.mile(1))} — resolve as a single expression: a carrier-returning
     *  call is a value, not only a local-assignment RHS. Additive — a directly-translatable expression keeps its
     *  existing handle; returns null (→ caller skips loudly) when the call isn't a modellable contracted carrier call. */
    private Object carrierValueOf(SmtSession s, Encoder enc, Expression e, MethodNode caller) {
        Object direct = enc.translate(e)
        if (direct != null) return direct
        ClassNode rt = carrierValueExprType(e)
        if (rt == null) return null
        Object fresh = s.varOfSort('chain#' + (havocCounter++), enc.sortForType(rt))
        assumeCalleeEnsures(s, enc, e, caller, fresh, hasDecreases(caller)) ? fresh : null
    }

    /** Phase 146 — rewrite each maximal carrier-returning call in {@code e} to a fresh temp local bound to its
     *  modelled value (via {@link #carrierValueOf}), registering the temp's carrier type so a subsequent
     *  {@code .field} read resolves. This is what lets a **read-out in the same expression** translate:
     *  {@code Quantity.km(1).plus(Quantity.mile(1)).value} — the chain call becomes a {@code Quantity} local and
     *  {@code .value} is then an ordinary component read. A non-carrier call (an int/self call) is left untouched
     *  for the existing Int-oriented hoist. Additive — an expression with no carrier call is returned unchanged. */
    private Expression hoistCarrierCalls(Expression e, Encoder enc, SmtSession s, MethodNode node) {
        if (e == null) return e
        boolean[] changed = [false]
        ExpressionTransformer tr = null
        tr = { Expression x ->
            ClassNode ct = isCallExpr(x) ? carrierValueExprType(x) : null
            if (ct != null) {
                // A maximal carrier call: model the WHOLE chain (carrierValueOf recurses into nested calls),
                // so don't descend further into x.
                Object h = carrierValueOf(s, enc, x, node)
                if (h == null) return x
                String nm = 'chain$local$' + (havocCounter++)
                enc.bind(nm, h)
                enc.registerScalarType(nm, ct)
                changed[0] = true
                return new VariableExpression(nm)
            }
            x.transformExpression(tr)
        } as ExpressionTransformer
        Expression out = tr.transform(e)
        // Identity-preserving when nothing was hoisted — transformExpression rebuilds the tree even when
        // unchanged, and handing a reconstructed copy to the encoder would perturb the SMT (and any
        // counterexample model) for *every* method, carrier or not. Return the original unless we rewrote a call.
        changed[0] ? out : e
    }

    /**
     * Phase 133 — rewrite a carrier-operand arithmetic operator to its method-call form (`a + b` → `a.plus(b)`),
     * so the value-flow's interprocedural path discharges it via the operator method's contract — but ONLY when
     * Phase 142b — a guarded operator IS routed now: {@code onMethodSelection} fires for the operator and checks
     * the callee's {@code @Requires} at the site (rewriting it to the same call shape), so assuming the
     * {@code @Ensures} here is sound. Any non-carrier or non-arithmetic expression is returned unchanged.
     */
    private static Expression carrierOperatorCall(Expression e, MethodNode caller) {
        if (!(e instanceof BinaryExpression)) return e
        BinaryExpression be = (BinaryExpression) e
        String m = carrierOperatorMethod(be.operation.text)
        ClassNode rt = (m == null) ? null : carrierTypeOfExpr(be.leftExpression)
        if (rt == null) return e
        MethodNode callee = resolveContractedCallee(caller, m, 1, true, rt)
        if (callee == null) return e
        MethodCallExpression call = new MethodCallExpression(
            be.leftExpression, m, new ArgumentListExpression(be.rightExpression))
        call.setImplicitThis(false)
        call.setSourcePosition(be)
        call
    }

    /** True if the method carries a method-level {@code @Decreases} termination measure. */
    private boolean hasDecreases(MethodNode node) {
        contractAstFor(node, 'decreases') != null
    }

    /** True if {@code expr} is a (direct, same-class) recursive call to {@code node} — by name + arity. */
    private static boolean isSelfCall(Expression expr, MethodNode node) {
        if (!(expr instanceof MethodCall)) return false
        String name = ((MethodCall) expr).methodAsString
        if (name == null || name != node.name) return false
        List<Expression> args = collectArgumentExpressions((MethodCall) expr)
        return args != null && args.size() == node.parameters.length
    }

    /**
     * Phase 7 (induction) — discharge the recursion termination obligation for a method carrying a
     * {@code @Decreases} measure: at every recursive call, prove {@code 0 <= measure[args] <
     * measure[entry]} under the path facts. This is the well-foundedness that justifies assuming the
     * method's own {@code @Ensures} as the inductive hypothesis at the recursive call (see
     * {@code checkPath}); the runtime twin is groovy-contracts' method-level {@code @Decreases} check.
     */
    private void verifyTermination(MethodNode node) {
        Expression measureAst = contractAstFor(node, 'decreases')
        if (measureAst == null) return
        Expression reqAst = findRequires(node) != null ? contractAstFor(node, 'requires') : null
        Statement body = (Statement) node.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (body == null) body = node.code
        if (body == null) return
        List<Path> paths
        try {
            paths = BodyEncoder.enumeratePaths(body, node.isVoidMethod())
        } catch (UnsupportedConstructException ignored) {
            return   // body outside the path fragment → checkPath skipped the IH too; stay consistent
        }
        for (Path p : paths) {
            for (int i = 0; i < p.steps.size(); i++) {
                Object step = p.steps.get(i)
                Expression call = (step instanceof Assign) ? ((Assign) step).rhs :
                                  (step instanceof LemmaCall) ? ((LemmaCall) step).call : null
                if (call != null && isSelfCall(call, node)) {
                    dischargeTermination(node, p.steps.subList(0, i), call, measureAst, reqAst)
                }
            }
        }
    }

    /** Prove the measure strictly decreases (and stays >= 0) at one recursive call on a path. */
    private void dischargeTermination(MethodNode node, List<Object> preceding, Expression callExpr,
                                      Expression measureAst, Expression reqAst) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            if (reqAst != null) {
                Object pre = enc.translateBool(reqAst)
                if (pre != null) { s.assertExpr(pre); captureExplain(s, enc, reqAst, pre) }
            }
            // Measure on entry — translated BEFORE the body effects below are replayed, so a measure over
            // *mutated* state (a set's cardinality, `n - s.size()`) reads the entry value, not the
            // post-body one. For the usual param-only measure this is identical: the replay never rebinds a
            // parameter, so where `entry` is computed makes no difference.
            Object entry = enc.translate(measureAst)
            // A measure that counts with Sets.boundedCount(_, k) drives the bcount per-add law across the replayed mutations too.
            currentBcountKExprs = bcountKArgs(measureAst)
            // Replay the path facts up to the call (single-assignment, so params keep entry values). A set
            // mutation `s.add(x)` / `s.remove(x)` threads the set and asserts the per-mutation cardinality
            // law, so a set-valued measure strictly decreases across the call exactly when a fresh element
            // was added — the cardinality law wired into recursion termination.
            for (Object step : preceding) {
                if (step instanceof Guard) {
                    Guard g = (Guard) step
                    Object c = enc.translate(g.cond)
                    if (c != null) s.assertExpr(g.positive ? c : s.not(c))
                } else if (step instanceof Assign) {
                    Assign a = (Assign) step
                    Object rhs = enc.translate(a.rhs)
                    if (rhs != null) s.assertExpr(s.eq(enc.varFor(a.name), rhs))
                } else if (step instanceof ArrayStore) {
                    ArrayStore st = (ArrayStore) step
                    // Phase 27 — same sort-routing as in checkPath's main step replay above.
                    boolean isMap = currentMapTypes.containsKey(st.arr)
                    Object idxSort = isMap ? enc.mapKeySort(st.arr) : s.intSort()
                    Object valSort = isMap ? enc.mapValueSort(st.arr) : enc.listElementSort(st.arr)
                    Object idx = enc.translateInSort(st.index, idxSort)
                    Object val = enc.translateInSort(st.value, valSort)
                    if (idx != null && val != null) {
                        if (isMap) doMapPut(s, enc, st.arr, idx, val)
                        else enc.bindArray(st.arr, s.store(enc.arrayFor(st.arr), idx, val))
                    }
                } else if (step instanceof LemmaCall) {
                    Expression lc = ((LemmaCall) step).call
                    if (!applySetMutation(s, enc, lc)) applyMapPut(s, enc, lc)
                }
            }
            List<Expression> actuals = collectArgumentExpressions((MethodCall) callExpr)
            Parameter[] formals = node.parameters
            Map<String, Object> bindings = new LinkedHashMap<String, Object>()
            boolean modelled = actuals != null
            for (int i = 0; modelled && i < formals.length && i < actuals.size(); i++) {
                Object h = enc.translate(actuals.get(i))
                if (h == null) { modelled = false; break }
                bindings.put(formals[i].name, h)
            }
            Object callMeasure = modelled ? enc.translateWith(measureAst, bindings) : null
            if (entry == null || callMeasure == null) {
                // Can't model the measure → don't silently accept the inductive hypothesis.
                addStaticTypeError(Reporter.formatTerminationSkipped(node.name, measureAst.text), callExpr as ASTNode)
                return
            }
            // Obligation: 0 <= measure[args] && measure[args] < measure[entry].
            Object obligation = s.and([s.le(s.intLit(0L), callMeasure), s.lt(callMeasure, entry)])
            s.assertExpr(s.not(obligation))
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(Reporter.formatTerminationFailure(node.name, measureAst.text, r), callExpr as ASTNode)
            }
        } finally {
            currentBcountKExprs = Collections.<Expression> emptyList()
            try { s.close() } catch (Throwable ignored) {}
        }
    }

    /**
     * Resolve a same-class method call by name + arity to a {@link MethodNode}
     * that carries an {@code @Ensures}. Self-calls are excluded — assuming a
     * method's own postcondition at a recursive call is the inductive hypothesis,
     * which needs {@code @Decreases} for well-foundedness and is a later slice.
     */
    private static MethodNode resolveContractedCallee(MethodNode caller, String name, int arity, boolean allowSelf,
                                                      ClassNode receiverType = null, List<String> actualTypeNames = null) {
        if (name == null) return null
        MethodNode m = resolveContractedIn(caller?.declaringClass, caller, name, arity, allowSelf)
        if (m != null) return m
        // Phase 133 — an instance call `recv.m(args)` whose method lives on the *receiver's* (carrier) type rather
        // than the caller's class — e.g. a record's `plus`. Search there too (a different class, so no self-call).
        if (receiverType != null && !receiverType.is(caller?.declaringClass)) {
            m = resolveContractedIn(receiverType, null, name, arity, true)
            if (m != null) return m
            // Phase 215 — the external-spec registry: a trusted skeleton contract for a library class
            // (`Math.abs` from META-INF/groovy-verify/specs/java.lang.Math.groovy). Same consumption as
            // any contracted callee: @Ensures assumed, @Modifies framed.
            // typed when the caller could infer the actuals (disambiguates same-arity overload pairs —
            // abs(int) vs abs(long)); arity-unique otherwise, exactly as before
            MethodNode spec = SpecRegistry.lookup(receiverType.name, name, arity, actualTypeNames)
            // gate on captured contract TEXT: the skeleton parses only to CONVERSION, so its annotation
            // types are unresolved simple names — @ContractSource (attached by CET) is the authority.
            // @ThrowsIf-only specs qualify too (Phase 222): a normal return implies no must-throw
            // condition held — the contrapositive is a consumable fact even with no @Ensures.
            if (spec != null && (contractAstFor(spec, 'ensures') != null || contractAstFor(spec, 'modifies') != null ||
                !SpecRegistry.throwsIfArms(spec).isEmpty())) return spec
        }
        null
    }

    /** Phase 226 — the width-classed simple type name the registry's acceptance rule speaks. */
    private static String specSimple(String n) {
        String s = n != null && n.contains('.') ? n.substring(n.lastIndexOf('.') + 1) : n
        switch (s) {
            case 'Integer': case 'char': case 'Character':
            case 'short': case 'Short': case 'byte': case 'Byte': return 'int'
            case 'Long': return 'long'
            default: return s
        }
    }

    /** Phase 225 — true when the call resolves to a contracted callee (registry or otherwise) whose
     *  declared return type is list-like — the gate for the rename route below. */
    private boolean calleeReturnsList(Expression call, MethodNode caller) {
        if (!(call instanceof MethodCall)) return false
        String name = ((MethodCall) call).methodAsString
        List<Expression> actuals = collectArgumentExpressions((MethodCall) call)
        if (name == null || actuals == null) return false
        ClassNode forResolve = receiverCarrierType(call) ?: ownerCarrierType(call) ?:
            staticOwnerType(call) ?: instanceReceiverType(call)
        MethodNode callee = resolveContractedCallee(caller, name, actuals.size(), true, forResolve)
        if (callee == null) return false
        // a registry skeleton parses only to CONVERSION, so its return type may be the UNRESOLVED
        // simple name ('List') — accept it alongside the resolved forms
        callee.returnType?.name in ['List', 'ArrayList'] || isListType(callee.returnType)
    }

    /** Phase 225 — a list-typed local assigned from a contracted call: mint the local's fresh list
     *  oracles (nullity, size, element array) so the callee's renamed {@code @Ensures} can constrain
     *  them, then assume it. Returns false (caller falls through) when the callee has nothing usable. */
    private boolean listLocalFromCall(SmtSession s, Encoder enc, String name, Expression call, MethodNode caller) {
        Object savedNull = enc.peekNullity(name)
        Object savedSize = enc.peekSize(name)
        Object savedArr = enc.peekArray(name)
        int v = ++havocCounter
        enc.bindNullity(name, s.boolVar(name + '?null#lfc' + v))
        enc.bindSize(name, s.intVar(name + '#size#lfc' + v))
        enc.bindArray(name, s.arrayVar(name + '#arr#lfc' + v))
        if (assumeCalleeEnsures(s, enc, call, caller, null, hasDecreases(caller), name)) return true
        // nothing assumable: restore, so the fresh-handle fallback behaves exactly as before
        if (savedNull != null) enc.bindNullity(name, savedNull)
        if (savedSize != null) enc.bindSize(name, savedSize)
        if (savedArr != null) enc.bindArray(name, savedArr)
        return false
    }

    /** Phase 220 — the STC-inferred type of an instance call's receiver (`d.getMonthValue()`), so the
     *  external-spec registry can answer for instance methods too. Null for static/implicit-this shapes. */
    private ClassNode instanceReceiverType(Expression callExpr) {
        if (!(callExpr instanceof MethodCallExpression)) return null
        MethodCallExpression mce = (MethodCallExpression) callExpr
        if (mce.implicitThis) return null
        Expression obj = mce.objectExpression
        if (obj == null || obj instanceof ClassExpression) return null
        inferredTypeOf(obj)
    }

    /** Phase 220 — a registry spec consumed on an INSTANCE receiver must be receiver-independent:
     *  its contract may reference only {@code result} and the formals (plus capitalised class refs
     *  like {@code Integer.MAX_VALUE}). Receiver-state names ({@code length()}, fields) would
     *  translate as unrelated caller variables — unsound — so such specs are declined here. */
    private static boolean specContractReceiverIndependent(MethodNode spec, Expression contractAst) {
        if (contractAst == null) return true
        Set<String> allowed = new HashSet<String>(spec.parameters.collect { it.name })
        allowed.add('result')
        allowed.add('old')   // Phase 229 — a @Modifies spec's ensures speaks old.<formal>
        boolean[] ok = [true]
        contractAst.visit(new CodeVisitorSupport() {
            @Override void visitVariableExpression(VariableExpression ve) {
                String n = ve.name
                if (!(n in allowed) && !(n && Character.isUpperCase(n.charAt(0)))) ok[0] = false
            }
            @Override void visitMethodCallExpression(MethodCallExpression call) {
                if (call.implicitThis) ok[0] = false   // receiver-state call (`length()`)
                super.visitMethodCallExpression(call)
            }
        })
        ok[0]
    }

    /** Phase 221 — rewrite a receiver-state contract onto the actual receiver: each implicit-this
     *  zero-arg call ({@code length()}) becomes {@code recv.length()}. Returns null (decline) for
     *  shapes that cannot be substituted faithfully: implicit-this calls WITH arguments, or bare
     *  lowercase names that are neither formals nor {@code result} (fields). */
    private static Expression substituteReceiverState(MethodNode spec, Expression contractAst, Expression recv) {
        Set<String> allowed = new HashSet<String>(spec.parameters.collect { it.name })
        allowed.add('result')
        boolean[] bad = [false]
        ExpressionTransformer tx = new ExpressionTransformer() {
            @Override Expression transform(Expression e) {
                if (e == null) return null
                if (e instanceof MethodCallExpression && ((MethodCallExpression) e).implicitThis) {
                    MethodCallExpression m = (MethodCallExpression) e
                    boolean zeroArg = m.arguments instanceof ArgumentListExpression &&
                        ((ArgumentListExpression) m.arguments).expressions.isEmpty()
                    if (!zeroArg) { bad[0] = true; return e }
                    MethodCallExpression sub = new MethodCallExpression(recv, m.methodAsString,
                        ArgumentListExpression.EMPTY_ARGUMENTS)
                    sub.setImplicitThis(false)
                    sub.setSourcePosition(e)
                    return sub
                }
                if (e instanceof VariableExpression) {
                    String n = ((VariableExpression) e).name
                    if (!(n in allowed) && !(n != null && !n.isEmpty() && Character.isUpperCase(n.charAt(0))) &&
                        n != 'this') bad[0] = true
                    return e
                }
                return e.transformExpression(this)
            }
        }
        Expression out = tx.transform(contractAst)
        bad[0] ? null : out
    }

    /**
     * Phase 222 — survival facts: an EXECUTED call the program moved past did not throw, so for every
     * registry-spec'd call subexpression, each @ThrowsIf arm's condition is FALSE (the contrapositive of
     * must-throw — valid for iff and one-directional arms alike). Contract-position mentions of the same
     * methods deliberately do NOT get this (a spec references a value, it doesn't execute a call) — that
     * is why it lives in the body paths, not in the Phase 218 admission axiom.
     */
    private void assertSurvivalFacts(SmtSession s, Encoder enc, Expression e, MethodNode caller) {
        if (e == null) return
        VerifyChecker self = this
        e.visit(new CodeVisitorSupport() {
            @Override void visitMethodCallExpression(MethodCallExpression call) {
                handle(call, call.arguments); super.visitMethodCallExpression(call)
            }
            @Override void visitStaticMethodCallExpression(StaticMethodCallExpression call) {
                handle(call, call.arguments); super.visitStaticMethodCallExpression(call)
            }
            private void handle(Expression call, Expression argsExpr) {
                ClassNode owner = staticOwnerType(call) ?: self.instanceReceiverType(call)
                if (owner == null) return
                List<Expression> actuals = argsExpr instanceof ArgumentListExpression ?
                    ((ArgumentListExpression) argsExpr).expressions : null
                if (actuals == null) return
                List<ClassNode> inferred = actuals.collect { Expression a -> self.inferredTypeOf(a) }
                MethodNode spec = SpecRegistry.lookup(owner.name, ((MethodCall) call).methodAsString,
                    actuals.size(), inferred.every { it != null } ? inferred.collect { it.name } : null)
                if (spec == null) return
                List<Map<String, Object>> arms = SpecRegistry.throwsIfArms(spec)
                if (arms.isEmpty()) return
                Map<String, Object> bindings = new LinkedHashMap<String, Object>()
                for (int i = 0; i < spec.parameters.length; i++) {
                    Object h = enc.translate(actuals.get(i))
                    if (h == null) return
                    bindings.put(spec.parameters[i].name, h)
                }
                for (Map<String, Object> arm : arms) {
                    Expression c = (Expression) arm.get('cond')
                    if (!specContractReceiverIndependent(spec, c)) continue
                    Object ch = enc.translateWith(c, bindings)
                    if (ch != null) {
                        Object neg = s.not(ch)
                        s.assertExpr(neg)
                        if (Reporter.EXPLAIN) {
                            s.explainNoteFact("TRUSTED survival fact ¬(${c.text.replaceAll(/\s+/, ' ')}) — ${owner.name}#${((MethodCall) call).methodAsString} arm".toString(), neg)
                        }
                    }
                }
            }
        })
    }

    /** Phase 215 — the owner type of a plain static call (`Math.abs(x)` / static-import shape), or null. */
    private static ClassNode staticOwnerType(Expression callExpr) {
        if (callExpr instanceof StaticMethodCallExpression) return ((StaticMethodCallExpression) callExpr).ownerType
        if (callExpr instanceof MethodCallExpression) {
            Expression obj = ((MethodCallExpression) callExpr).objectExpression
            if (obj instanceof ClassExpression) return ((ClassExpression) obj).type
        }
        null
    }

    private static MethodNode resolveContractedIn(ClassNode dc, MethodNode caller, String name, int arity, boolean allowSelf) {
        if (dc == null) return null
        for (MethodNode m : dc.getMethods(name)) {
            // A self-call is the inductive hypothesis; only honour it when the caller carries a
            // termination measure (@Decreases) — its well-foundedness is checked separately.
            if (m.is(caller) && !allowSelf) continue
            if (m.parameters.length != arity) continue
            // Usable if it has an @Ensures to assume, or an @Modifies whose effect (a havoc) we model.
            if (findEnsures(m) == null && contractAstFor(m, 'modifies') == null) continue
            return m
        }
        null
    }

    /** Phase 133 — the carrier (record/wrapper) type of an instance call's receiver (`recv.m(…)`), or null. */
    private static ClassNode receiverCarrierType(Expression callExpr) {
        if (!(callExpr instanceof MethodCallExpression)) return null
        Expression recv = ((MethodCallExpression) callExpr).objectExpression
        if (recv == null || ((MethodCallExpression) callExpr).isImplicitThis()) return null
        if (recv instanceof ClassExpression) return null   // `Length.km(…)` is a STATIC call, not an instance receiver
        ClassNode t = (recv instanceof ConstructorCallExpression) ? ((ConstructorCallExpression) recv).type : null
        if (t == null) { try { t = recv.getType() } catch (ignored) {} }
        (t != null && Encoder.isCarrier(t)) ? t : null
    }

    /** Phase 142c — the carrier type a STATIC call's method lives on (`Length.km(…)` → `Length`), for resolution. */
    private static ClassNode ownerCarrierType(Expression callExpr) {
        ClassNode t = null
        if (callExpr instanceof StaticMethodCallExpression) t = ((StaticMethodCallExpression) callExpr).ownerType
        else if (callExpr instanceof MethodCallExpression) {
            Expression recv = ((MethodCallExpression) callExpr).objectExpression
            if (recv instanceof ClassExpression) t = recv.getType()
        }
        (t != null && Encoder.isCarrier(t)) ? t : null
    }

    private static List<FieldNode> instanceFields(ClassNode cn) {
        List<FieldNode> out = new ArrayList<FieldNode>()
        if (cn?.fields != null) for (FieldNode f : cn.fields) if (!f.isStatic()) out.add(f)
        out
    }

    /**
     * Assume the {@code @Ensures} of the method {@code callExpr} resolves to,
     * substituting its formals with the actual-argument handles and {@code result}
     * with {@code resultHandle} (null for a call whose value is unused). Returns
     * true iff a contract was found, fully substitutable, and asserted — so the
     * caller can fall back to "skipped" when it was not.
     */
    /**
     * The {@code @Ensures} we may soundly assume from a statement that ran immediately before
     * {@code callExpr}: the single preceding sibling, when it is a standalone (void) call. Restricting
     * to the *immediately* preceding statement is what keeps it sound — nothing executes between it and
     * the target, so its postcondition still holds (a call further back could be invalidated by an
     * intervening store). Lets `insert(a, n-1)`'s precondition rely on the `sort(a, n-1)` right before
     * it. Matched by source position against the CONVERSION snapshot, so it is robust to the live
     * body's contract instrumentation; returns 0 or 1 expressions.
     */
    private static List<Expression> precedingCallExprs(MethodNode node, Expression callExpr) {
        Statement body = (Statement) node.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (body == null) body = node.code
        if (body == null || callExpr.lineNumber <= 0) return Collections.<Expression> emptyList()
        Expression pc
        try {
            pc = precedingSiblingCall(body, callExpr.lineNumber, callExpr.columnNumber)
        } catch (Throwable ignored) {
            return Collections.<Expression> emptyList()
        }
        pc != null ? Collections.singletonList(pc) : Collections.<Expression> emptyList()
    }

    /** The standalone call in the statement immediately preceding the one that holds the target, or null. */
    private static Expression precedingSiblingCall(Statement st, int tl, int tc) {
        if (st instanceof BlockStatement) {
            List<Statement> ss = ((BlockStatement) st).statements
            for (int i = 0; i < ss.size(); i++) {
                Statement child = ss.get(i)
                if (!spans(child, tl, tc)) continue
                if (child instanceof BlockStatement || child instanceof IfStatement) {
                    return precedingSiblingCall(child, tl, tc)   // recurse; don't use this block's sibling
                }
                // child is the leaf statement directly containing the target call
                return i > 0 ? standaloneCallOf(ss.get(i - 1)) : null
            }
            return null
        }
        if (st instanceof IfStatement) {
            IfStatement ifs = (IfStatement) st
            Expression r = precedingSiblingCall(ifs.ifBlock, tl, tc)
            if (r != null) return r
            return ifs.elseBlock != null ? precedingSiblingCall(ifs.elseBlock, tl, tc) : null
        }
        null
    }

    private static Expression standaloneCallOf(Statement st) {
        if (st instanceof ExpressionStatement) {
            Expression e = ((ExpressionStatement) st).expression
            if (e instanceof MethodCallExpression || e instanceof StaticMethodCallExpression) return e
        }
        null
    }

    private static boolean spans(Statement st, int tl, int tc) {
        cmp(st.lineNumber, st.columnNumber, tl, tc) <= 0 &&
            cmp(tl, tc, st.lastLineNumber, st.lastColumnNumber) <= 0
    }

    /**
     * The conditions of {@code if (cond) <terminating>} statements that are *preceding siblings* of the call
     * at {@code (tl, tc)} — at any enclosing block level. Reaching the call means each such {@code cond} was
     * false, so the caller asserts their negations (the early-return path narrowing PathFacts can't supply,
     * since these are not enclosing ifs). "Terminating" = the then-branch always returns/throws and there is
     * no else.
     */
    private static List<Expression> earlyReturnGuards(Statement body, int tl, int tc) {
        List<Expression> out = new ArrayList<Expression>()
        try { collectEarlyReturns(body, tl, tc, out) } catch (Throwable ignored) {}
        out
    }

    private static boolean collectEarlyReturns(Statement st, int tl, int tc, List<Expression> out) {
        if (st instanceof BlockStatement) {
            for (Statement child : ((BlockStatement) st).statements) {
                if (spans(child, tl, tc)) { collectEarlyReturns(child, tl, tc, out); return true }
                if (child instanceof IfStatement) {
                    IfStatement ifs = (IfStatement) child
                    boolean noElse = ifs.elseBlock == null || ifs.elseBlock instanceof EmptyStatement
                    if (noElse && alwaysExits(ifs.ifBlock)) out.add(ifs.booleanExpression)
                }
            }
            return false
        }
        if (st instanceof IfStatement) {
            IfStatement ifs = (IfStatement) st
            int before = out.size()
            if (ifs.ifBlock != null && collectEarlyReturns(ifs.ifBlock, tl, tc, out)) return true
            while (out.size() > before) out.remove(out.size() - 1)
            if (ifs.elseBlock != null && collectEarlyReturns(ifs.elseBlock, tl, tc, out)) return true
            while (out.size() > before) out.remove(out.size() - 1)
            return false
        }
        return false
    }

    /**
     * True if every path through {@code s} ends by returning or throwing.
     *
     * <p>Also the predicate behind <em>early-exit narrowing</em> in {@link #collectVfObligations} and
     * {@link #dischargeRegion}: reaching the statement after {@code if (x == null) return} means the guard
     * was false, so its negation is a true fact on the continuation. Deliberately conservative — an
     * unrecognised shape answers {@code false}, which costs a fact we could have learned, never soundness.
     */
    private static boolean alwaysExits(Statement s) {
        if (s instanceof ReturnStatement || s instanceof ThrowStatement) return true
        if (s instanceof BlockStatement) {
            List<Statement> ss = ((BlockStatement) s).statements
            return !ss.isEmpty() && alwaysExits(ss.get(ss.size() - 1))
        }
        if (s instanceof IfStatement) {
            IfStatement ifs = (IfStatement) s
            return ifs.elseBlock != null && !(ifs.elseBlock instanceof EmptyStatement) &&
                   alwaysExits(ifs.ifBlock) && alwaysExits(ifs.elseBlock)
        }
        false
    }

    /**
     * The straight-line statements that definitely execute before the call at {@code (tl, tc)} on its path:
     * the siblings before the call's containing statement, at each nesting level down to it. Enclosing
     * {@code if} conditions are excluded (they are the path facts / early-return guards, asserted separately).
     */
    private static List<Statement> prefixStatements(Statement body, int tl, int tc) {
        List<Statement> out = new ArrayList<Statement>()
        try { collectPrefix(body, tl, tc, out) } catch (Throwable ignored) {}
        out
    }

    private static boolean collectPrefix(Statement st, int tl, int tc, List<Statement> out) {
        if (st instanceof BlockStatement) {
            for (Statement child : ((BlockStatement) st).statements) {
                if (spans(child, tl, tc)) { collectPrefix(child, tl, tc, out); return true }
                out.add(child)
            }
            return false
        }
        if (st instanceof IfStatement) {
            IfStatement ifs = (IfStatement) st
            int before = out.size()
            if (ifs.ifBlock != null && collectPrefix(ifs.ifBlock, tl, tc, out)) return true
            while (out.size() > before) out.remove(out.size() - 1)
            if (ifs.elseBlock != null && collectPrefix(ifs.elseBlock, tl, tc, out)) return true
            while (out.size() > before) out.remove(out.size() - 1)
            return false
        }
        return false
    }

    /**
     * Replay the intervening prefix into the encoder so a callee's precondition — and the call's actual
     * arguments — are discharged against the state *at the call*. Straight-line mutations (scalar/field
     * assigns, array stores, map puts, set add/remove) are threaded precisely; a standalone call is left to
     * the preceding-call {@code @Ensures} path; anything else (an {@code if}/loop in the prefix, an
     * unmodelable rhs) soundly *havocs* every location it could write — unknown, never wrongly at entry value.
     */
    private void replayPrefix(List<Statement> prefix, Encoder enc, SmtSession s) {
        for (Statement st : prefix) {
            if (st instanceof ExpressionStatement && replayMutation(((ExpressionStatement) st).expression, enc, s)) {
                continue
            }
            Expression call = standaloneCallOf(st)
            if (call != null) {
                // Phase 237 — a preceding survived non-null asserter narrows everything after it on
                // this replay path (dischargeRegion regions, callee-@Requires prefixes): the call ran
                // and didn't throw, so the target is non-null here.
                Expression nnt = nonNullAssertedTarget(call)
                if (nnt != null) {
                    Object f = enc.translate(nonNullFact(nnt))
                    if (f != null) s.assertExpr(f)
                    continue
                }
                // Assume a preceding standalone call's @Ensures (and frame its @Modifies), in path order.
                // Sound now that intervening mutations are threaded above — so this generalises the old
                // immediate-predecessor-only rule to ANY preceding call, which is what lets a lemma proved
                // before a mutation (e.g. a monotone-bound lemma before the sort's swap) reach a later call.
                assumeCalleeEnsures(s, enc, call, currentMethod, null, hasDecreases(currentMethod))
                continue
            }
            for (String loc : modifiedLocations(st)) havocLocation(enc, loc)
        }
    }

    /** Apply one straight-line mutation expression to the encoder; false if it is not one we model precisely. */
    private boolean replayMutation(Expression e, Encoder enc, SmtSession s) {
        if (e instanceof DeclarationExpression) {
            DeclarationExpression de = (DeclarationExpression) e
            if (de.leftExpression instanceof VariableExpression) {
                String name = ((VariableExpression) de.leftExpression).name
                ClassNode declType = ((VariableExpression) de.leftExpression).originType ?: de.leftExpression.type
                Object rhs = enc.translate(de.rightExpression)
                if (rhs != null) enc.bind(name, rhs)
                else if (!replayCarrierCall(enc, s, name, de.rightExpression, declType)) havocLocation(enc, name)
                Object kn = enc.nullityOfExpr(de.rightExpression)   // Phase 142b — thread known nullity (a `new X(…)` local is non-null)
                if (kn != null) enc.bindNullity(name, kn)
                return true
            }
            // Phase 236 — a multiple-assignment declaration in a replayed prefix. Translate EVERY
            // element against the pre-state first, then bind: that is the parallel semantics, so the
            // shadowed-field `def (a, b) = [b, a]` shape needs no aliasing special-case here. Any
            // element that doesn't translate drops to the generic havoc path below (sound — the
            // components just stay unconstrained fresh handles).
            if (de.leftExpression instanceof TupleExpression) {
                List<Expression> targets = ((TupleExpression) de.leftExpression).expressions
                List<Expression> elems = BodyEncoder.tupleElementExprs(de.rightExpression)
                if (elems != null && elems.size() >= targets.size() &&
                    targets.every { it instanceof VariableExpression }) {
                    List<Object> vals = new ArrayList<Object>()
                    for (int k = 0; k < targets.size(); k++) vals.add(enc.translate(elems.get(k)))
                    if (!vals.contains(null)) {
                        for (int k = 0; k < targets.size(); k++) {
                            String tn = ((VariableExpression) targets.get(k)).name
                            enc.bind(tn, vals.get(k))
                            Object kn2 = enc.nullityOfExpr(elems.get(k))
                            if (kn2 != null) enc.bindNullity(tn, kn2)
                        }
                        return true
                    }
                }
            }
            return false
        }
        if (e instanceof MethodCallExpression) {
            return applySetMutation(s, enc, e) || applyMapPut(s, enc, e)
        }
        if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.ASSIGN) {
            BinaryExpression be = (BinaryExpression) e
            Expression lhs = be.leftExpression
            if (lhs instanceof VariableExpression) {
                String name = ((VariableExpression) lhs).name
                Object rhs = enc.translate(be.rightExpression)
                if (rhs != null) enc.bind(name, rhs)
                else if (!replayCarrierCall(enc, s, name, be.rightExpression, ((VariableExpression) lhs).originType ?: lhs.type)) havocLocation(enc, name)
                return true
            }
            if (lhs instanceof PropertyExpression &&
                ((PropertyExpression) lhs).objectExpression instanceof VariableExpression &&
                ((VariableExpression) ((PropertyExpression) lhs).objectExpression).name == 'this') {
                String name = ((PropertyExpression) lhs).propertyAsString
                Object rhs = enc.translate(be.rightExpression)
                if (rhs != null) enc.bind(name, rhs) else havocLocation(enc, name)
                return true
            }
            if (lhs instanceof BinaryExpression &&
                ((BinaryExpression) lhs).operation.type == Types.LEFT_SQUARE_BRACKET &&
                ((BinaryExpression) lhs).leftExpression instanceof VariableExpression) {
                String name = ((VariableExpression) ((BinaryExpression) lhs).leftExpression).name
                // Phase 27 — same sort-routing as the ArrayStore-step path: map key/val sorts for
                // a map write, Int-index + list element sort for a list/array write.
                boolean isMap = currentMapTypes.containsKey(name)
                Object idxSort = isMap ? enc.mapKeySort(name) : s.intSort()
                Object valSort = isMap ? enc.mapValueSort(name) : enc.listElementSort(name)
                Object idx = enc.translateInSort(((BinaryExpression) lhs).rightExpression, idxSort)
                Object val = enc.translateInSort(be.rightExpression, valSort)
                if (idx == null || val == null) { havocLocation(enc, name); return true }
                if (isMap) doMapPut(s, enc, name, idx, val)
                else enc.bindArray(name, s.store(enc.arrayFor(name), idx, val))
                return true
            }
        }
        return false
    }

    /** Phase 144 — model a carrier-returning contracted call in the prefix replay, so a precondition check's
     *  replayed prefix sees a factory-built local (`Q b = Q.mile(1.0)`) or a routed carrier operator
     *  (`Q s = a + b`) as a real carrier value rather than an {@code Int} havoc. The Int havoc was unsound by
     *  crash: a later same-sort equality (`eq(Q-formal, b)` at a guarded-operator site) mixed {@code Q} with
     *  {@code Int}. Mirrors the main value-flow's carrier-call branch — mint a fresh carrier-sorted handle and
     *  assume the callee's @Ensures (which binds `result` ↦ the handle). Returns false (→ havoc) when the local
     *  is not a carrier or the call isn't a modellable contracted call. */
    private boolean replayCarrierCall(Encoder enc, SmtSession s, String name, Expression rhs, ClassNode declType) {
        if (declType == null || isIntElement(declType)) return false
        Object carrierSort = enc.sortForType(declType)
        if (carrierSort == null || carrierSort == s.intSort()) return false
        Expression rhsE = carrierOperatorCall(rhs, currentMethod)   // `a + b` → `a.plus(b)`; otherwise unchanged
        if (!isCallExpr(rhsE)) return false
        Object fresh = s.varOfSort(name + '#replay' + (havocCounter++), carrierSort)
        if (!assumeCalleeEnsures(s, enc, rhsE, currentMethod, fresh, hasDecreases(currentMethod))) return false
        enc.bind(name, fresh)
        return true
    }

    /** Havoc every representation a name might have (sound when its type is unknown at the havoc site). */
    private void havocLocation(Encoder enc, String name) {
        if (currentSetElementTypes.containsKey(name)) { enc.havocSet(name); return }
        if (currentMapTypes.containsKey(name)) { enc.havocMap(name); return }
        enc.havoc(name); enc.havocArray(name); enc.havocSize(name)
    }

    /** Caller-visible locations a statement may write (assignment LHS, or a set/map mutation receiver). */
    private static Set<String> modifiedLocations(Statement st) {
        Set<String> out = new HashSet<String>()
        try {
            st.visit(new ClassCodeVisitorSupport() {
                protected SourceUnit getSourceUnit() { null }
                @Override
                void visitBinaryExpression(BinaryExpression be) {
                    if (be.operation.type == Types.ASSIGN) {
                        String w = writtenLocation(be.leftExpression)
                        if (w != null) out.add(w)
                    }
                    super.visitBinaryExpression(be)
                }
                @Override
                void visitMethodCallExpression(MethodCallExpression mce) {
                    String m = mce.methodAsString
                    if ((m == 'add' || m == 'remove' || m == 'put') &&
                        mce.objectExpression instanceof VariableExpression) {
                        out.add(((VariableExpression) mce.objectExpression).name)
                    }
                    super.visitMethodCallExpression(mce)
                }
            })
        } catch (Throwable ignored) {
        }
        out
    }


    private static int cmp(int l1, int c1, int l2, int c2) {
        l1 != l2 ? Integer.compare(l1, l2) : Integer.compare(c1, c2)
    }

    /** Phase 113 — a copy of {@code e} with every {@code VariableExpression(from)} renamed to {@code to}
     *  (aliasing a callee's {@code result} to the caller's tuple local). Returns a new tree — the original
     *  contract AST is untouched. Closure bodies aren't descended, but a tuple {@code @Ensures} references
     *  {@code result} at the top level (`result.vN`), so that's sufficient here. */
    private static Expression renameVariable(Expression e, String from, String to) {
        if (e == null) return null
        e.transformExpression(new org.codehaus.groovy.ast.expr.ExpressionTransformer() {
            @Override Expression transform(Expression expr) {
                if (expr instanceof VariableExpression && ((VariableExpression) expr).name == from) {
                    return new VariableExpression(to)
                }
                expr.transformExpression(this)
            }
        })
    }

    /** A {@link LoopEncoder.LoopCallHandler} that frames a contracted (rely-step) call inside a loop body via the
     *  same caller-side framing the straight-line pass uses — havoc the callee's {@code @Modifies} frame, assume
     *  its {@code @Ensures}. Returns false for an uncontracted call (→ the loop still loud-skips it). */
    private LoopEncoder.LoopCallHandler relyCallHandler(MethodNode node) {
        return new LoopEncoder.LoopCallHandler() {
            @Override boolean handle(MethodCallExpression call, Encoder enc, SmtSession s) {
                return assumeCalleeEnsures(s, enc, call, node, null, false)
            }
        }
    }

    private boolean assumeCalleeEnsures(SmtSession s, Encoder enc, Expression callExpr,
                                        MethodNode caller, Object resultHandle, boolean allowSelf,
                                        String resultTupleName = null) {
        if (!(callExpr instanceof MethodCall)) return false
        String name = ((MethodCall) callExpr).methodAsString
        List<Expression> actuals = collectArgumentExpressions((MethodCall) callExpr)
        if (name == null || actuals == null) return false
        ClassNode receiverType = receiverCarrierType(callExpr)                 // Phase 133 — instance call on a carrier
        // Phase 145 — the receiver may itself be a carrier-returning call (`a.f().g()`); resolve its carrier type.
        if (receiverType == null && callExpr instanceof MethodCallExpression) {
            Expression rcv = ((MethodCallExpression) callExpr).objectExpression
            if (rcv != null && !(rcv instanceof ClassExpression) && isCallExpr(rcv)) receiverType = carrierValueExprType(rcv)
        }
        // Resolve on the instance receiver's type, else a static call's owner type (`Length.km(…)` — Phase 142c),
        // else the plain static owner (Phase 215 — `Math.abs(x)`, so the external-spec registry can answer).
        ClassNode forResolve = receiverType != null ? receiverType :
            (ownerCarrierType(callExpr) ?: staticOwnerType(callExpr) ?: instanceReceiverType(callExpr))
        // Phase 219 — STC-inferred actual types, when all are known, disambiguate registry overloads.
        List<ClassNode> inferred = actuals.collect { Expression a -> inferredTypeOf(a) }
        List<String> actualTypeNames = inferred.every { it != null } ? inferred.collect { it.name } : null
        MethodNode callee = resolveContractedCallee(caller, name, actuals.size(), allowSelf, forResolve, actualTypeNames)
        if (callee == null) return false
        // Phase 215 — a registry skeleton must match the actuals' types (the unique-arity fallback can
        // still collide with a JDK overload set: abs(int) spec vs an abs(double) call — sort crash).
        Expression specEnsuresOverride = null
        if (callee.getNodeMetaData(SpecRegistry.SPEC_KEY) != null) {
            // Phase 220 — requires stays receiver-independent (obligation-side wiring is separate work)
            if (!specContractReceiverIndependent(callee, contractAstFor(callee, 'requires'))) return false
            Expression specEns = contractAstFor(callee, 'ensures')
            if (!specContractReceiverIndependent(callee, specEns)) {
                // Phase 221 — receiver-STATE ensures (`result < length()` on String#indexOf): substitute
                // each implicit-this zero-arg call onto the ACTUAL receiver expression, so `length()`
                // becomes `s.length()` and translates through the native seq/oracle machinery.
                Expression recv = (callExpr instanceof MethodCallExpression &&
                    !((MethodCallExpression) callExpr).implicitThis) ?
                    ((MethodCallExpression) callExpr).objectExpression : null
                specEnsuresOverride = recv != null ? substituteReceiverState(callee, specEns, recv) : null
                if (specEnsuresOverride == null) return false
            }
            for (int ti = 0; ti < actuals.size(); ti++) {
                ClassNode at = inferredTypeOf(actuals.get(ti))
                if (at == null) continue
                // Phase 226 — one acceptance rule shared with the typed lookup (Object wildcard,
                // Collection/List kinds, width-classed equality)
                if (!SpecRegistry.formalAccepts(specSimple(callee.parameters[ti].type.name), specSimple(at.name))) {
                    return false
                }
            }
        }
        Expression ensuresAst = specEnsuresOverride != null ? specEnsuresOverride : contractAstFor(callee, 'ensures')
        Set<String> modSet = modifiedNames(callee)
        // Phase 222 — a spec callee's @ThrowsIf arms yield the normal-return contrapositive below.
        List<Map<String, Object>> specArms = callee.getNodeMetaData(SpecRegistry.SPEC_KEY) != null ?
            SpecRegistry.throwsIfArms(callee) : Collections.<Map<String, Object>> emptyList()
        // Nothing to model — no @Ensures, no @Modifies, no arms — so we can't account for the call's effect.
        if (ensuresAst == null && (modSet == null || modSet.isEmpty()) && specArms.isEmpty()) return false

        Parameter[] formals = callee.parameters
        Map<String, Object> bindings = new LinkedHashMap<String, Object>()
        for (int i = 0; i < formals.length; i++) {
            ClassNode ft = formals[i].type
            // A decimal (BigDecimal) actual needs the Real path — plain translate is Int-oriented and returns null
            // (this blocked a `km(2.0)`-style factory call with a decimal argument).
            Object h
            if (enc.sortForType(ft) == s.realSort()) {
                h = enc.asRealValue(actuals.get(i))
            } else {
                h = enc.translate(actuals.get(i))
                // Phase 145 — a carrier-typed argument that is itself a call (`plus(Quantity.mile(1))`): model it.
                if (h == null && Encoder.isCarrier(ft)) h = carrierValueOf(s, enc, actuals.get(i), caller)
            }
            // Phase 226 — a collection-typed formal bound to a NAMED list actual: the contract reads the
            // formal's list oracles (`coll.every { … }`, `coll.count(o)`), so alias them to the actual's —
            // a scalar handle can't carry element/size facts across the boundary. A formal the callee
            // @Modifies is aliased AFTER the framing havoc instead (Phase 229): pre-havoc aliasing would
            // pin the spec's post-state ensures to the stale array.
            if (specSimple(ft.name) in ['Collection', 'List'] &&
                    !(modSet != null && formals[i].name in modSet) &&
                    actuals.get(i) instanceof VariableExpression) {
                String an = ((VariableExpression) actuals.get(i)).name
                // sizeOf/arrayFor/nullityOf MINT on demand (a lazy peek misses oracles the session
                // hasn't touched yet), so the formal is aliased to the actual's canonical oracles
                enc.bindArray(formals[i].name, enc.arrayFor(an))
                enc.bindSize(formals[i].name, enc.sizeOf(an))
                enc.bindNullity(formals[i].name, enc.nullityOf(an))
                // Phase 228 — and REGISTER it as a list name: `c.count(o)` in the spec must take the
                // same bounded-bcount encoding as the caller's `xs.count(5)` (the name-set dispatch
                // otherwise routes the formal to the whole-array count UF, which never unifies)
                enc.registerListName(formals[i].name)
                if (h == null) h = enc.varFor(formals[i].name)   // placeholder scalar; the oracles carry the facts
            }
            if (h == null) return false   // can't faithfully substitute → don't assume
            bindings.put(formals[i].name, h)
            // Phase 185 — alias a Function-typed formal to its named actual, so the callee's @Ensures over
            // `g.apply(…)` is assumed onto the caller's own `apply$<actual>` symbol (the other half of the
            // lemma-reuse bridge; see the @Requires-discharge twin).
            if ((ft?.name == 'java.util.function.Function' || ft?.name == 'java.util.function.BiFunction') &&
                    actuals.get(i) instanceof VariableExpression) {
                enc.aliasFunction(formals[i].name, ((VariableExpression) actuals.get(i)).name)
            }
        }
        // Phase 113 — a tuple result is bound by renaming `result` to the caller's tuple local in the
        // @Ensures (below), not by a scalar `result` term, so its slot accessors resolve to the local's slots.
        if (resultTupleName == null && resultHandle != null) bindings.put('result', resultHandle)

        // Phase 133 — instance call on a carrier receiver (`recv.m(args)`): bind `this` and each component field
        // (so the callee's bare `field` / `this.field` resolves to the receiver's value), and register the carrier
        // types of `this` / formals / `result` so a `o.field` / `result.field` read resolves while translating.
        Map<String, ClassNode> typeReg = new LinkedHashMap<String, ClassNode>()
        if (receiverType != null && callExpr instanceof MethodCallExpression) {
            Expression recvExpr = ((MethodCallExpression) callExpr).objectExpression
            Object recvH = carrierValueOf(s, enc, recvExpr, caller)            // Phase 145 — receiver may itself be a call
            if (recvH == null) return false
            bindings.put('this', recvH)
            typeReg.put('this', receiverType)
            for (FieldNode f : instanceFields(receiverType)) {
                Object fv = enc.carrierField(receiverType, f.name, recvH)      // read each component off the handle
                if (fv != null) bindings.put(f.name, fv)                       // bare `field` == this.field
            }
        }
        for (Parameter p : formals) if (Encoder.isCarrier(p.type)) typeReg.put(p.name, p.type)
        if (resultHandle != null && resultTupleName == null && Encoder.isCarrier(callee.returnType)) {
            typeReg.put('result', callee.returnType)
        }

        // Caller-side framing (Phase 13): for each location the callee @Modifies, snapshot its value
        // *at the call*, pin the callee's `old.X` to that snapshot, then HAVOC the location (fresh
        // symbol) so the caller can no longer assume it unchanged. The callee's @Ensures (if any)
        // re-constrains it relative to the snapshot; with no @Ensures the location is simply unknown
        // afterwards. Locations not in @Modifies stay framed. This closes the cross-call "clobber"
        // hole and gives the recursion a sound `old`. Actuals are translated above (pre-havoc). A null
        // @Modifies frames everything — the pre-Phase-13 behaviour, sound only when the callee truly
        // modifies nothing visible.
        Map<String, Object> savedVar = new LinkedHashMap<String, Object>()
        Map<String, Object> savedArr = new LinkedHashMap<String, Object>()
        Map<String, Object> savedSet = new LinkedHashMap<String, Object>()
        Map<String, Object> savedMapVals = new LinkedHashMap<String, Object>()
        Map<String, Object> savedMapKeys = new LinkedHashMap<String, Object>()
        if (modSet != null) {
            for (String loc : modSet) {
                String callerLoc = callerSideLocation(loc, formals, actuals)
                if (callerLoc == null) continue
                String oldKey = 'old$' + loc   // the callee's @Ensures spells old.<field>
                if (!savedVar.containsKey(oldKey)) {
                    savedVar.put(oldKey, enc.peekVar(oldKey))
                    savedArr.put(oldKey, enc.peekArray(oldKey))
                    savedSet.put(oldKey, enc.peekSet(oldKey))
                    savedMapVals.put(oldKey, enc.peekMapVals(oldKey))
                    savedMapKeys.put(oldKey, enc.peekMapKeys(oldKey))
                }
                enc.bind(oldKey, enc.varFor(callerLoc))            // old.X (scalar) = value at the call
                enc.bindArray(oldKey, enc.arrayFor(callerLoc))     // old.X (array contents) at the call
                enc.bind(callerLoc, s.intVar('havoc$' + callerLoc + '$' + (havocCounter++)))     // havoc
                enc.bindArray(callerLoc, s.arrayVar('havoc$' + callerLoc + '$' + (havocCounter++)))
                // A modified set field is havoced (and snapshotted) too, so a caller can't assume a
                // set the callee may mutate is unchanged, and the callee's `old.s` reframes from the call.
                if (currentSetElementTypes.containsKey(callerLoc)) {
                    enc.bindSet(oldKey, enc.setFor(callerLoc))
                    enc.bindSet(callerLoc, s.setVar('havoc$' + callerLoc + '$' + (havocCounter++)))
                }
                // A modified map field — both value array and key-set — likewise snapshotted and havoced.
                if (currentMapTypes.containsKey(callerLoc)) {
                    enc.putMapVals(oldKey, enc.mapValsFor(callerLoc))
                    enc.putMapKeys(oldKey, enc.mapKeysFor(callerLoc))
                    enc.putMapVals(callerLoc, s.arrayVar('havoc$' + callerLoc + '$' + (havocCounter++)))
                    enc.putMapKeys(callerLoc, s.setVar('havoc$' + callerLoc + '$' + (havocCounter++)))
                }
                // Phase 229 — a MODIFIED collection-typed formal (Collections.sort's `list`) aliases the
                // actual's POST-havoc handles, so the spec's post-state ensures (`list.indices.every …`)
                // constrains the caller's new content; `old.<formal>` was captured above, pre-havoc.
                // Size is deliberately NOT havoced: the shipped mutators are size-preserving, and the
                // implicit size stability is a true, load-bearing fact.
                for (int fi = 0; fi < formals.length; fi++) {
                    if (formals[fi].name == loc && specSimple(formals[fi].type.name) in ['Collection', 'List']) {
                        enc.bindArray(loc, enc.arrayFor(callerLoc))
                        enc.bindSize(loc, enc.sizeOf(callerLoc))
                        enc.bindNullity(loc, enc.nullityOf(callerLoc))
                        enc.registerListName(loc)
                    }
                }
            }
        }

        // Phase 113 — for a tuple result, rename `result` → the caller's tuple local so `result.vN` becomes
        // `<local>.vN`, which the registered tuple local resolves to its per-slot entities.
        Expression effEnsures = (resultTupleName != null && ensuresAst != null) ?
            renameVariable(ensuresAst, 'result', resultTupleName) : ensuresAst
        Map<String, ClassNode> savedTypes = enc.pushScalarTypes(typeReg)
        Object post
        try {
            post = effEnsures != null ? enc.translateWith(effEnsures, bindings) : null
        } finally {
            enc.popScalarTypes(savedTypes)
        }

        // Restore the caller's own `old$X` bindings; the havoced locations stay havoced.
        savedVar.each { String k, Object v -> if (v != null) enc.bind(k, v) }
        savedArr.each { String k, Object v -> if (v != null) enc.bindArray(k, v) }
        savedSet.each { String k, Object v -> if (v != null) enc.bindSet(k, v) }
        savedMapVals.each { String k, Object v -> if (v != null) enc.putMapVals(k, v) }
        savedMapKeys.each { String k, Object v -> if (v != null) enc.putMapKeys(k, v) }

        if (ensuresAst != null && post == null) return false   // @Ensures outside the fragment → skip
        boolean fromRegistry = callee.getNodeMetaData(SpecRegistry.SPEC_KEY) != null
        String calleeLabel = "${callee.declaringClass?.name ?: '?'}#${callee.name}".toString()
        if (post != null) {
            s.assertExpr(post)
            // Phase 231 — VERIFY_EXPLAIN heritage: a proof leaning on a spec's ensures should SAY so,
            // with trusted provenance front and centre (the per-proof twin of the trusted ledger).
            if (Reporter.EXPLAIN) {
                s.explainNoteFact((fromRegistry ? "TRUSTED spec ${calleeLabel} @Ensures"
                                                : "callee ${calleeLabel} @Ensures").toString(), post)
            }
        }
        // Phase 222 — the normal-return contrapositive: this call RETURNED, so no must-throw condition
        // held (valid for iff and one-directional arms alike — both promise cond ⟹ throws). parseInt(s)
        // surviving proves s != null; floorDiv(a, b) surviving proves b != 0. Receiver-dependent or
        // untranslatable conditions are simply not assumed.
        for (Map<String, Object> arm : specArms) {
            Expression c = (Expression) arm.get('cond')
            if (!specContractReceiverIndependent(callee, c)) continue
            Object ch = enc.translateWith(c, bindings)
            if (ch != null) {
                Object neg = s.not(ch)
                s.assertExpr(neg)
                if (Reporter.EXPLAIN) {
                    s.explainNoteFact("TRUSTED survival fact ¬(${c.text.replaceAll(/\s+/, ' ')}) — ${calleeLabel} arm".toString(), neg)
                }
            }
        }
        return true
    }

    /**
     * The caller-side name of a callee {@code @Modifies} location: a field name is shared (same name
     * in the caller); a formal parameter maps to its actual argument when that is a plain variable
     * (else null — a non-nameable actual can't be havoced as a location).
     */
    private static String callerSideLocation(String loc, Parameter[] formals, List<Expression> actuals) {
        for (int i = 0; i < formals.length; i++) {
            if (formals[i].name == loc) {
                Expression act = actuals.get(i)
                return act instanceof VariableExpression ? ((VariableExpression) act).name : null
            }
        }
        loc   // not a formal → a field, same name in the caller
    }

    /** Find a @Requires on the method, walking declared then inherited methods (superclass + interfaces). */
    private static AnnotationNode findRequires(MethodNode m) {
        List<AnnotationNode> direct = m.getAnnotations(REQUIRES_TYPE)
        if (direct != null && !direct.isEmpty()) return direct[0]
        List<AnnotationNode> str = m.getAnnotations(VERIFY_REQUIRES_TYPE)
        if (str != null && !str.isEmpty()) return str[0]
        for (MethodNode inherited : superAndInterfaceDecls(m)) {
            AnnotationNode a = findRequires(inherited)
            if (a != null) return a
        }
        null
    }

    /**
     * Resolve the contract expression of the given kind ("requires" or
     * "ensures") for a method. The verbatim source text lives on the
     * {@link ContractSource} that {@link ContractExpansionTransform}
     * attaches at producer-compile-time — a RUNTIME annotation, so it is
     * present even when {@code m} comes from a decompiled, already-compiled
     * {@link ClassNode} at a downstream call site. The text is re-parsed
     * back into an {@link Expression} for the encoder.
     */
    private static Expression contractAstFor(MethodNode m, String kind) {
        String text = findContractText(m, kind)
        // Normalise the fresh re-parse against m's signature (the one home for pre-resolution parse
        // shapes — e.g. the SAM shorthand f(x) → f.apply(x)), so the encoder deals in one spelling.
        return text != null ? ContractNormalizer.normalize(parseContract(text), m) : null
    }

    /** Read @ContractSource's member, walking superclass then implemented interfaces for inherited contracts. */
    private static String findContractText(MethodNode m, String kind) {
        List<AnnotationNode> sources = m.getAnnotations(CONTRACT_SOURCE_TYPE)
        if (sources != null && !sources.isEmpty()) {
            Expression member = sources[0].getMember(kind)
            if (member instanceof ConstantExpression) {
                Object v = ((ConstantExpression) member).value
                if (v instanceof String && !((String) v).isEmpty()) return (String) v
            }
        }
        for (MethodNode inherited : superAndInterfaceDecls(m)) {
            String t = findContractText(inherited, kind)
            if (t != null) return t
        }
        return null
    }

    /** The same-signature ancestor methods this one inherits a contract from, nearest first: the superclass
     *  declaration, then each directly-implemented interface (Phase 123 — an interface / abstract method's
     *  {@code @Requires} / {@code @Ensures} is inherited by every implementer, as groovy-contracts enforces at
     *  runtime). Deeper superclasses and super-interfaces are reached by the callers' recursion. */
    private static List<MethodNode> superAndInterfaceDecls(MethodNode m) {
        List<MethodNode> out = new ArrayList<MethodNode>()
        ClassNode dc = m.declaringClass
        if (dc == null) return out
        ClassNode sc = dc.superClass
        if (sc != null && sc != ClassHelper.OBJECT_TYPE) {
            MethodNode inh = sc.getMethod(m.name, m.parameters)
            if (inh != null) out.add(inh)
        }
        ClassNode[] itfs = dc.interfaces
        if (itfs != null) for (ClassNode itf : itfs) {
            MethodNode inh = itf.getMethod(m.name, m.parameters)
            if (inh != null) out.add(inh)
        }
        out
    }

    /**
     * Phase 15a — the class-level invariants in effect on {@code cn}: the conjunction
     * of any {@code @Invariant}s declared on the class itself plus every parent's
     * class invariants, walked up the superclass chain.
     *
     * Returned in superclass-first order so a child's clauses follow the parents
     * (purely a readability choice — conjunction is commutative). Each entry is the
     * re-parsed {@link Expression} the encoder can translate, mirroring the
     * round-trip {@link #contractAstFor} performs for method-level pre/postconditions.
     */
    static List<Expression> classInvariantTexts(ClassNode cn) {
        List<Expression> out = new ArrayList<Expression>()
        walkClassInvariants(cn, out)
        // Phase 121 — a class may reach the same invariant by two paths (e.g. two traits extending a common
        // one, or a superclass that also implements the trait); dedupe by source text so it isn't proved twice.
        Set<String> seen = new HashSet<String>()
        List<Expression> deduped = new ArrayList<Expression>()
        for (Expression e : out) { if (seen.add(e.text)) deduped.add(e) }
        deduped
    }

    /** Recursive helper: walk superclass and implemented interfaces/traits first, then add this class's own
     *  invariants (ancestors-first order). Phase 121 — walking {@code interfaces} lets a **trait**'s class
     *  {@code @Invariant} be enforced on the methods of every implementing class. */
    private static void walkClassInvariants(ClassNode cn, List<Expression> out) {
        if (cn == null || cn == ClassHelper.OBJECT_TYPE) return
        walkClassInvariants(cn.superClass, out)
        ClassNode[] itfs = cn.interfaces
        if (itfs != null) for (ClassNode itf : itfs) walkClassInvariants(itf, out)
        // Phase 132 — a @NonNull (reference) field is an implicit object invariant `field != null`. The sibling
        // NullChecker enforces the syntactic half (a literal null store; since 6.0.0-beta-2/GROOVY-12251 also
        // definite initialization, in strict mode). With field-write nullity flowing (this phase), the existing
        // class-invariant machinery proves the value-level whole: establishment (every constructor leaves it
        // non-null under its own preconditions) and preservation (no method nulls it, however the null flows).
        addNonNullFieldInvariants(cn, out)
        List<AnnotationNode> sources = cn.getAnnotations(CLASS_INVARIANT_SOURCE_TYPE)
        if (sources == null || sources.isEmpty()) return
        Expression member = sources[0].getMember('invariants')
        if (!(member instanceof ListExpression)) return
        for (Expression item : ((ListExpression) member).expressions) {
            if (item instanceof ConstantExpression) {
                Object v = ((ConstantExpression) item).value
                if (v instanceof String && !((String) v).isEmpty()) {
                    // Normalise against the DECLARING class of this invariant (the recursion's cn) —
                    // class-scope rewrites only (e.g. the values().length enum-count fold).
                    Expression parsed = ContractNormalizer.normalize(parseContract((String) v), cn)
                    if (parsed != null) out.add(parsed)
                }
            }
        }
    }

    /** Phase 132 — append an implicit `field != null` invariant for each non-static, reference-typed field of
     *  {@code cn} carrying a NullChecker-style @NonNull annotation (on the field or its type use). Primitive
     *  fields can't be null and are skipped; an unencodable clause is dropped later by filterEncodableInvariants. */
    private static void addNonNullFieldInvariants(ClassNode cn, List<Expression> out) {
        List<FieldNode> fields = cn.fields
        if (fields == null) return
        // Phase M-E — a @Monadic carrier's @NonNull content is *conditional* (`present ⟹ value != null`, the
        // Optional contract), not a blanket field invariant — `None` legitimately holds a null content. The
        // carrier models that nullity itself (the M-E datatype axiom); a blanket `value != null` here would be
        // false for `None` and mis-translate the carrier's case-split bodies. So skip carrier classes.
        if (Encoder.isCarrier(cn)) return
        for (FieldNode f : fields) {
            if (f.isStatic()) continue
            ClassNode ft = f.type
            if (ft == null || ClassHelper.isPrimitiveType(ft)) continue
            boolean nonNull = hasAnnotationNamed(f.annotations, NON_NULL_ANNOTATION_NAMES) ||
                              hasAnnotationNamed(ft.annotations, NON_NULL_ANNOTATION_NAMES)
            // Phase 239 — an explicit @Nullable on the same field defeats the implicit invariant
            // (it is both an exit obligation and an entry assumption; nullable wins on either).
            boolean veto = hasAnnotationNamed(f.annotations, NULLABLE_ANNOTATION_NAMES) ||
                           hasAnnotationNamed(ft.annotations, NULLABLE_ANNOTATION_NAMES)
            if (!nonNull || veto) continue
            Expression parsed = parseContract(f.name + ' != null')
            if (parsed != null) out.add(parsed)
        }
    }

    private static Expression parseContract(String contractText) {
        try {
            List<ASTNode> parsed = new AstBuilder().buildFromString(
                CompilePhase.CONVERSION, true, contractText)
            // AstBuilder wraps in BlockStatement → ExpressionStatement → Expression
            if (parsed.isEmpty()) return null
            ASTNode top = parsed[0]
            if (top instanceof BlockStatement) {
                BlockStatement bs = (BlockStatement) top
                if (bs.statements.size() == 1 &&
                    bs.statements[0] instanceof ExpressionStatement) {
                    return ((ExpressionStatement) bs.statements[0]).expression
                }
            }
            return null
        } catch (Throwable t) {
            return null
        }
    }

    /** Argument expressions in the order they appear at the call site. */
    private static List<Expression> collectArgumentExpressions(MethodCall mc) {
        Expression args = mc.arguments
        if (args == null) return Collections.<Expression>emptyList()
        // arguments is typically an ArgumentListExpression
        if (args.metaClass.respondsTo(args, 'getExpressions')) {
            try {
                List<Expression> es = (List<Expression>) args.invokeMethod('getExpressions', null)
                return es != null ? es : Collections.<Expression>emptyList()
            } catch (Throwable ignored) {}
        }
        Collections.<Expression>emptyList()
    }
}
