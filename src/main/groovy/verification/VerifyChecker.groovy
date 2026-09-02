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
    private static final ClassNode UNDERRELY_TYPE = ClassHelper.make(UnderRely)   // Phase 244 — wiring completeness
    private static final String RG_LAW_KEY = 'verification.relyGuaranteeLaw'
    /** Phase 244 — metadata on a synthesized guarantee-conformance twin: {@code [methodName, predName, role]}. */
    private static final String RG_CONF_KEY = 'verification.guaranteeConformance'
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
        // (No early return on empty predicate lists: the Phase 244 passes below must still see a
        // body-level @Guarantee with no predicate, and report it loudly.)

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

        // Phase 244 — guarantee CONFORMANCE (slice 5 of the SEQ/PAR ladder): a @Guarantee('Role') on a
        // BODY method (a non-predicate) declares that the method's own-step transitions honour the
        // Role's guarantee predicate — the obligation the §VII argument had left to hand-inspection.
        // Discharged on a synthesised twin: the method's body MINUS the prepended env step (the
        // `$rely$…` call @UnderRely inserts — the guarantee covers the thread's OWN step, not the
        // environment's), with @Requires kept (the rely-stable precondition stands in for any
        // reachable post-env state) and @Ensures `pred(old.f…, f…)` over the fields the predicate's
        // post-state parameters name.
        boolean conformanceAdopted = false
        for (MethodNode m : new ArrayList<MethodNode>(classNode.methods)) {
            if (isRgPredicate(m)) continue
            String role = rgThread(m, GUARANTEE_TYPE)
            if (role == null) continue
            conformanceAdopted = true
            MethodNode pred = null
            for (Object[] g : guars) if (g[0] == role) { pred = (MethodNode) g[1]; break }
            runGuaranteeConformance(classNode, m, role, pred)
        }

        // Phase 244 — unbacked relies, in classes that ADOPT the conformance discipline (some body
        // method declares @Guarantee): a role-based @UnderRely assumes its @Rely predicate holds of
        // the environment, and the existing G ⟹ R lemmas justify that from the peers' guarantees —
        // but only if a peer role DECLARES a guarantee. With no other-role @Guarantee predicate the
        // assumption has nothing in the class justifying it: loudly. A class with no body-level
        // @Guarantee keeps the modular posture (a single-sided rely is an interface assumption,
        // justified outside the class — like a @Requires at a boundary); an @UnderRely naming a
        // hand-written rely-step METHOD is likewise untouched (its own @Ensures is its backing).
        if (!conformanceAdopted) return
        Set<String> underRoles = new LinkedHashSet<String>()
        Map<String, MethodNode> roleAnchor = new HashMap<String, MethodNode>()
        for (MethodNode m : classNode.methods) {
            for (String role : underRelyRolesOf(m)) {
                underRoles.add(role)
                if (!roleAnchor.containsKey(role)) roleAnchor.put(role, m)
            }
        }
        for (String role : underRoles) {
            MethodNode relyPred = null
            for (Object[] r : relies) if (r[0] == role) { relyPred = (MethodNode) r[1]; break }
            if (relyPred == null) continue
            boolean backed = false
            for (Object[] g : guars) if (g[0] != role) { backed = true; break }
            if (!backed) {
                MethodNode anchor = roleAnchor.get(role)
                addStaticTypeError(Reporter.formatUnbackedRely(classNode.nameWithoutPackage,
                    relyPred.name, role, anchor.name), anchor)
            }
        }
    }

    /** The role names an {@code @UnderRely} on {@code m} carries (a single string or a list). */
    private static List<String> underRelyRolesOf(MethodNode m) {
        List<AnnotationNode> anns = m.getAnnotations(UNDERRELY_TYPE)
        if (anns == null || anns.isEmpty()) return Collections.emptyList()
        List<String> out = new ArrayList<String>()
        for (AnnotationNode a : anns) {
            Expression v = a.getMember('value')
            if (v instanceof ConstantExpression && ((ConstantExpression) v).value != null) {
                out.add(((ConstantExpression) v).value.toString())
            } else if (v instanceof ListExpression) {
                for (Expression e : ((ListExpression) v).expressions) {
                    if (e instanceof ConstantExpression && ((ConstantExpression) e).value != null) {
                        out.add(((ConstantExpression) e).value.toString())
                    }
                }
            }
        }
        out
    }

    /**
     * Phase 244 — synthesise and discharge the guarantee-conformance twin of {@code m}: the method's
     * own-step transition must satisfy the {@code @Guarantee(role)} predicate. See the caller's
     * comment for the semantics; loud skips where the shape is outside the fragment (no predicate
     * for the role, a static method, predicate post-state parameters that don't name fields).
     */
    private void runGuaranteeConformance(ClassNode cn, MethodNode m, String role, MethodNode pred) {
        // Anchor every conformance diagnostic at the @Guarantee ANNOTATION's own position: STC
        // dedups errors per source position (StaticTypeCheckingVisitor.addError keys on
        // line<<16+column), so an anchor shared with the real method's other diagnostics would be
        // silently dropped — the live form of the Phase 94 hazard.
        List<AnnotationNode> gAnns = m.getAnnotations(GUARANTEE_TYPE)
        ASTNode at = (gAnns != null && !gAnns.isEmpty() && gAnns.get(0).lineNumber > 0) ? gAnns.get(0) : m
        try {
            runGuaranteeConformance0(cn, m, role, pred, at)
        } catch (Throwable t) {
            // A declared conformance must never pass silently: if the twin cannot be built or
            // verified, say so loudly rather than let the class sweep swallow it.
            addStaticTypeError(Reporter.formatGuaranteeConformanceSkipped(m.name,
                "the conformance twin could not be verified (${t.class.simpleName}: ${t.message})"), at)
        }
    }

    private void runGuaranteeConformance0(ClassNode cn, MethodNode m, String role, MethodNode pred, ASTNode at) {
        if (pred == null) {
            addStaticTypeError(Reporter.formatGuaranteeConformanceSkipped(m.name,
                "no @Guarantee('${role}') predicate method in the class to conform to"), at)
            return
        }
        if (m.isStatic()) {
            addStaticTypeError(Reporter.formatGuaranteeConformanceSkipped(m.name,
                "a static method has no instance transition to check against '${pred.name}'"), at)
            return
        }
        int n = pred.parameters.length.intdiv(2)
        List<String> fields = new ArrayList<String>()
        for (int i = 0; i < n; i++) {
            String fn = pred.parameters[n + i].name
            if (cn.getField(fn) == null) {
                addStaticTypeError(Reporter.formatGuaranteeConformanceSkipped(m.name,
                    "predicate '${pred.name}' post-state parameter '${fn}' names no field of ${cn.nameWithoutPackage}"), at)
                return
            }
            fields.add(fn)
        }
        StringBuilder call = new StringBuilder(pred.name).append('(')
        for (int i = 0; i < n; i++) { if (i > 0) call.append(', '); call.append('old.').append(fields.get(i)) }
        for (int i = 0; i < n; i++) call.append(', ').append(fields.get(i))
        call.append(')')

        Statement body = (Statement) m.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (body == null) body = m.code
        if (!(body instanceof BlockStatement)) {
            addStaticTypeError(Reporter.formatGuaranteeConformanceSkipped(m.name,
                "the method body is not a plain block (${body?.class?.simpleName})"), at)
            return
        }
        // Drop the `$rely$…` env step(s) wherever they sit in the top-level list: the guarantee
        // covers the thread's OWN step, not the environment's. DEEP-COPY the rest — the real
        // method's verification annotates the shared nodes, and a twin re-walk over them breaks.
        List<Statement> kept = new ArrayList<Statement>()
        for (Statement st : ((BlockStatement) body).statements) if (!isRelyStepCall(st)) kept.add(st)
        BlockStatement twinBody = (BlockStatement) ContractExpansionTransform.copyBody(
            new BlockStatement(kept, ((BlockStatement) body).variableScope), false)

        MethodNode twin = new MethodNode(m.name + '$guarantee$' + role, m.modifiers, m.returnType,
            m.parameters, ClassNode.EMPTY_ARRAY, twinBody)
        twin.declaringClass = cn
        twin.addAnnotation(new AnnotationNode(ENSURES_TYPE))
        AnnotationNode cs = new AnnotationNode(CONTRACT_SOURCE_TYPE)
        cs.addMember('ensures', new ConstantExpression(call.toString()))
        String reqText = findContractText(m, 'requires')
        if (reqText != null) {
            twin.addAnnotation(new AnnotationNode(REQUIRES_TYPE))
            cs.addMember('requires', new ConstantExpression(reqText))
        }
        twin.addAnnotation(cs)
        twin.setSourcePosition(at)      // the @Guarantee annotation's line — a position no other diagnostic owns
        twin.putNodeMetaData(RG_CONF_KEY, [m.name, pred.name, role] as String[])
        beforeVisitMethod(twin)
        afterVisitMethod(twin)
    }

    /** A statement that is a call to a synthesised {@code $rely$<Role>} env step. */
    private static boolean isRelyStepCall(Statement st) {
        if (!(st instanceof ExpressionStatement)) return false
        Expression e = ((ExpressionStatement) st).expression
        if (e instanceof MethodCallExpression) return ((MethodCallExpression) e).methodAsString?.startsWith('$rely$')
        if (e instanceof StaticMethodCallExpression) return ((StaticMethodCallExpression) e).method?.startsWith('$rely$')
        false
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
        collectChannelContracts(node)
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

            // Phase 240 — PAR disjointness (fork-window interference), BEFORE the Phase 118/119
            // desugaring flattens `async { … }` arms into the body: the safe-value model those
            // phases apply is sound only when nothing an arm touches is concurrently written.
            // Check that side condition and error loudly on a violation — without this, a
            // stale-read race passes as a proof of the post-write value. Contained: an analysis
            // failure never breaks the compile flow.
            // Phase 248 — literal-bounded channel loops unroll first, so the structural walk and the
            // channel rewrite both see one-shot traffic (a symbolic bound stays a loop: the frontier).
            Set<String> streamChans = new HashSet<String>()
            if (body instanceof BlockStatement) collectChannelVars((BlockStatement) body, streamChans)
            if (!streamChans.isEmpty()) {
                Statement unrolled = unrollLiteralChannelLoops(body, streamChans)
                if (!unrolled.is(body)) {
                    node.putNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY, unrolled)
                    body = unrolled
                }
            }
            try {
                checkParInterference(node, body)
            } catch (Throwable ignored) {
            }

            // Phase 242 — a constrained channel PARAM's statement send becomes its contract assert
            // (`ch.send(e)` → `assert φ(e)`): the producer's half of the modular channel contract.
            Statement deSend = desugarParamChannelSends(body)
            if (!deSend.is(body)) {
                node.putNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY, deSend)
                body = deSend
            }

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
            List<Object[]> ghostErrors = new ArrayList<Object[]>()
            Statement deChan = desugarChannels(body, currentChannelBounds, currentScalarTypes, paramNames(node), node, ghostErrors)
            deChan = desugarGuardedSelects(deChan)      // Phase 275 — a masked select's index, with or without a stream model
            for (Object[] ge : ghostErrors) addStaticTypeError(Reporter.formatGhostMisuse((String) ge[0], (String) ge[1]), (ASTNode) ge[2])   // Phase 259
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
                if (as.getNodeMetaData(ASSUME_ONLY_KEY) != null) continue
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
                    if (enc.tryBindChannelSelect(a.name, a.rhs)) continue     // Phase 249 — an ALT's index / value
                    if (enc.tryBindAwaitAny(a.name, a.rhs)) continue
                    // Phase 242 — the modular channel receive (mirrors checkPath): a channel-typed
                    // param's first()/awaited receive() binds a fresh value with the element bounds.
                    if (enc.tryBindChannelReceive(a.name, a.rhs, currentChannelRecvParams)) continue
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
                // The hint pastes the PRINTED text into that @Requires, so it is offered only for a real
                // asserted expression: a synthesized obligation prints its own prose wording ("the receive on
                // 'c' (line n) may block forever — …"), which would paste an English sentence into a contract.
                String label = (String) asite.node.getNodeMetaData(ASSERT_LABEL_KEY)   // Phase 252 — a synthesized assert's own wording
                boolean overParam = label == null && referencesParameter(asite.cond, currentMethod)
                addStaticTypeError(withRepro(Reporter.formatAssertion(label != null ? label : asite.cond.text, r, overParam), r, 'AssertionError'), asite.node)
            }
            return
        }
        if (site instanceof IndexSite) {
            IndexSite ix = (IndexSite) site
            // m[k] on a map is a key lookup, not a bounds-checked array index — no obligation.
            if (currentMapTypes.containsKey(ix.receiver)) return
            // Phase 242 — first()/head() on a CHANNEL is a receive: it BLOCKS until an element
            // arrives (delivery is the assumed structural half), it never throws on "empty", and
            // the type has no size() — the collection non-empty obligation would be factually
            // wrong here. (The receive's value contract is handled by tryBindChannelReceive.)
            if (currentChannelNames.contains(ix.receiver)) return
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
            // Phase 245 — a locally-CONSTRUCTED channel (create()/subscribe()/a pipeline op) is a
            // factory result and never null: an un-rewritten call on it (send/close/toList in a
            // drain shape the scalar model refuses) carries no deref obligation. A channel PARAM
            // stays obligated — it can be null, and @NotNull is its honest discharge (Phase 242).
            if (currentChannelLocalNames.contains(df.receiver)) return
            // Phase 257 — likewise a HELD ChannelSelect (`ChannelSelect alt = ChannelSelect.from(..)[.fair()]`):
            // a factory result, never null; `alt.select()` in the loop carries no deref obligation.
            if (currentHeldSelectLocalNames.contains(df.receiver)) return
            // Phase 277 — and a local bound to a `new …`: a constructor yields an object or throws.
            if (currentNewLocalNames.contains(df.receiver)) return
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
        if (handleAsserts && st instanceof AssertStatement && st.getNodeMetaData(ASSUME_ONLY_KEY) != null) return   // Phase 254 — assumed, reported elsewhere
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
    private static Statement desugarGuardedSelects(Statement body) {
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
    private static void collectHeldOfferGuards(Statement body, Map<String, List<Expression>> out) {
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
    private static void collectMaskedSelects(Statement body, Map<String, String> out, Map<String, List<Expression>> guards) {
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
    private static int guardedSelectArity(Expression rhs, Map<String, List<Expression>> guards) {
        List<Expression> mask = awaitedSelectMask(rhs)
        if (mask != null && !mask.isEmpty()) return mask.size()
        List<Expression> og = offerGuardsFor(rhs, guards)
        og == null ? 0 : og.size()
    }

    /** The per-offer guards behind an awaited select — through a held instance, or inline. */
    private static List<Expression> offerGuardsFor(Expression rhs, Map<String, List<Expression>> guards) {
        MethodCallExpression sel = awaitedSelectCall(rhs)
        if (sel == null) return null
        Expression recv = stripCasts(sel.objectExpression)
        if (recv instanceof VariableExpression) return guards == null ? null : guards.get(((VariableExpression) recv).name)
        selectOfferGuards(recv)
    }

    /** `r.index` / `r.getIndex()` → `r$index`, for the result vars bound above. */
    private static Expression rewriteGuardedExpr(Expression e, Map<String, String> bound) {
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
    private static List<Expression> selectOffersArgs(Expression e) {
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
    private static Expression guardClosureBody(Expression e) {
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

    /** One offer's conjoined guard — `receive(c).when { a }.when { b }` is `a && b` — else null when unguarded.
     *  A `when` whose argument is not a single-expression closure yields null too, and the caller then treats
     *  the offer as unmodelled rather than as unguarded (silently dropping a guard would be unsound). */
    private static Expression offerGuardOf(Expression offer, boolean[] unmodelled) {
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
    private static List<Expression> selectOfferGuards(Expression selectExpr) {
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
    private static void rebindLoopSpec(Statement from, Statement to, Map<String, String> bound, Map<String, List<Expression>> guards) {
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
    private static Statement rewriteGuardedStmt(Statement st, Map<String, String> bound, Map<String, List<Expression>> guards) {
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
    private static Statement desugarChannels(Statement body, Map<String, List<long[]>> bounds,
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
    private static class AltInfo {
        String name
        List<Integer> branches = new ArrayList<Integer>()
        List<String> elems = new ArrayList<String>()
        List<Expression> heads = new ArrayList<Expression>()
        List<Integer> keep
    }

    /** Phase 247 — the state of one channel rewrite: the var classes, and the per-channel element
     *  counters that make the FIFO pairing explicit (send k ↔ receive k). */
    private static class ChanRewrite {
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
    private static String chanRoot(Expression recv, Set<String> ch) {
        Expression e = stripCasts(recv)
        while (e instanceof MethodCallExpression && ((MethodCallExpression) e).methodAsString in CHANNEL_PIPE_OPS) {
            e = stripCasts(((MethodCallExpression) e).objectExpression)
        }
        (e instanceof VariableExpression && ch.contains(((VariableExpression) e).name)) ? ((VariableExpression) e).name : null
    }

    /** The pipeline ops applied between {@code recv} and its base var, bottom-up. */
    private static List<String> chanChainOps(Expression recv) {
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
    private static void collectChannelParents(BlockStatement body, Set<String> ch, Map<String, String> parent,
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
    private static void countChannelSends(BlockStatement body, Set<String> ch, Map<String, Integer> totals) {
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
    private static final List<String> CHANNEL_EXACT_OPS = ['map', 'subscribe'].asImmutable()

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
    private static Map<String, String> channelModelVerdicts(BlockStatement body, Set<String> ch, Set<String> params,
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
    private static boolean unrollableLoopBody(Statement s) {
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
    private static void collectChannelVars(BlockStatement body, Set<String> ch) {
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

    /** `BroadcastChannel.create(...)` — one-to-many delivery; each `subscribe()` hands the receiver its own
     *  per-subscriber `AsyncChannel` (Phase 241). Same AST shapes as {@link #isChannelCreate}. */
    private static boolean isBroadcastCreate(Expression e) {
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
    private static final List<String> CHANNEL_PIPE_OPS = ['map', 'filter', 'tap', 'merge', 'split', 'subscribe'].asImmutable()

    /** A channel-valued expression: a channel var, or a pipeline/derivation op on one. */
    private static boolean isChannelExpr(Expression e, Set<String> ch) {
        if (e instanceof VariableExpression) return ch.contains(((VariableExpression) e).name)
        if (e instanceof MethodCallExpression) {
            MethodCallExpression m = (MethodCallExpression) e
            return (m.methodAsString in CHANNEL_PIPE_OPS) && isChannelExpr(m.objectExpression, ch)
        }
        false
    }

    private static void rewriteChStatements(List<Statement> stmts, ChanRewrite rw, List<Statement> out) {
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
    private static void rewriteSelect(String name, List<Expression> alt, DeclarationExpression de, ChanRewrite rw, List<Statement> out) {
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
    private static String chanNameOf(Expression e) {
        Expression x = stripCasts(e)
        x instanceof VariableExpression ? ((VariableExpression) x).name : null
    }

    private static List<Expression> selectFromArgs(Expression e) {
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
    private static List<Expression> awaitedSelectMask(Expression rhs) {
        MethodCallExpression sel = awaitedSelectCall(rhs)     // one matcher, not a parallel one
        if (sel == null) return null
        Expression args = sel.arguments
        if (!(args instanceof TupleExpression)) return null
        List<Expression> flags = ((TupleExpression) args).expressions
        flags.isEmpty() ? null : flags
    }

    private static List<Expression> awaitedSelectArgs(Expression rhs) { awaitedSelectArgs(rhs, null) }

    private static List<Expression> awaitedSelectArgs(Expression rhs, Map<String, SelectRef> selectVars) {
        SelectRef r = awaitedSelect(rhs, selectVars)
        r == null ? null : r.chans
    }

    /** Phase 247 — `for (v in ch) { body }` over a channel with k known sends becomes k copies of the
     *  body, the i-th with `v` bound to the i-th element (through any map stages) and the body's own
     *  locals renamed apart. Exact for the drain of a closed bounded stream; the drain's blocking
     *  (until close) is certified separately by the Phase 245 wait-for analysis on the original body. */
    private static void unrollChannelDrain(ForStatement st, ChanRewrite rw, List<Statement> out) {
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
    private static Statement copyRenamed(Statement s, Map<String, Expression> ren) { copyRenamed(s, ren, false) }

    /** As above; {@code lenient} keeps a statement kind outside the copying fragment SHARED (unrenamed) instead of
     *  failing — for the arm renamer, whose live closures carry groovy-contracts' runtime-check plumbing. */
    private static Statement copyRenamed(Statement s, Map<String, Expression> ren, boolean lenient) {
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
    private static LoopSpec renameSpec(LoopSpec spec, Map<String, Expression> ren) {
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
    private static String chanBaseVar(Expression e, ChanRewrite rw) {
        Expression x = stripCasts(e)
        while (x instanceof MethodCallExpression && ((MethodCallExpression) x).methodAsString in CHANNEL_PIPE_OPS) {
            x = stripCasts(((MethodCallExpression) x).objectExpression)
        }
        (x instanceof VariableExpression && rw.ch.contains(((VariableExpression) x).name)) ? ((VariableExpression) x).name : null
    }

    /** Resolve a channel-valued expression to its scalar value: expand a pipeline-derived var to its recorded
     *  definition, beta-reduce each `map { f }` over its upstream value, and read receives / drains as the
     *  indexed elements (Phase 247). */
    private static Expression rewriteChExpr(Expression e, ChanRewrite rw) {
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
    private static class StreamInfo {
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
    private static class ConsumerInfo {
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
    private static class StreamScan {
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
    private static List<List<Statement>> topLevelBlocks(BlockStatement body) {
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

    private static MethodCallExpression sendCallOf(Statement st, Set<String> ch) {
        if (!(st instanceof ExpressionStatement)) return null
        Expression e = ((ExpressionStatement) st).expression
        if (!(e instanceof MethodCallExpression) || ((MethodCallExpression) e).methodAsString != 'send') return null
        Expression recv = stripCasts(((MethodCallExpression) e).objectExpression)
        (recv instanceof VariableExpression && ch.contains(((VariableExpression) recv).name)) ? (MethodCallExpression) e : null
    }

    /** The unit counter of a loop — `i` with exactly one `i = i + 1` / `i++` / `i += 1` per iteration — with its
     *  entry value from the enclosing block; `[name, initExpr]`, or null (with a reason in {@code why}). */
    private static Object[] unitCounter(LoopingStatement loop, List<Statement> enclosing, Set<String> params, String[] why) {
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

    private static boolean isUnitIncrement(Expression e, String v) { unitIncrementTarget(e) == v }

    /** Phase 254 — `while (true)`: the non-terminating process's loop. */
    private static boolean isForever(LoopingStatement loop) {
        if (!(loop instanceof WhileStatement)) return false
        Expression g = stripCasts(((WhileStatement) loop).booleanExpression.expression)
        g instanceof ConstantExpression && Boolean.TRUE.equals(((ConstantExpression) g).value)
    }

    /** `i++` / `++i` / `i += 1` / `i = i + 1` → `i`; else null. */
    private static String unitIncrementTarget(Expression e) {
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
    private static boolean namesWithin(Expression e, Set<String> names) {
        boolean[] ok = [true]
        e.visit(new CodeVisitorSupport() {
            @Override void visitVariableExpression(VariableExpression ve) { if (!names.contains(ve.name) && ve.name != 'this') ok[0] = false }
        })
        ok[0]
    }

    private static Set<String> varNames(Expression e) {
        final Set<String> out = new HashSet<String>()
        e.visit(new CodeVisitorSupport() { @Override void visitVariableExpression(VariableExpression ve) { out.add(ve.name) } })
        out
    }

    /**
     * Phase 251 — the streaming scan: which channels are produced by one send in one specified
     * unit-counter loop (and are otherwise only drained), and why the other loop-send channels are out.
     */
    /** Phase 258 — the value alias of an ALT loop: `T q = (cast) r.value` at the body's top level, else null. */
    private static String valueAliasOf(ConsumerInfo ci) {
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
    private static void guardedReplyStreams(StreamScan scan, Map<String, List<MethodCallExpression>> allSends, Set<String> ch,
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
    private static String staticTotalText(StreamInfo info, Set<String> ch) {
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
    private static void computeCycles(StreamScan scan, Map<String, String> parent, Set<String> ch) {
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

    private static StreamScan scanStreams(BlockStatement body, Set<String> ch, Map<String, String> parent,
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
    private static MethodCallExpression receiveCallOf(Expression e) {
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
    private static String entryText(Expression counterInit) {
        Expression ci = stripCasts(counterInit)
        ci instanceof ConstantExpression ? String.valueOf(((ConstantExpression) ci).value) :
        ci instanceof VariableExpression ? ((VariableExpression) ci).name : "(${ci.text})".toString()
    }

    /** True when the call sits inside any loop of the body (at any depth, arms included). */
    private static boolean insideLoop(BlockStatement body, MethodCallExpression target) {
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

    private static final ClassNode INT_LIST_TYPE = GenericsUtils.makeClassSafeWithGenerics(ClassHelper.LIST_TYPE, new GenericsType(ClassHelper.Integer_TYPE))

    private static Statement listDecl(String name, ASTNode at) {
        DeclarationExpression de = new DeclarationExpression(new VariableExpression(name, INT_LIST_TYPE),
            Token.newSymbol(Types.ASSIGN, at.lineNumber, at.columnNumber), new ListExpression())
        de.setSourcePosition(at)
        ExpressionStatement st = new ExpressionStatement(de)
        st.setSourcePosition(at)
        st
    }

    /** The transform `f` a map-derived var applies to its root's element, as an expression over {@code elem}. */
    private static Expression derivedValue(String d, Expression elem, ChanRewrite rw) {
        String hole = '$elem$'
        Expression chain = rw.withElement(rw.rootOf(d), hole) { rewriteChExpr(new VariableExpression(d), rw) }
        substituteVar(chain, hole, elem)
    }

    /** {@code e} with every occurrence of the variable {@code name} replaced by {@code by} — closure bodies
     *  included (a `ClosureExpression` does not transform its code by itself, so quantifier closures are rebuilt). */
    private static Expression substituteVar(Expression e, String name, Expression by) {
        substituteVars(e, Collections.singletonMap(name, by))
    }

    /** Multi-name substitution; a `VariableExpression` replacement is re-minted per occurrence. */
    private static Expression substituteVars(Expression e, Map<String, Expression> ren) {
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
    private static Statement rewriteStreamLoop(LoopingStatement loop, List<StreamInfo> infos, ChanRewrite rw) {
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
    private static List<Statement> loopingAlt(DeclarationExpression de, ChanRewrite rw) {
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
    private static List<Expression> consumerBoundInvariants(ConsumerInfo ci, ChanRewrite rw) {
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
    private static Expression cursorInvariant(ConsumerInfo consumer, ChanRewrite rw, boolean stableOnly = false) {
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
    private static Set<String> assignedNames(Statement s) {
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
    private static List<Statement> relyBlock(Collection<String> vars, ChanRewrite rw, ASTNode at) {
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
    private static Set<String> takenVars(ConsumerInfo ci, ChanRewrite rw) {
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
    private static Expression takenGhostRewrite(Expression e, ChanRewrite rw) {
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
    private static List<Expression> specInContext(List<Expression> invs, Statement loop, ChanRewrite rw) {
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
    private static Statement takenAppend(String v, ChanRewrite rw, ASTNode at) {
        ConsumerInfo ci = rw.curConsumer
        Expression val = ContractExpansionTransform.reparse("${rw.relyName.get(v)}[${ci.counter} - ${entryText(ci.counterInit)}]")
        val == null ? null : addStmt(v + '$taken', val, at)
    }

    /** Phase 252 — the shadow-list read a sanctioned receive becomes inside its consumer loop: `x$q[i - a]`. */
    private static Expression consumerRead(MethodCallExpression recv, ChanRewrite rw) {
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
    private static List<Statement> consumerAssert(MethodCallExpression recv, ChanRewrite rw) {
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
    private static List<MethodCallExpression> sanctionedReceivesIn(Expression e, ChanRewrite rw) {
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
    private static List<Expression> streamInvariants(StreamInfo info, ChanRewrite rw, boolean stableOnly = false) {
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
    private static List<Expression> sendsFollowTakes(StreamInfo info, ChanRewrite rw) {
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
    private static int topIndexOf(List<Statement> top, final ASTNode node) {
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
    private static List<Expression> stableUserConjuncts(List<Expression> invs) {
        List<Expression> out = new ArrayList<Expression>()
        List<Expression> conj = new ArrayList<Expression>()
        for (Expression inv : invs) splitAnd(inv, conj)
        for (Expression c : conj) if (ghostSizeOnlyInBounds(c)) out.add(c)
        out
    }

    private static void splitAnd(Expression e, List<Expression> out) {
        if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.LOGICAL_AND) {
            splitAnd(((BinaryExpression) e).leftExpression, out); splitAnd(((BinaryExpression) e).rightExpression, out)
        } else out.add(e)
    }

    private static boolean isGhostList(Expression e) {
        Expression x = stripCasts(e)
        x instanceof VariableExpression && (((VariableExpression) x).name.endsWith('$taken') || ((VariableExpression) x).name.endsWith('$q'))
    }

    private static boolean ghostSizeOnlyInBounds(Expression c) {
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
    private static boolean loopConstant(Expression e, StreamInfo info, ChanRewrite rw) {
        for (String n : varNames(e)) if (rw.ch.contains(n) || writesVar(info.loop.loopBlock, n)) return false
        true
    }

    /** Phase 252 — the sent expression with each receive alias (`def v = in.first()` in the same loop) replaced
     *  by the element it read, `in$q[(k + a) - a_c]` — spelled over the relation's index {@code k}. */
    private static Expression aliasedSend(StreamInfo info, String k, String initText, ChanRewrite rw) {
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
    private static Expression norm(Expression e, ChanRewrite rw) {
        if (rw.method == null) return e
        Expression n = ContractNormalizer.normalize(e, rw.method)
        n != null ? n : e
    }

    /** Statements of a producer loop body with the stream's sends / closes rewritten (nested blocks and ifs walked). */
    private static List<Statement> rewriteStreamStmts(List<Statement> stmts, ChanRewrite rw) {
        boolean savedMode = rw.readsAsTaken
        rw.readsAsTaken = false                                                  // Phase 258 — body reads go through rely views
        try { rewriteStreamStmts0(stmts, rw) } finally { rw.readsAsTaken = savedMode }
    }

    private static List<Statement> rewriteStreamStmts0(List<Statement> stmts, ChanRewrite rw) {
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

    private static Statement addStmt(String list, Expression val, ASTNode at) {
        MethodCallExpression add = new MethodCallExpression(new VariableExpression(list), 'add', new ArgumentListExpression(val))
        add.setSourcePosition(at)
        ExpressionStatement st = new ExpressionStatement(add)
        st.setSourcePosition(at)
        st
    }

    /** Phase 251 — a `for (v in c)` drain of a streaming channel: the same loop over the shadow list, its
     *  LoopSpec renamed to match (the loop engine then decides — a per-element body proves, an accumulating
     *  one is its loud skip). */
    private static Statement streamDrainLoop(ForStatement st, String q, String c, ChanRewrite rw) {
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
    private static BlockStatement desugarPartnerDrains(BlockStatement body, Set<String> ch, Set<String> params) {
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
    private static Set<String> channelOps(Statement st, Set<String> ch, boolean sends) {
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
    private static BlockStatement alphaRenameArms(BlockStatement body) {
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
    private static final int CHANNEL_UNROLL_LIMIT = 32

    /** Phase 257 — the runtime hosting the compiler has GROOVY-12320's claim-based ChannelSelect (6.0.0-beta-4+):
     *  exactly one branch dequeues, losers are untouched, `fair()` / `random()` policies exist. Probed by
     *  reflection once: the runtime that runs the type checker is the runtime the code will run on. */
    static final boolean CLAIM_SELECT = probeClaimSelect()
    /** Phase 271 — the runtime hosting the checker carries GROOVY-12323's arbitrated select (offers/send/receive). */
    static final boolean ARBITRATED_SELECT = probeArbitratedSelect()

    /** Phase 274 — does the hosting runtime carry GROOVY-12324's guarded select? */
    static final boolean GUARDED_SELECT = probeGuardedSelect()

    /** Phase 276 — …and GROOVY-12326's per-offer `when` guard? */
    static final boolean WHEN_GUARD = probeWhenGuard()

    private static boolean probeArbitratedSelect() {
        try {
            Class<?> cs = Class.forName('groovy.concurrent.ChannelSelect')
            return cs.methods.any { it.name == 'offers' }
        } catch (Throwable ignored) {
            return false
        }
    }
    private static boolean probeClaimSelect() {
        try { Class.forName('groovy.concurrent.ChannelSelect').getMethod('fair'); return true } catch (Throwable ignored) { return false }
    }

    /** Phase 274 — GROOVY-12324's per-select precondition mask: `select(boolean... enabled)`, one flag per
     *  offer, indices preserved. The guarded ALT of occam and JCSP, at last spellable. */
    private static boolean probeGuardedSelect() {
        try { Class.forName('groovy.concurrent.ChannelSelect').getMethod('select', boolean[].class); return true }
        catch (Throwable ignored) { return false }
    }

    /** Phase 276 — GROOVY-12326's per-offer guard: `receive(c).when { cond }`, the flag bound to its branch
     *  by syntax rather than by position, and consulted once per select so a held instance stays usable. */
    private static boolean probeWhenGuard() {
        try { Class.forName('groovy.concurrent.ChannelSelect$Offer').getMethod('when', java.util.function.BooleanSupplier.class); return true }
        catch (Throwable ignored) { return false }
    }

    /** Phase 257 — a `ChannelSelect` chain: its channel args, its policy, and whether it is a held instance. */
    private static class SelectRef {
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
    private static SelectRef selectChainInfo(Expression e) {
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
        if (args == null) return null
        SelectRef r = new SelectRef(); r.chans = args; r.policy = policy; r.fromCall = x
        r.fromCalls.add(x)
        r
    }

    /** Held select instances: `X = ChannelSelect.from(..)[.policy()]` declarations anywhere in the body. */
    private static Map<String, SelectRef> collectSelectVars(Statement body) {
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
    private static SelectRef awaitedSelect(Expression rhs, Map<String, SelectRef> selectVars) {
        MethodCallExpression sel = awaitedSelectCall(rhs)
        if (sel == null) return null
        selectRefOf(sel.objectExpression, selectVars)
    }

    private static SelectRef selectRefOf(Expression receiver, Map<String, SelectRef> selectVars) {
        Expression x = stripCasts(receiver)
        if (x instanceof VariableExpression && selectVars != null && selectVars.containsKey(((VariableExpression) x).name)) return selectVars.get(((VariableExpression) x).name)
        selectChainInfo(x)
    }

    /** The `select()` call inside `await …`, else null. Phase 275 — arguments are admitted, because
     *  GROOVY-12324's `select(boolean... enabled)` carries one precondition flag per offer; before it,
     *  any argument meant "not the shape we model" and the ALT was invisible to every pass. */
    private static MethodCallExpression awaitedSelectCall(Expression rhs) {
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
    private static Statement unrollLiteralChannelLoops(Statement body, Set<String> ch) {
        if (!(body instanceof BlockStatement) || ch.isEmpty()) return body
        boolean[] changed = [false]
        BlockStatement out = unrollBlock((BlockStatement) body, ch, changed, 0)
        changed[0] ? out : body
    }

    private static BlockStatement unrollBlock(BlockStatement b, Set<String> ch, boolean[] changed, int depth) {
        List<Statement> out = new ArrayList<Statement>()
        for (Statement st : b.statements) unrollInto(st, ch, changed, out, depth)
        BlockStatement nb = new BlockStatement(out, b.variableScope)
        nb.setSourcePosition(b); nb.copyNodeMetaData(b)
        nb
    }

    private static void unrollInto(Statement st, Set<String> ch, boolean[] changed, List<Statement> out, int depth) {
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
    private static Expression rebuildAsyncCall(Expression call, ClosureExpression cl, BlockStatement code) {
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
    private static boolean mentionsChannelOp(Statement s, Set<String> ch) {
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
    private static List<Statement> unrollLiteralLoop(ForStatement f, Set<String> ch) {
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
    private static Object[] literalLoopRange(ForStatement f) {
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

    private static Integer intLiteral(Expression e) {
        Expression x = stripCasts(e)
        if (x instanceof ConstantExpression && ((ConstantExpression) x).value instanceof Integer) return (Integer) ((ConstantExpression) x).value
        null
    }

    /** The loop-body shapes the stream unroller copies: blocks, expressions, returns, if/else — and
     *  nested `for` loops (a literal inner loop unrolls in turn; any other stays a loop, and its
     *  channel ops stay conditional — a loud skip, never a wrong count). */
    private static boolean unrollableStreamBody(Statement s) {
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
    private static boolean writesVar(Statement s, String name) {
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

    // ── Phase 240 — PAR disjointness: the fork-window interference check ────────────────────────
    //
    // The safe-value model for async arms (Phases 118/119/153–155) resolves an arm's captured reads
    // against the bindings in scope AT THE READ-OUT SITE — sound only under the "safe async closure"
    // discipline: nothing the arm touches is concurrently written. This check makes that side
    // condition real (the Hoare/CSL PAR rule's disjointness premise — slice 1 of the SEQ/PAR
    // ladder): between an arm's fork and its join, the enclosing body must not write anything the
    // arm reads or writes, must not read anything it writes, and two arms whose fork-join windows
    // overlap must have disjoint write-vs-touch sets. A violation is a genuine race — the arm may
    // observe either state — and ERRORS loudly rather than skipping: without it the engine proves
    // the post-write value (a stale-read race passes as a proof).
    //
    // The synchronisation media are exempt, exactly as channels are exempt in the CSP PAR rule:
    // DataflowVariable locals (write-once, reads block until the bind), AsyncChannel pipeline vars
    // (FIFO), and the Awaitable handles themselves. A declared interference discipline
    // (@Rely/@Guarantee/@UnderRely on the method or class) suppresses the check — that machinery
    // models interference deliberately.
    //
    // Boundaries (documented, not silent): the join is the first statement mentioning the arm's
    // handle after the fork (any use — an await, an orTimeout wrapper, a gather — counts); an arm
    // never mentioned again joins at end-of-body (conservative). Accesses are name-grained over the
    // outer universe (params, body locals, fields of the enclosing class); statics and foreign
    // receivers are out of scope, like the rest of the fragment. Effects hidden behind operators
    // (`sb << x` on a shared builder) are not writes here — those arms already fall out of the
    // value model elsewhere.

    private static class ParArm {
        int fork
        int join = Integer.MAX_VALUE
        int line
        boolean conditional        // forked inside an if-branch / loop — execution not guaranteed
        String handle              // the local the Awaitable is bound to, or null
        Expression anchor          // the async call (diagnostic anchor — an in-body expression)
        final Set<String> reads = new HashSet<String>()
        final Set<String> writes = new HashSet<String>()
    }

    private static class ParAccess {
        final int ord, line
        ParAccess(int ord, int line) { this.ord = ord; this.line = line }
    }

    // Phase 241 — a channel END use: who (main = null proc / an arm) touched which end of which
    // channel, where. Kinds: SEND (`send`/`close`), RECV (`first`/`receive`, or a pipeline
    // derivation consuming its source), SUB (`subscribe` on a broadcast).
    private static final int CHAN_SEND = 0, CHAN_RECV = 1, CHAN_SUB = 2
    private static class ChanUse {
        String chan; String method; int kind
        ParArm proc            // null = the main body
        int ord; int line
        int seq                // program-order position WITHIN its process (main: ord; arm: op counter)
        boolean conditional    // inside an if-branch / loop / catch — execution not guaranteed
        Expression anchor
        List<String> alts      // Phase 249 — an ALT node's channels (set on the group's representative)
    }

    private static class ParCtx {
        int counter
        int condDepth          // > 0 while walking statements whose execution is not guaranteed
        final Set<String> chanVars
        Map<String, SelectRef> selectRefs = new HashMap<String, SelectRef>()   // Phase 257 — held select instances
        final List<ParArm> arms = new ArrayList<ParArm>()
        final List<ChanUse> chanUses = new ArrayList<ChanUse>()
        // Phase 277 — barrier syncs are kept OUT of chanUses: a barrier is not a channel, and every
        // channel pass (linearity, FIFO pairing, streams) would have to special-case it. They join the
        // wait-for graph directly instead, which is the only pass that has anything to say about them.
        final List<ChanUse> barrierUses = new ArrayList<ChanUse>()
        final Map<String, Integer> phaserParties = new LinkedHashMap<String, Integer>()
        final Map<String, List<ParAccess>> mainWrites = new HashMap<String, List<ParAccess>>()
        final Map<String, List<ParAccess>> mainReads = new HashMap<String, List<ParAccess>>()
        ParCtx(Set<String> chanVars) { this.chanVars = chanVars }
        void write(String n, int ord, int line) { record(mainWrites, n, ord, line) }
        void read(String n, int ord, int line) {
            record(mainReads, n, ord, line)
            // The first mention of an arm's handle after its fork is its join (await/gather/wrapper).
            for (ParArm a : arms) if (n.equals(a.handle) && ord > a.fork && a.join == Integer.MAX_VALUE) a.join = ord
        }
        void barrierUse(String bar, String op, ParArm proc, int ord, int line, int seq, boolean conditional, Expression anchor) {
            ChanUse u = new ChanUse()
            u.chan = bar; u.method = op; u.kind = -1; u.proc = proc
            u.ord = ord; u.line = line; u.seq = seq; u.conditional = conditional; u.anchor = anchor
            barrierUses.add(u)
        }
        void chanUse(String chan, String method, int kind, ParArm proc, int ord, int line, int seq,
                     boolean conditional, Expression anchor) {
            ChanUse u = new ChanUse()
            u.chan = chan; u.method = method; u.kind = kind; u.proc = proc
            u.ord = ord; u.line = line; u.seq = seq; u.conditional = conditional; u.anchor = anchor
            chanUses.add(u)
        }
        private static void record(Map<String, List<ParAccess>> m, String n, int ord, int line) {
            List<ParAccess> l = m.get(n)
            if (l == null) { l = new ArrayList<ParAccess>(); m.put(n, l) }
            l.add(new ParAccess(ord, line))
        }
    }

    /** Phase 245 — the drain ops: consume the WHOLE stream, blocking until the channel is closed. */
    private static final List<String> CHANNEL_DRAIN_OPS = ['toList', 'each', 'collect'].asImmutable()

    /** Classify a channel end-use by method name: SEND, RECV, SUB, or -1 (neutral — isClosed etc.). */
    private static int chanUseKindOf(String method) {
        if (method == 'send' || method == 'close') return CHAN_SEND
        if (method == 'first' || method == 'receive') return CHAN_RECV
        if (method == 'subscribe') return CHAN_SUB
        if (method in CHANNEL_DRAIN_OPS) return CHAN_RECV    // Phase 245 — a drain is a (whole-stream) receive
        if (method in CHANNEL_PIPE_OPS) return CHAN_RECV     // map/filter/tap/merge/split consume their source
        -1
    }

    /** Phase 245 — a blocking-until-close consumption: a `for (v in ch)` (recorded as 'iterate') or a drain op. */
    private static boolean isIterateUse(ChanUse u) { u.method == 'iterate' || u.method in CHANNEL_DRAIN_OPS }

    /** Phase 249 — `ChannelSelect.from(c0, c1, …)`: a RECV-kind use ('select') of EVERY channel-var
     *  argument, all sharing the call as anchor (the network check groups them into one ALT node). */
    private static void recordSelectUsesIfAny(Expression call, ParCtx ctx, ParArm proc, int ord,
                                              int seq, boolean conditional) {
        // Phase 257 — the ALT's op is the select() CALL (inline chain or a held instance), so a held instance's
        // uses are recorded where the process blocks, not where the instance was declared.
        if (!(call instanceof MethodCallExpression) || ((MethodCallExpression) call).methodAsString != 'select' || !noArgs((MethodCallExpression) call)) return
        SelectRef ref = selectRefOf(((MethodCallExpression) call).objectExpression, ctx.selectRefs)
        if (ref == null) return
        for (Expression a : ref.chans) {
            Expression x = stripCasts(a)
            if (x instanceof VariableExpression && ctx.chanVars.contains(((VariableExpression) x).name)) {
                ctx.chanUse(((VariableExpression) x).name, 'select', CHAN_RECV, proc, ord, call.lineNumber, seq, conditional, call)
            }
        }
    }

    /** Record a channel end-use at a DIRECT channel-var receiver (a chain's base op has the var
     *  receiver, so a pipeline chain registers exactly one consumption of its source). */
    private static void recordChanUseIfAny(MethodCallExpression call, ParCtx ctx, ParArm proc, int ord,
                                           int seq, boolean conditional, Expression anchor) {
        Expression recv = stripCasts(call.objectExpression)
        if (!(recv instanceof VariableExpression)) return
        String name = ((VariableExpression) recv).name
        if (!ctx.chanVars.contains(name)) return
        int k = chanUseKindOf(call.methodAsString)
        if (k >= 0) ctx.chanUse(name, call.methodAsString, k, proc, ord, call.lineNumber, seq, conditional, anchor)
    }

    /** Phase 277 — a BARRIER sync at a phaser-var receiver. `java.util.concurrent.Phaser` is JCSP's
     *  `Barrier` under another name — `register()` is enroll, `arriveAndDeregister()` is resign, and
     *  `arriveAndAwaitAdvance()` is sync — so the books' barrier shapes port onto it with no new runtime
     *  primitive. This slice models STATIC enrollment only: a phaser constructed with a literal party
     *  count and synced by that many processes. */
    private static void recordBarrierUseIfAny(MethodCallExpression call, ParCtx ctx, ParArm proc, int ord,
                                              int seq, boolean conditional, Expression anchor) {
        Expression recv = stripCasts(call.objectExpression)
        if (!(recv instanceof VariableExpression)) return
        String name = ((VariableExpression) recv).name
        if (!ctx.phaserParties.containsKey(name)) return
        // Phase 278 — the enrolment ops join the syncs: `register()` is JCSP's enroll and
        // `arriveAndDeregister()` its resign, and c14's whole discipline is the order they come in.
        String m = call.methodAsString
        if (m == 'arriveAndAwaitAdvance' || m == 'register' || m == 'arriveAndDeregister') {
            ctx.barrierUse(name, m == 'arriveAndAwaitAdvance' ? 'sync' : m, proc, ord, call.lineNumber, seq, conditional, anchor)
        }
    }

    /** `new Phaser(n)` declarations: var name → the literal party count. A non-literal count, or any
     *  dynamic `register()` / `arriveAndDeregister()`, leaves the barrier out of the model (loudly). */
    private static void collectPhaserVars(BlockStatement body, Map<String, Integer> out) {
        body.visit(new CodeVisitorSupport() {
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (de.leftExpression instanceof VariableExpression) {
                    Expression r = stripCasts(de.rightExpression)
                    if (r instanceof ConstructorCallExpression &&
                        ((ConstructorCallExpression) r).type?.nameWithoutPackage == 'Phaser') {
                        Expression a = ((ConstructorCallExpression) r).arguments
                        List<Expression> args = (a instanceof TupleExpression) ? ((TupleExpression) a).expressions : null
                        if (args != null && args.size() == 1) {
                            Expression c = stripCasts(args.get(0))
                            if (c instanceof ConstantExpression && ((ConstantExpression) c).value instanceof Integer) {
                                out.put(((VariableExpression) de.leftExpression).name, (Integer) ((ConstantExpression) c).value)
                            }
                        }
                    }
                }
                super.visitDeclarationExpression(de)
            }
        })
    }

    /** Peel casts (STC/lowering wrappers) off an expression. */
    private static Expression stripCasts(Expression e) {
        Expression a = e
        while (a instanceof CastExpression) a = ((CastExpression) a).expression
        a
    }

    private static boolean isThisRef(Expression e) {
        e instanceof VariableExpression && ((VariableExpression) e).isThisExpression()
    }

    /** The root name a store targets: `v = …`/`v[i] = …` → v, `this.f = …` → f, else null. */
    private static String lhsRootName(Expression lhs) {
        Expression e = lhs
        while (true) {
            if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.LEFT_SQUARE_BRACKET) {
                e = ((BinaryExpression) e).leftExpression; continue
            }
            if (e instanceof CastExpression) { e = ((CastExpression) e).expression; continue }
            break
        }
        if (e instanceof VariableExpression) return ((VariableExpression) e).name
        if (e instanceof PropertyExpression && isThisRef(((PropertyExpression) e).objectExpression)) {
            return ((PropertyExpression) e).propertyAsString
        }
        null
    }

    /** Per-statement expression scan: records arms (async closures — not descended into as main
     *  code), main-body reads/writes at this statement's ordinal, and handle mentions (joins). */
    private static class ParScanner extends CodeVisitorSupport {
        final int ord
        final ParCtx ctx
        private int awaitDepth      // > 0 while inside an `await(...)` — an arm forked there joins in place
        ParScanner(int ord, ParCtx ctx) { this.ord = ord; this.ctx = ctx }

        @Override void visitMethodCallExpression(MethodCallExpression call) {
            ClosureExpression cl = asyncClosure(call)
            if (cl != null) { recordArm(call, cl, null); return }
            // Phase 241 — a main-body channel end-use (seq = the statement ordinal)
            recordChanUseIfAny(call, ctx, null, ord, ord, ctx.condDepth > 0, call)
            recordBarrierUseIfAny(call, ctx, null, ord, ord, ctx.condDepth > 0, call)
            recordSelectUsesIfAny(call, ctx, null, ord, ord, ctx.condDepth > 0)     // Phase 249
            boolean isAwait = call.methodAsString == 'await'
            if (isAwait) awaitDepth++
            try { super.visitMethodCallExpression(call) } finally { if (isAwait) awaitDepth-- }
        }

        @Override void visitStaticMethodCallExpression(StaticMethodCallExpression call) {
            ClosureExpression cl = asyncClosure(call)
            if (cl != null) { recordArm(call, cl, null); return }
            recordSelectUsesIfAny(call, ctx, null, ord, ord, ctx.condDepth > 0)     // Phase 249
            boolean isAwait = call.method == 'await'
            if (isAwait) awaitDepth++
            try { super.visitStaticMethodCallExpression(call) } finally { if (isAwait) awaitDepth-- }
        }

        @Override void visitDeclarationExpression(DeclarationExpression de) {
            Expression rhs = stripCasts(de.rightExpression)
            ClosureExpression cl = asyncClosure(rhs)
            if (cl != null && de.leftExpression instanceof VariableExpression) {
                recordArm(rhs, cl, ((VariableExpression) de.leftExpression).name)
                return
            }
            de.rightExpression?.visit(this)     // the LHS is a fresh binding, not a shared-state write
        }

        @Override void visitBinaryExpression(BinaryExpression be) {
            int t = be.operation.type
            if (t == Types.ASSIGN || Types.ofType(t, Types.ASSIGNMENT_OPERATOR)) {
                Expression rhs = stripCasts(be.rightExpression)
                ClosureExpression cl = (t == Types.ASSIGN) ? asyncClosure(rhs) : null
                if (cl != null && be.leftExpression instanceof VariableExpression) {
                    recordArm(rhs, cl, ((VariableExpression) be.leftExpression).name)
                    return
                }
                String root = lhsRootName(be.leftExpression)
                if (root != null) {
                    ctx.write(root, ord, be.lineNumber)
                    if (t != Types.ASSIGN) ctx.read(root, ord, be.lineNumber)     // compound also reads
                }
                if (be.leftExpression instanceof BinaryExpression) {              // a[i] = v — the index is read
                    ((BinaryExpression) be.leftExpression).rightExpression?.visit(this)
                }
                if (be.leftExpression instanceof PropertyExpression) {            // o.f = v — a non-this receiver is read
                    Expression o = ((PropertyExpression) be.leftExpression).objectExpression
                    if (!isThisRef(o)) o.visit(this)
                }
                be.rightExpression.visit(this)
                return
            }
            super.visitBinaryExpression(be)
        }

        @Override void visitPostfixExpression(PostfixExpression e) {
            String root = lhsRootName(e.expression)
            if (root != null) ctx.write(root, ord, e.lineNumber)
            super.visitPostfixExpression(e)
        }

        @Override void visitPrefixExpression(PrefixExpression e) {
            String root = lhsRootName(e.expression)
            if (root != null) ctx.write(root, ord, e.lineNumber)
            super.visitPrefixExpression(e)
        }

        @Override void visitVariableExpression(VariableExpression ve) { ctx.read(ve.name, ord, ve.lineNumber) }

        @Override void visitPropertyExpression(PropertyExpression pe) {
            if (isThisRef(pe.objectExpression)) ctx.read(pe.propertyAsString, ord, pe.lineNumber)
            else super.visitPropertyExpression(pe)
        }

        private void recordArm(Expression call, ClosureExpression cl, String handle) {
            ParArm a = new ParArm()
            a.fork = ord
            a.line = call.lineNumber
            a.conditional = ctx.condDepth > 0
            a.handle = handle
            a.anchor = call
            if (awaitDepth > 0) a.join = ord      // `await async { … }` — forked and joined in place
            ctx.arms.add(a)
            collectArmAccesses(cl, a.reads, a.writes, ctx, a)
        }
    }

    /** Collect an arm's captured accesses: outer names read/written inside the closure (closure
     *  params and closure-local declarations excluded; nested closures included as arm code) —
     *  plus its channel end-uses (Phase 241), recorded against the arm's fork-join window. */
    private static void collectArmAccesses(ClosureExpression cl, Set<String> reads, Set<String> writes,
                                           ParCtx ctx, ParArm arm) {
        final Set<String> local = new HashSet<String>()
        local.add('it')
        if (cl.parameters != null) for (Parameter p : cl.parameters) local.add(p.name)
        Statement code = cl.code
        if (code == null) return
        code.visit(new CodeVisitorSupport() {
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (de.leftExpression instanceof VariableExpression) {
                    local.add(((VariableExpression) de.leftExpression).name)
                } else if (de.leftExpression instanceof TupleExpression) {
                    for (Expression t : ((TupleExpression) de.leftExpression).expressions) {
                        if (t instanceof VariableExpression) local.add(((VariableExpression) t).name)
                    }
                }
                de.rightExpression?.visit(this)
            }
            @Override void visitBinaryExpression(BinaryExpression be) {
                int t = be.operation.type
                if (t == Types.ASSIGN || Types.ofType(t, Types.ASSIGNMENT_OPERATOR)) {
                    String root = lhsRootName(be.leftExpression)
                    if (root != null && !local.contains(root)) {
                        writes.add(root)
                        if (t != Types.ASSIGN) reads.add(root)
                    }
                    if (be.leftExpression instanceof BinaryExpression) {
                        ((BinaryExpression) be.leftExpression).rightExpression?.visit(this)
                    }
                    be.rightExpression.visit(this)
                    return
                }
                super.visitBinaryExpression(be)
            }
            @Override void visitPostfixExpression(PostfixExpression e) {
                String root = lhsRootName(e.expression)
                if (root != null && !local.contains(root)) writes.add(root)
                super.visitPostfixExpression(e)
            }
            @Override void visitPrefixExpression(PrefixExpression e) {
                String root = lhsRootName(e.expression)
                if (root != null && !local.contains(root)) writes.add(root)
                super.visitPrefixExpression(e)
            }
            private int armSeq = 0
            private int armCondDepth = 0
            @Override void visitMethodCallExpression(MethodCallExpression call) {
                // Phase 241 — an arm-side end-use; seq is the arm's own op order (Phase 243 needs it)
                int seq = ++armSeq
                recordChanUseIfAny(call, ctx, arm, arm.fork, seq, arm.conditional || armCondDepth > 0, call)
                recordBarrierUseIfAny(call, ctx, arm, arm.fork, seq, arm.conditional || armCondDepth > 0, call)
                recordSelectUsesIfAny(call, ctx, arm, arm.fork, seq, arm.conditional || armCondDepth > 0)   // Phase 249
                super.visitMethodCallExpression(call)
            }
            @Override void visitStaticMethodCallExpression(StaticMethodCallExpression call) {
                recordSelectUsesIfAny(call, ctx, arm, arm.fork, ++armSeq, arm.conditional || armCondDepth > 0)   // Phase 249
                super.visitStaticMethodCallExpression(call)
            }
            @Override void visitIfElse(IfStatement st) {
                st.booleanExpression.visit(this)
                armCondDepth++
                try { st.ifBlock?.visit(this); st.elseBlock?.visit(this) } finally { armCondDepth-- }
            }
            @Override void visitForLoop(ForStatement st) {
                // Phase 245 — an arm-side `for (v in ch)` is a whole-stream receive (blocks until close).
                Expression coll = stripCasts(st.collectionExpression)
                if (coll instanceof VariableExpression && ctx.chanVars.contains(((VariableExpression) coll).name)) {
                    ctx.chanUse(((VariableExpression) coll).name, 'iterate', CHAN_RECV, arm, arm.fork,
                        coll.lineNumber, ++armSeq, arm.conditional || armCondDepth > 0, arm.anchor)
                }
                st.collectionExpression?.visit(this)
                armCondDepth++
                try { st.loopBlock?.visit(this) } finally { armCondDepth-- }
            }
            @Override void visitWhileLoop(WhileStatement st) {
                st.booleanExpression.visit(this)
                armCondDepth++
                try { st.loopBlock?.visit(this) } finally { armCondDepth-- }
            }
            @Override void visitVariableExpression(VariableExpression ve) {
                if (!local.contains(ve.name)) reads.add(ve.name)
            }
            @Override void visitPropertyExpression(PropertyExpression pe) {
                if (isThisRef(pe.objectExpression)) reads.add(pe.propertyAsString)
                else super.visitPropertyExpression(pe)
            }
            @Override void visitClosureExpression(ClosureExpression c2) {
                if (c2.parameters != null) for (Parameter p : c2.parameters) local.add(p.name)
                super.visitClosureExpression(c2)
            }
        })
    }

    /** Method-body local declarations (closure interiors excluded) — part of the outer universe. */
    private static void collectBodyLocalNames(BlockStatement body, Set<String> out) {
        body.visit(new CodeVisitorSupport() {
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (de.leftExpression instanceof VariableExpression) {
                    out.add(((VariableExpression) de.leftExpression).name)
                } else if (de.leftExpression instanceof TupleExpression) {
                    for (Expression t : ((TupleExpression) de.leftExpression).expressions) {
                        if (t instanceof VariableExpression) out.add(((VariableExpression) t).name)
                    }
                }
                super.visitDeclarationExpression(de)
            }
            @Override void visitClosureExpression(ClosureExpression e) { }   // closure-locals are not outer names
        })
    }

    /** Ordinal walk: each statement gets a fresh ordinal; nested statements their own; whole
     *  subtrees of unhandled statement kinds scan coarsely at the enclosing ordinal. */
    private static void parWalkStatement(Statement st, ParCtx ctx) {
        if (st == null || st instanceof EmptyStatement) return
        if (st instanceof BlockStatement) {
            for (Statement s : ((BlockStatement) st).statements) parWalkStatement(s, ctx)
            return
        }
        int ord = ++ctx.counter
        if (st instanceof IfStatement) {
            IfStatement i = (IfStatement) st
            parScanExpr(i.booleanExpression, ord, ctx)
            ctx.condDepth++
            try { parWalkStatement(i.ifBlock, ctx); parWalkStatement(i.elseBlock, ctx) } finally { ctx.condDepth-- }
            return
        }
        if (st instanceof ForStatement) {
            ForStatement f = (ForStatement) st
            // Phase 245 — `for (v in ch)` is a whole-stream receive that blocks until close.
            Expression coll = stripCasts(f.collectionExpression)
            if (coll instanceof VariableExpression && ctx.chanVars.contains(((VariableExpression) coll).name)) {
                ctx.chanUse(((VariableExpression) coll).name, 'iterate', CHAN_RECV, null, ord,
                    coll.lineNumber, ord, ctx.condDepth > 0, coll)
            }
            parScanExpr(f.collectionExpression, ord, ctx)
            ctx.condDepth++
            try { parWalkStatement(f.loopBlock, ctx) } finally { ctx.condDepth-- }
            return
        }
        if (st instanceof WhileStatement) {
            WhileStatement w = (WhileStatement) st
            parScanExpr(w.booleanExpression, ord, ctx)
            ctx.condDepth++
            try { parWalkStatement(w.loopBlock, ctx) } finally { ctx.condDepth-- }
            return
        }
        if (st instanceof DoWhileStatement) {
            DoWhileStatement w = (DoWhileStatement) st
            ctx.condDepth++                                  // a do-while body RE-runs — not one-shot
            try { parWalkStatement(w.loopBlock, ctx) } finally { ctx.condDepth-- }
            parScanExpr(w.booleanExpression, ord, ctx)
            return
        }
        if (st instanceof org.codehaus.groovy.ast.stmt.TryCatchStatement) {
            org.codehaus.groovy.ast.stmt.TryCatchStatement t = (org.codehaus.groovy.ast.stmt.TryCatchStatement) st
            parWalkStatement(t.tryStatement, ctx)
            ctx.condDepth++
            try { for (org.codehaus.groovy.ast.stmt.CatchStatement c : t.catchStatements) parWalkStatement(c.code, ctx) }
            finally { ctx.condDepth-- }
            parWalkStatement(t.finallyStatement, ctx)
            return
        }
        st.visit(new ParScanner(ord, ctx))
    }

    private static void parScanExpr(Expression e, int ord, ParCtx ctx) {
        if (e != null) e.visit(new ParScanner(ord, ctx))
    }

    private static ParAccess firstInWindow(List<ParAccess> accesses, ParArm a) {
        if (accesses == null) return null
        for (ParAccess x : accesses) if (x.ord > a.fork && x.ord < a.join) return x
        null
    }

    /** A name {@code w} writes that {@code other} also touches (deterministic: sorted), else null. */
    private static String armConflict(ParArm w, ParArm other, Set<String> outer, Set<String> exempt) {
        List<String> ws = new ArrayList<String>(w.writes)
        Collections.sort(ws)
        for (String v : ws) {
            if (!outer.contains(v) || exempt.contains(v)) continue
            if (other.reads.contains(v) || other.writes.contains(v)) return v
        }
        null
    }

    /** Phase 266 — the method's `@DeliveredWithin(value, from, to)`, as [value, from, to], or null. */
    private static Object[] deliveredWithinOf(MethodNode node) {
        for (AnnotationNode a : node.getAnnotations()) {
            if (a.classNode?.nameWithoutPackage != 'DeliveredWithin') continue
            Expression v = a.getMember('value'), f = a.getMember('from'), t = a.getMember('to')
            if (v instanceof ConstantExpression && ((ConstantExpression) v).value instanceof Number &&
                f instanceof ConstantExpression && t instanceof ConstantExpression) {
                return [((Number) ((ConstantExpression) v).value).intValue(), String.valueOf(((ConstantExpression) f).value), String.valueOf(((ConstantExpression) t).value)] as Object[]
            }
        }
        null
    }

    /**
     * Phase 266 — the multi-hop service bound: hops from `from` to `to` through the scanned stages. A hop is a
     * consumer loop taking the incoming channel and producing the next: a plain stage costs 1 iteration; an ALT
     * branch costs its branch count under a held fair() (Phase 265's arithmetic) and is unbounded otherwise; a
     * guarded reply leaves on ITS branch's reply channel at the ALT's cost. Every simple path must meet the
     * bound (an element travels whichever exists), so the worst path decides; an unbounded hop refutes with its
     * own reason, and the claim is the SERVICE bound only — queueing is not claimed.
     */
    private void checkDeliveredWithin(MethodNode node, Object[] claim, StreamScan sc, Map<String, String> parent) {
        if (claim == null) return
        int bound = (int) claim[0]
        String from = (String) claim[1], to = (String) claim[2]
        Map<String, List<Object[]>> edges = new HashMap<String, List<Object[]>>()   // root → [next root, cost (-1 = unbounded), reason/label]
        for (ConsumerInfo ci : sc.consumers.values()) {
            Statement loop = (Statement) ci.loop
            List<StreamInfo> produced = new ArrayList<StreamInfo>()
            for (StreamInfo si : sc.streams.values()) if (si.loop.is(loop)) produced.add(si)
            if (produced.isEmpty()) continue
            int line = loop.lineNumber
            // plain receives: cost 1 to every non-conditional stream the stage produces
            for (String v : ci.receives.values()) {
                String root = sc.streamVarRoot(v, parent) ?: v
                for (StreamInfo si : produced) {
                    if (si.conditional) continue
                    addHop(edges, root, si.root, 1, "the stage at line ${line} (1)".toString())
                }
            }
            // ALT branches: the policy's cost, to non-conditional outputs and to the branch's OWN guarded reply
            if (ci.altVar != null) {
                int k = ci.altChans.size()
                String why = null
                if (!CLAIM_SELECT) why = "the racing select (before GROOVY-12320) re-sends losers — the hop at line ${line} has no bound".toString()
                else if (ci.altPolicy == 'priority') why = "the ALT at line ${line} selects by priority — no bound at all for a branch behind an always-ready one".toString()
                else if (ci.altPolicy == 'random') why = "the ALT at line ${line} selects with random() — fair in expectation only, no deterministic bound".toString()
                else if (ci.altPolicy == 'fair' && !ci.altHeld) why = "the ALT at line ${line} calls fair() on a fresh instance — no rotation state, no bound".toString()
                for (String c : ci.altChans) {
                    String root = sc.streamVarRoot(c, parent) ?: c
                    for (StreamInfo si : produced) {
                        if (si.conditional && si.condChan != c) continue          // a guarded reply leaves on its own branch's channel
                        addHop(edges, root, si.root, why == null ? k : -1, why == null ? "the held fair() ALT at line ${line} (${k})".toString() : why)
                    }
                }
            }
        }
        Set<String> known = new HashSet<String>()
        for (String r : edges.keySet()) known.add(r)
        for (List<Object[]> es : edges.values()) for (Object[] e : es) known.add((String) e[0])
        if (!known.contains(from) && !sc.streams.containsKey(from)) { addStaticTypeError(Reporter.formatDeliveredWithin(node.name, "'${from}' is not a channel a scanned stage consumes or produces"), node); return }
        // every simple path from → to
        List<Object[]> worst = [null]                                            // [total, label list] of the worst bounded path
        String[] unbounded = [null]
        boolean[] found = [false]
        deliverDfs(edges, from, to, new LinkedHashSet<String>(), 0, new ArrayList<String>(), worst, unbounded, found)
        if (unbounded[0] != null) { addStaticTypeError(Reporter.formatDeliveredWithin(node.name, unbounded[0]), node); return }
        if (!found[0]) { addStaticTypeError(Reporter.formatDeliveredWithin(node.name, "no path carries an element from '${from}' to '${to}' through the scanned stages"), node); return }
        Object[] w = (Object[]) worst[0]
        if (((int) w[0]) > bound) {
            addStaticTypeError(Reporter.formatDeliveredWithin(node.name,
                "the path ${from} -> ${((List<String>) w[1]).join(' -> ')} totals ${w[0]} service step(s) — the claimed ${bound} is below it"), node)
        }
    }

    private static void addHop(Map<String, List<Object[]>> edges, String from, String to, int cost, String label) {
        List<Object[]> l = edges.get(from)
        if (l == null) { l = new ArrayList<Object[]>(); edges.put(from, l) }
        for (Object[] e : l) if (e[0] == to) return
        l.add([to, cost, label] as Object[])
    }

    private static void deliverDfs(Map<String, List<Object[]>> edges, String at, String to, Set<String> onPath,
                                   int total, List<String> labels, List<Object[]> worst, String[] unbounded, boolean[] found) {
        if (at == to) {
            found[0] = true
            Object[] w = (Object[]) worst[0]
            if (w == null || total > (int) w[0]) worst[0] = [total, new ArrayList<String>(labels)] as Object[]
            return
        }
        if (!onPath.add(at)) return
        List<Object[]> es = edges.get(at)
        if (es != null) for (Object[] e : es) {
            if (unbounded[0] != null) break
            if (((int) e[1]) < 0) {
                // reachable unbounded hop on a path toward `to`: refute only if `to` is reachable beyond it
                if (reaches(edges, (String) e[0], to, new HashSet<String>())) { unbounded[0] = (String) e[2]; break }
                continue
            }
            labels.add("${e[2]} -> ${e[0]}".toString())
            deliverDfs(edges, (String) e[0], to, onPath, total + (int) e[1], labels, worst, unbounded, found)
            labels.remove(labels.size() - 1)
        }
        onPath.remove(at)
    }

    private static boolean reaches(Map<String, List<Object[]>> edges, String at, String to, Set<String> seen) {
        if (at == to) return true
        if (!seen.add(at)) return false
        List<Object[]> es = edges.get(at)
        if (es != null) for (Object[] e : es) if (reaches(edges, (String) e[0], to, seen)) return true
        false
    }

    /** Phase 265 — the method's `@ServedWithin(n)` bound, or null. */
    private static Integer servedWithinOf(MethodNode node) {
        for (AnnotationNode a : node.getAnnotations()) {
            if (a.classNode?.nameWithoutPackage != 'ServedWithin') continue
            Expression v = a.getMember('value')
            if (v instanceof ConstantExpression && ((ConstantExpression) v).value instanceof Number) return ((Number) ((ConstantExpression) v).value).intValue()
        }
        null
    }

    /**
     * Phase 265 — the @ServedWithin(n) claim, decided per ALT loop against the selection policy: certified
     * (silently, like any proved contract) only for a HELD fair() over k <= n branches on the claim-based
     * runtime; refuted with the policy's own reason otherwise. The loop's and the network's liveness are the
     * other rungs' verdicts on the same compile — the bound here is the selection's.
     */
    private void checkServedWithin(MethodNode node, Integer bound, StreamScan sc) {
        if (bound == null) return
        boolean anyAlt = false
        for (ConsumerInfo ci : sc.consumers.values()) {
            if (ci.altVar == null) continue
            anyAlt = true
            int k = ci.altChans.size()
            int line = ((Statement) ci.loop).lineNumber
            String why = null
            if (!CLAIM_SELECT) why = "the racing select (before GROOVY-12320) re-sends a losing branch's element to the back of its queue — no bound exists (the claim needs the claim-based select's held fair())"
            else if (ci.altPolicy == 'priority') why = "the ALT at line ${line} selects by priority — a branch behind an always-ready one may wait forever, so there is no bound at all (select with a held fair() instance for a bound of ${k})".toString()
            else if (ci.altPolicy == 'random') why = "the ALT at line ${line} selects with random() — fair in expectation only, no deterministic bound (select with a held fair() instance for a bound of ${k})".toString()
            else if (ci.altPolicy == 'fair' && !ci.altHeld) why = "the ALT at line ${line} calls fair() on a fresh instance each iteration, which keeps no rotation state — priority in effect, no bound (hoist the instance for a bound of ${k})".toString()
            else if (bound < k) why = "the ALT at line ${line} is a held fair() select over ${k} branches: the rotation may pass a ready branch ${k - 1} time(s), so the bound it gives is ${k} — the claimed ${bound} is below it".toString()
            if (why != null) addStaticTypeError(Reporter.formatServedWithin(node.name, why), (Statement) ci.loop)
        }
        if (!anyAlt) addStaticTypeError(Reporter.formatServedWithin(node.name, 'the method has no ALT loop for the claim to bound'), node)
    }

    /** Phase 263 — the method's `@Protocol` text, or null. */
    private static String protocolTextOf(MethodNode node) {
        for (AnnotationNode a : node.getAnnotations()) {
            if (a.classNode?.nameWithoutPackage != 'Protocol') continue
            // Phase 269 — the closure DSL arrives here already rendered: ContractExpansionTransform harvested
            // the closure pre-STC into the `text` member (the closure member is cleared to Void).
            Expression t = a.getMember('text')
            if (t instanceof ConstantExpression && ((ConstantExpression) t).value) return ((ConstantExpression) t).value.toString()
            Expression v = a.getMember('value')
            if (v instanceof ConstantExpression && ((ConstantExpression) v).value != null) return ((ConstantExpression) v).value.toString()
        }
        null
    }

    /** The Phase 240 entry point — see the section comment above. Runs on the ORIGINAL body,
     *  before the Phase 118/119 desugaring flattens the arms away. */
    private void checkParInterference(MethodNode node, Statement body) {
        if (!(body instanceof BlockStatement)) return
        if (methodOrClassHasAnnotation(node, 'UnderRely') || methodOrClassHasAnnotation(node, 'Rely') ||
            methodOrClassHasAnnotation(node, 'Guarantee')) return       // declared interference discipline
        // Channel vars are classified up front (Phase 241): the walk records end-uses against them,
        // and the created/derived/broadcast split drives the linearity rules below.
        Set<String> chanVars = new HashSet<String>()
        collectChannelVars((BlockStatement) body, chanVars)
        Set<String> createdChans = new HashSet<String>(), derivedChans = new HashSet<String>(),
                    broadcastChans = new HashSet<String>()
        Map<String, String> chanParent = new HashMap<String, String>()
        classifyChannelVars((BlockStatement) body, chanVars, createdChans, derivedChans, broadcastChans, chanParent)
        ParCtx ctx = new ParCtx(chanVars)
        ctx.selectRefs = collectSelectVars(body)                              // Phase 257
        collectPhaserVars((BlockStatement) body, ctx.phaserParties)           // Phase 277 — barriers
        parWalkStatement(body, ctx)
        String protocol = protocolTextOf(node)                                // Phase 263 — a session type for the network
        if (protocol != null) for (Object[] f : SessionChecker.check(node.name, protocol, (BlockStatement) body, chanVars, ARBITRATED_SELECT)) addStaticTypeError((String) f[0], (ASTNode) f[1])
        int chanFindings = checkChannelLinearity(node, ctx, (BlockStatement) body, derivedChans, broadcastChans)
        // Phase 243/245 — the network well-formedness check: runs unless a RACE-class finding
        // re-shaped the network's meaning (its own loud report stands). Model-limit skips only
        // refuse the VALUE rewrite — the blocking structure is still analysable (Phase 245), and
        // with multiple sends the single r→s edge under-detects but never over-claims.
        if (chanFindings < 2) {
            try {
                checkNetworkWellFormedness(node, ctx, (BlockStatement) body, chanParent, broadcastChans)
            } catch (Throwable ignored) {
            }
        }
        if (ctx.arms.isEmpty()) return

        // The synchronisation media, exempt from state conflicts (the "channels" of the PAR rule) —
        // their ENDS get their own discipline in checkChannelLinearity above.
        Set<String> exempt = new HashSet<String>()
        collectDataflowVars((BlockStatement) body, exempt)
        exempt.addAll(chanVars)
        for (ParArm a : ctx.arms) if (a.handle != null) exempt.add(a.handle)

        // The outer universe accesses are resolved against: params, body locals, fields.
        Set<String> outer = new HashSet<String>()
        for (Parameter p : node.parameters) outer.add(p.name)
        collectBodyLocalNames((BlockStatement) body, outer)
        if (node.declaringClass != null) for (FieldNode f : node.declaringClass.fields) outer.add(f.name)

        Set<String> reported = new HashSet<String>()
        for (ParArm a : ctx.arms) {
            Set<String> touched = new TreeSet<String>(a.reads)
            touched.addAll(a.writes)
            touched.retainAll(outer)
            touched.removeAll(exempt)
            for (String v : touched) {
                ParAccess w = firstInWindow(ctx.mainWrites.get(v), a)
                if (w != null && reported.add(a.line + ':' + v)) {
                    addStaticTypeError(Reporter.formatParInterference(node.name, v,
                        "the async task forked at line ${a.line} captures '${v}', which the body writes " +
                        "at line ${w.line} before the task's join"), a.anchor)
                }
            }
            Set<String> armWrites = new TreeSet<String>(a.writes)
            armWrites.retainAll(outer)
            armWrites.removeAll(exempt)
            for (String v : armWrites) {
                ParAccess r = firstInWindow(ctx.mainReads.get(v), a)
                if (r != null && reported.add(a.line + ':' + v)) {
                    addStaticTypeError(Reporter.formatParInterference(node.name, v,
                        "the async task forked at line ${a.line} writes '${v}', which the body reads " +
                        "at line ${r.line} before the task's join"), a.anchor)
                }
            }
        }
        for (int i = 0; i < ctx.arms.size(); i++) {
            for (int j = i + 1; j < ctx.arms.size(); j++) {
                ParArm a = ctx.arms.get(i), b = ctx.arms.get(j)
                if (a.fork > b.join || b.fork > a.join) continue     // sequential: one joined before the other forked
                String v = armConflict(a, b, outer, exempt)
                if (v == null) v = armConflict(b, a, outer, exempt)
                if (v != null && reported.add(a.line + '&' + b.line + ':' + v)) {
                    addStaticTypeError(Reporter.formatParInterference(node.name, v,
                        "concurrent async tasks forked at lines ${a.line} and ${b.line} conflict on " +
                        "'${v}' (a write in one, a read or write in the other)"), b.anchor)
                }
            }
        }
    }

    /** Split the channel vars by provenance (Phase 241): created (`AsyncChannel.create`), broadcast
     *  (`BroadcastChannel.create`), derived (a pipeline op or `subscribe` on a channel expr) — the
     *  derived var's base channel recorded in {@code parent} (Phase 243 resolves reads to roots). */
    private static void classifyChannelVars(BlockStatement body, Set<String> ch, Set<String> created,
                                            Set<String> derived, Set<String> broadcast,
                                            Map<String, String> parent) {
        body.visit(new CodeVisitorSupport() {
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (de.leftExpression instanceof VariableExpression) {
                    String n = ((VariableExpression) de.leftExpression).name
                    if (isChannelCreate(de.rightExpression)) created.add(n)
                    else if (isBroadcastCreate(de.rightExpression)) broadcast.add(n)
                    else if (isChannelExpr(de.rightExpression, ch)) {
                        derived.add(n)
                        String base = chanRoot(de.rightExpression, ch)
                        if (base != null && base != n) parent.put(n, base)
                    }
                }
                super.visitDeclarationExpression(de)
            }
        })
    }

    /** Neither both-main (sequential by definition) nor the same arm. */
    private static boolean distinctProcs(ChanUse a, ChanUse b) {
        if (a.proc == null && b.proc == null) return false
        if (a.proc != null && b.proc != null && a.proc.is(b.proc)) return false
        true
    }

    /** Do the two uses' windows overlap? A main use is the point [ord, ord] and must fall strictly
     *  inside the arm's fork-join window; two arms overlap on their windows (slice-1 convention). */
    private static boolean usesConcurrent(ChanUse a, ChanUse b) {
        if (a.proc == null) return b.proc != null && b.proc.fork < a.ord && a.ord < b.proc.join
        if (b.proc == null) return a.proc.fork < b.ord && b.ord < a.proc.join
        a.proc.fork <= b.proc.join && b.proc.fork <= a.proc.join
    }

    private static String procDesc(ChanUse u) {
        u.proc == null ? "the enclosing body (line ${u.line})" : "the async task forked at line ${u.proc.line}"
    }

    private static Set<String> paramNames(MethodNode node) {
        Set<String> out = new HashSet<String>()
        for (Parameter p : node.parameters) out.add(p.name)
        out
    }

    /** The declaration of a channel local (`def ch = AsyncChannel.create(..)` / a derived stage), or null. */
    private static Expression chanDeclAnchor(BlockStatement body, String chan) {
        final Expression[] found = [null]
        body.visit(new CodeVisitorSupport() {
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (found[0] == null && de.leftExpression instanceof VariableExpression &&
                    ((VariableExpression) de.leftExpression).name == chan) found[0] = de
                super.visitDeclarationExpression(de)
            }
        })
        found[0]
    }

    private static Expression anchorFor(List<ChanUse> uses, String chan) {
        for (ChanUse u : uses) if (u.chan == chan) return u.anchor
        null
    }

    /**
     * Phase 241 — channel-end linearity over the recorded uses (slice 2 of the SEQ/PAR ladder).
     * Concurrent same-end users ERROR — that is a race in the code: two live senders interleave
     * nondeterministically, two live receivers split the stream. A send into a pipeline-derived
     * channel ERRORS (its upstream stage owns that end), and a `subscribe` inside a live sender's
     * window ERRORS (a late subscriber may miss elements). Sequential over-use of the one-element
     * model — a second send or a second consumer by the same process — is NOT a race but is beyond
     * the scalar rewrite, so it SKIPS loudly here with the channel named (and desugarChannels'
     * guard independently refuses the rewrite, so nothing downstream can prove a FIFO-false value).
     */
    private int checkChannelLinearity(MethodNode node, ParCtx ctx, BlockStatement body,
                                      Set<String> derivedChans, Set<String> broadcastChans) {
        List<ChanUse> uses = ctx.chanUses
        if (uses.isEmpty()) return 0
        Set<String> flagged = new HashSet<String>()          // per-channel per-rule dedupe
        Set<String> erroredChans = new HashSet<String>()     // channels with a concurrency error
        for (int i = 0; i < uses.size(); i++) {
            for (int j = i + 1; j < uses.size(); j++) {
                ChanUse a = uses.get(i), b = uses.get(j)
                if (a.chan != b.chan || !distinctProcs(a, b) || !usesConcurrent(a, b)) continue
                if (a.kind == CHAN_SEND && b.kind == CHAN_SEND && flagged.add(a.chan + ':ss')) {
                    erroredChans.add(a.chan)
                    addStaticTypeError(Reporter.formatChannelLinearity(node.name, a.chan,
                        "two concurrent senders on '${a.chan}' — ${procDesc(a)} and ${procDesc(b)} " +
                        "both use its send-end, so the element order is a race"), b.anchor)
                } else if (a.kind == CHAN_RECV && b.kind == CHAN_RECV && !broadcastChans.contains(a.chan) &&
                           flagged.add(a.chan + ':rr')) {
                    erroredChans.add(a.chan)
                    addStaticTypeError(Reporter.formatChannelLinearity(node.name, a.chan,
                        "two concurrent receivers on '${a.chan}' — ${procDesc(a)} and ${procDesc(b)} " +
                        "both consume it, and each element is delivered to only one of them"), b.anchor)
                } else if (((a.kind == CHAN_SUB && b.kind == CHAN_SEND) || (a.kind == CHAN_SEND && b.kind == CHAN_SUB)) &&
                           flagged.add(a.chan + ':sub')) {
                    erroredChans.add(a.chan)
                    ChanUse sub = a.kind == CHAN_SUB ? a : b
                    ChanUse snd = a.kind == CHAN_SUB ? b : a
                    addStaticTypeError(Reporter.formatChannelLinearity(node.name, a.chan,
                        "${procDesc(sub)} subscribes to '${a.chan}' while a sender " +
                        "(${procDesc(snd)}) is live — a late subscriber may miss elements; " +
                        "subscribe before any sender starts"), sub.anchor)
                }
            }
        }
        // A derived channel's send-end belongs to the stage that produces it.
        for (ChanUse u : uses) {
            if (u.kind == CHAN_SEND && derivedChans.contains(u.chan) && flagged.add(u.chan + ':derived')) {
                erroredChans.add(u.chan)
                addStaticTypeError(Reporter.formatChannelLinearity(node.name, u.chan,
                    "'${u.chan}' is a pipeline-derived channel — its upstream stage is its producer, " +
                    "but ${procDesc(u)} uses its send-end"), u.anchor)
            }
        }
        // Phase 247 — beyond the bounded-FIFO model (conditional traffic, an end shared by two
        // processes, two consumer families, an inexact drain): name the channel and the reason
        // instead of a bare skip. The same verdicts make desugarChannels refuse the rewrite.
        // Anchored at the channel's DECLARATION: STC dedups errors per source position, and the
        // Phase 243 network skip may anchor at the very same conditional op (Phase 244's finding).
        // Phase 262 — the verdicts see the body as the rewrite will: a partner's drain already rebuilt as its counter loop
        BlockStatement modelBody = desugarPartnerDrains(body, ctx.chanVars, paramNames(node))
        for (Map.Entry<String, String> e : channelModelVerdicts(modelBody, ctx.chanVars, paramNames(node), currentScalarTypes).entrySet()) {
            if (!erroredChans.contains(e.key) && flagged.add(e.key + ':model')) {
                Expression anchor = chanDeclAnchor(body, e.key)
                if (anchor == null) anchor = anchorFor(uses, e.key)
                addStaticTypeError(Reporter.formatChannelModelSkipped(node.name, e.key, e.value),
                    anchor != null ? anchor : (ASTNode) node)
            }
        }
        // 2 = race-class findings (they re-shape the network's meaning: the structural analysis
        // must not run); 1 = model-limit skips only (value model refused, structure still analysable);
        // 0 = clean.
        !erroredChans.isEmpty() ? 2 : (!flagged.isEmpty() ? 1 : 0)
    }

    // ── Phase 242 — channel contracts: the element type is the protocol invariant ───────────────
    //
    // A channel's element type may carry Bean Validation bounds (TYPE_USE, the Phase 145
    // vocabulary): `AsyncChannel<@PositiveOrZero Integer>`. That is the channel's CONTRACT —
    // "every value sent satisfies φ" — the monitor-invariant reduction transplanted to channels
    // (slice 3 of the SEQ/PAR ladder): φ is CHECKED at each send (an `assert` at the send site,
    // discharged by the existing assert machinery with a counterexample) and ASSUMED at each
    // receive from an OPAQUE channel — a channel-typed parameter, whose producer lives in another
    // method and is checked by its own compilation. That is the compositional rule: producer and
    // consumer verify separately against the type, no whole-network analysis. An unconstrained
    // param channel still binds a fresh (unconstrained) receive value, so a postcondition stronger
    // than the contract honestly REFUTES instead of skipping.
    //
    // Fragment: int/long elements; numeric bounds (@Positive/@PositiveOrZero/@Negative/
    // @NegativeOrZero/@Min/@Max — @NotNull is a supported no-op for an int element). Any other
    // jakarta constraint on a channel element skips loudly: neither checked nor assumed.

    /** Constrained channels (params + locals): name → bounds, for send-site asserts. */
    private Map<String, List<long[]>> currentChannelBounds = Collections.emptyMap()
    /** Channel-typed params with an int/long element: name → bounds (maybe empty), for receive-binds. */
    private Map<String, List<long[]>> currentChannelRecvParams = Collections.emptyMap()
    /** Every channel-valued name in the method (params by declared type + locals by construction),
     *  regardless of element type — for exempting channels from collection-shaped obligations. */
    private Set<String> currentChannelNames = Collections.emptySet()
    /** Phase 245 — the LOCAL subset of {@link #currentChannelNames} (constructed via create()/
     *  subscribe()/pipeline ops — factory results, never null, so no deref obligation; a channel
     *  PARAM stays out: it can be null, and @NotNull is its honest discharge). */
    private Set<String> currentChannelLocalNames = Collections.emptySet()
    /** Phase 257 — locals holding a `ChannelSelect.from(..)` chain (a factory result, never null). */
    private Set<String> currentHeldSelectLocalNames = Collections.emptySet()
    /** Phase 277 — locals initialised by a `new …`: a constructor returns an object or throws, never null.
     *  Generalises the channel-factory and held-select exemptions above; without it any ordinary
     *  `StringBuilder sb = new StringBuilder(); sb.append(…)` carried an undischargeable deref obligation. */
    private Set<String> currentNewLocalNames = Collections.emptySet()

    // Bound op codes (shared with Encoder.tryBindChannelReceive by value): ge / gt / le / lt.
    private static final long CB_GE = 0L, CB_GT = 1L, CB_LE = 2L, CB_LT = 3L

    private void collectChannelContracts(MethodNode node) {
        Map<String, List<long[]>> bounds = new HashMap<String, List<long[]>>()
        Map<String, List<long[]>> recvParams = new HashMap<String, List<long[]>>()
        Set<String> names = new HashSet<String>()
        for (Parameter p : node.parameters) {
            String tn = p.type?.nameWithoutPackage
            if (tn == 'AsyncChannel' || tn == 'BroadcastChannel') names.add(p.name)
            List<long[]> b = channelElementBounds(p.type, p.name, node)
            if (b == null) continue
            recvParams.put(p.name, b)
            if (!b.isEmpty()) bounds.put(p.name, b)
        }
        Set<String> localNames = new HashSet<String>()
        if (node.code instanceof BlockStatement) collectChannelVars((BlockStatement) node.code, localNames)
        names.addAll(localNames)
        currentChannelNames = names
        currentChannelLocalNames = localNames
        currentHeldSelectLocalNames = collectSelectVars(node.code).keySet()          // Phase 257
        currentNewLocalNames = collectNewLocalNames(node.code)                       // Phase 277
        if (node.code != null) {
            node.code.visit(new CodeVisitorSupport() {
                @Override void visitDeclarationExpression(DeclarationExpression de) {
                    if (de.leftExpression instanceof VariableExpression) {
                        VariableExpression ve = (VariableExpression) de.leftExpression
                        // A `def` / `var` / `val` channel local carries no declared generics: the element type
                        // is the factory call's explicit type witness — `val ch = AsyncChannel.<String>create(1)`
                        // — which is also what lets STC type the channel (this harvest runs before STC has
                        // stamped inferred types, so the witness in the AST is the only source).
                        ClassNode declared = ve.getOriginType()
                        if (declared == null || ClassHelper.isDynamicTyped(declared) || ClassHelper.OBJECT_TYPE.equals(declared)) {
                            ClassNode w = witnessedChannelType(de.rightExpression)
                            if (w != null) declared = w
                        }
                        List<long[]> b = channelElementBounds(declared, ve.name, node)
                        if (b != null && !b.isEmpty()) bounds.put(ve.name, b)
                        // Phase 246 — a channel LOCAL's scalar shadow (the desugared `def ch = v`)
                        // takes the channel's ELEMENT type, so a String-element channel's value
                        // proves in the string theory instead of colliding with the Int default.
                        ClassNode elem = channelElementType(declared)
                        if (elem != null && isNonIntScalar(elem) && !currentScalarTypes.containsKey(ve.name)) {
                            currentScalarTypes.put(ve.name, elem)
                        }
                    }
                    super.visitDeclarationExpression(de)
                }
            })
        }
        currentChannelBounds = bounds
        currentChannelRecvParams = recvParams
    }

    /** The element type of an {@code AsyncChannel<T>} / {@code BroadcastChannel<T>} type, else null. */
    /** `AsyncChannel.<T>create(..)` / `BroadcastChannel.<T>create()` → the channel type with T as its element
     *  generic (from the call's explicit type arguments); null when there is no witness. */
    private static ClassNode witnessedChannelType(Expression rhs) {
        Expression e = stripCasts(rhs)
        GenericsType[] gts = null
        String owner = null
        if (e instanceof MethodCallExpression) {          // the pre-STC shape (a static call carries no witness)
            MethodCallExpression m = (MethodCallExpression) e
            if (m.methodAsString == 'create') { gts = m.genericsTypes; owner = channelOwnerName(m.objectExpression) }
        }
        if (gts == null || gts.length != 1 || gts[0].type == null || owner == null) return null
        if (owner != 'AsyncChannel' && owner != 'BroadcastChannel') return null
        ClassNode base = ClassHelper.make('groovy.concurrent.' + owner)
        GenericsUtils.makeClassSafeWithGenerics(base, new GenericsType(gts[0].type))
    }

    private static ClassNode channelElementType(ClassNode t) {
        if (t == null) return null
        String cn = t.nameWithoutPackage
        if (cn != 'AsyncChannel' && cn != 'BroadcastChannel') return null
        GenericsType[] gts = t.genericsTypes
        (gts != null && gts.length > 0) ? gts[0].type : null
    }

    /** The element bounds of a channel-typed declaration, or null when it isn't an int/long-element
     *  channel. Unsupported jakarta constraints on the element skip loudly, per constraint. */
    private List<long[]> channelElementBounds(ClassNode t, String name, MethodNode node) {
        if (t == null) return null
        String cn = t.nameWithoutPackage
        if (cn != 'AsyncChannel' && cn != 'BroadcastChannel') return null
        GenericsType[] gts = t.genericsTypes
        if (gts == null || gts.length == 0 || gts[0].type == null) return null
        ClassNode elem = gts[0].type
        if (!isJvmInt(elem) && !isJvmLong(elem)) return null
        List<long[]> out = new ArrayList<long[]>()
        List<AnnotationNode> anns = new ArrayList<AnnotationNode>()
        if (elem.annotations != null) anns.addAll(elem.annotations)
        if (elem.typeAnnotations != null) anns.addAll(elem.typeAnnotations)
        for (AnnotationNode a : anns) {
            String fqn = a.classNode?.name
            if (fqn == null ||
                !(fqn.startsWith('jakarta.validation.constraints.') || fqn.startsWith('javax.validation.constraints.'))) {
                continue
            }
            switch (a.classNode.nameWithoutPackage) {
                case 'Positive':       out.add([CB_GT, 0L] as long[]); break
                case 'PositiveOrZero': out.add([CB_GE, 0L] as long[]); break
                case 'Negative':       out.add([CB_LT, 0L] as long[]); break
                case 'NegativeOrZero': out.add([CB_LE, 0L] as long[]); break
                case 'Min':            { Long n = longMember(a); if (n != null) out.add([CB_GE, n.longValue()] as long[]); break }
                case 'Max':            { Long n = longMember(a); if (n != null) out.add([CB_LE, n.longValue()] as long[]); break }
                case 'NotNull':        break        // supported no-op: an int-element value is never null
                default:
                    addStaticTypeError(Reporter.formatChannelConstraintSkipped(node.name, name,
                        '@' + a.classNode.nameWithoutPackage), node)
            }
        }
        out
    }

    /** The conjunction of a channel's bounds over {@code subject}, as an `assert` the existing
     *  assert machinery discharges (with a counterexample on refutation) at the send site. */
    private static Statement boundsAssert(Expression subject, List<long[]> bounds, ASTNode pos) {
        Expression conj = null
        for (long[] b : bounds) {
            int tok
            if (b[0] == CB_GE) tok = Types.COMPARE_GREATER_THAN_EQUAL
            else if (b[0] == CB_GT) tok = Types.COMPARE_GREATER_THAN
            else if (b[0] == CB_LE) tok = Types.COMPARE_LESS_THAN_EQUAL
            else tok = Types.COMPARE_LESS_THAN
            long n = b[1]
            Expression lit = new ConstantExpression(
                (n >= Integer.MIN_VALUE && n <= Integer.MAX_VALUE) ? (Object) Integer.valueOf((int) n)
                                                                   : (Object) Long.valueOf(n))
            Expression cmp = bin(subject, tok, lit)
            cmp.setSourcePosition(pos)
            conj = conj == null ? cmp : bin(conj, Types.LOGICAL_AND, cmp)
        }
        conj.setSourcePosition(pos)
        AssertStatement st = new AssertStatement(new BooleanExpression(conj))
        st.setSourcePosition(pos)
        st
    }

    /** Phase 242 — a statement-position `ch.send(e)` (or `await ch.send(e)`) on a CONSTRAINED
     *  channel PARAM becomes `assert φ(e)`: the send's contract obligation, checked here in the
     *  producer while delivery stays the assumed structural half. (An unconstrained param send
     *  keeps today's loud-skip path; local channels get their assert inside the Phase 119
     *  rewrite, where the send also binds the representative element.) */
    private Statement desugarParamChannelSends(Statement body) {
        if (!(body instanceof BlockStatement) || currentChannelBounds.isEmpty()) return body
        Set<String> paramChans = new HashSet<String>(currentChannelRecvParams.keySet())
        paramChans.retainAll(currentChannelBounds.keySet())
        if (paramChans.isEmpty()) return body
        boolean[] changed = [false] as boolean[]
        List<Statement> out = rewriteParamSends(((BlockStatement) body).statements, paramChans, changed)
        changed[0] ? new BlockStatement(out, ((BlockStatement) body).variableScope) : body
    }

    private List<Statement> rewriteParamSends(List<Statement> stmts, Set<String> paramChans, boolean[] changed) {
        List<Statement> out = new ArrayList<Statement>()
        for (Statement st : stmts) {
            if (st instanceof BlockStatement) {
                out.add(new BlockStatement(
                    rewriteParamSends(((BlockStatement) st).statements, paramChans, changed),
                    ((BlockStatement) st).variableScope))
                continue
            }
            if (st instanceof ExpressionStatement) {
                Expression e = stripCasts(((ExpressionStatement) st).expression)
                // `await ch.send(v)` — unwrap to the send (completion assumed, as for orTimeout)
                if (e instanceof MethodCallExpression && ((MethodCallExpression) e).methodAsString == 'await') {
                    List<Expression> aw = argListOf((MethodCallExpression) e)
                    if (aw != null && aw.size() == 1) e = stripCasts(aw.get(0))
                } else if (e instanceof StaticMethodCallExpression && ((StaticMethodCallExpression) e).method == 'await' &&
                           ((StaticMethodCallExpression) e).arguments instanceof ArgumentListExpression) {
                    List<Expression> aw = ((ArgumentListExpression) ((StaticMethodCallExpression) e).arguments).expressions
                    if (aw.size() == 1) e = stripCasts(aw.get(0))
                }
                if (e instanceof MethodCallExpression) {
                    MethodCallExpression m = (MethodCallExpression) e
                    Expression recv = stripCasts(m.objectExpression)
                    if (m.methodAsString == 'send' && recv instanceof VariableExpression &&
                        paramChans.contains(((VariableExpression) recv).name)) {
                        List<Expression> a = argListOf(m)
                        if (a != null && a.size() == 1) {
                            out.add(boundsAssert(a.get(0),
                                currentChannelBounds.get(((VariableExpression) recv).name), m))
                            changed[0] = true
                            continue
                        }
                    }
                }
            }
            out.add(st)
        }
        out
    }

    private static List<Expression> argListOf(MethodCallExpression m) {
        (m.arguments instanceof ArgumentListExpression) ? ((ArgumentListExpression) m.arguments).expressions : null
    }

    // ── Phase 243 — network well-formedness: deadlock-freedom as well-foundedness ───────────────
    //
    // With the ends linear (Phase 241) and one element in flight per channel, a method's channel
    // network is a tiny, EXACT dependency system. The blocking operations are receives (`first` /
    // awaited `receive`) and joins (`await t`); a statement-position send discards its Awaitable
    // and does not block. So: a blocking read completes only after its root channel's send has
    // executed; an op executes only after its process passes its earlier blocking points (an arm's
    // ops additionally need main to reach the fork — i.e. main's blocking points before it); a
    // join completes only when the whole arm has. The network is deadlock-free EXACTLY when this
    // wait-for order is well-founded — the same argument as @Decreases and the dining-philosophers
    // resource hierarchy, in its fourth appearance. A cycle is a guaranteed deadlock (error, with
    // the circular wait spelled out); a blocking read whose root channel is never sent to can
    // never be satisfied (error). The certificate covers exactly what it says: every op
    // unconditional (an op inside an if/loop/catch → loud skip), channels local and non-escaping
    // (a channel passed out or received as a parameter may be served elsewhere — the modular
    // assumption, silent), the one-element model enforced upstream.

    /** Channel names that ESCAPE the method: appear anywhere other than as a method-call receiver
     *  or their own declaration LHS (a call argument, a return value, an alias, a field store). */
    private static Set<String> collectEscapingChannels(BlockStatement body, Set<String> chanNames) {
        if (chanNames.isEmpty()) return Collections.emptySet()
        final Set<Expression> sanctioned = Collections.newSetFromMap(new IdentityHashMap<Expression, Boolean>())
        body.visit(new CodeVisitorSupport() {
            private void sanctionSelect(Expression call) {           // Phase 249 — an ALT consumes its channels in place
                List<Expression> args = selectFromArgs(call)
                if (args != null) for (Expression a : args) { Expression x = stripCasts(a); if (x instanceof VariableExpression) sanctioned.add(x) }
            }
            @Override void visitMethodCallExpression(MethodCallExpression m) {
                Expression recv = stripCasts(m.objectExpression)
                if (recv instanceof VariableExpression) sanctioned.add(recv)
                sanctionSelect(m)
                super.visitMethodCallExpression(m)
            }
            @Override void visitStaticMethodCallExpression(StaticMethodCallExpression m) {
                sanctionSelect(m)
                super.visitStaticMethodCallExpression(m)
            }
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (de.leftExpression instanceof VariableExpression) sanctioned.add(de.leftExpression)
                de.rightExpression?.visit(this)
            }
            @Override void visitForLoop(ForStatement st) {
                // Phase 245 — `for (v in ch)` consumes the channel in place; it is not an escape.
                Expression coll = stripCasts(st.collectionExpression)
                if (coll instanceof VariableExpression) sanctioned.add(coll)
                super.visitForLoop(st)
            }
        })
        final Set<String> escaping = new HashSet<String>()
        body.visit(new CodeVisitorSupport() {
            @Override void visitVariableExpression(VariableExpression ve) {
                if (chanNames.contains(ve.name) && !sanctioned.contains(ve)) escaping.add(ve.name)
            }
        })
        escaping
    }

    /** Follow the derivation chain to the base channel: {@code out → src}, {@code s1 → b}. */
    private static String chanBaseOf(String c, Map<String, String> parent) {
        String r = c
        int guard = 0
        while (parent.containsKey(r) && guard++ < 100) r = parent.get(r)
        r
    }

    private static String describeChanEvent(Object ev) {
        if (ev instanceof ParArm) return "the await of the task forked at line ${((ParArm) ev).line}"
        ChanUse u = (ChanUse) ev
        String who = u.proc == null ? '' : " in the task forked at line ${u.proc.line}"
        if (u.alts != null) return "the ALT over ${u.alts.collect { "'" + it + "'" }.join(', ')} (line ${u.line}${who})"
        String what = u.method == 'send' ? 'the send on' :
                      u.method == 'close' ? 'the close of' :
                      isIterateUse(u) ? 'the iteration over' : 'the receive on'
        "${what} '${u.chan}' (line ${u.line}${who})"
    }

    /** The Phase 243 entry point — see the section comment above. Runs only when the linearity
     *  pass was silent, so the one-sender/one-receiver/one-element discipline holds. */
    /** Phase 277 — locals whose declaration initialiser is a constructor call, anywhere in the body. A
     *  later re-assignment from something nullable would make this unsound, so a name assigned anywhere
     *  else in the method is excluded. */
    private static Set<String> collectNewLocalNames(Statement code) {
        if (code == null) return Collections.emptySet()
        final Set<String> news = new LinkedHashSet<String>(), reassigned = new HashSet<String>()
        code.visit(new CodeVisitorSupport() {
            @Override void visitDeclarationExpression(DeclarationExpression de) {
                if (de.leftExpression instanceof VariableExpression &&
                    stripCasts(de.rightExpression) instanceof ConstructorCallExpression) {
                    news.add(((VariableExpression) de.leftExpression).name)
                }
                super.visitDeclarationExpression(de)
            }
            @Override void visitBinaryExpression(BinaryExpression be) {
                if (Types.ofType(be.operation.type, Types.ASSIGNMENT_OPERATOR) &&
                    !(be instanceof DeclarationExpression) && be.leftExpression instanceof VariableExpression) {
                    reassigned.add(((VariableExpression) be.leftExpression).name)
                }
                super.visitBinaryExpression(be)
            }
        })
        news.removeAll(reassigned)
        news
    }

    /**
     * Phase 277 — the barrier certificate, standing on its own. Two checks, in order:
     * <ol>
     *   <li>ENROLMENT: a barrier releases when every party it was constructed for has arrived, so if fewer
     *       processes sync on it than that, it never advances and everyone who did arrive waits forever.</li>
     *   <li>WELL-FOUNDEDNESS: the same theorem the channel network rests on. A round — the j-th sync of
     *       every party — is ONE synchronisation, so its members inherit the round's program-order
     *       predecessors and none waits on another (which would make every barrier its own cycle). A real
     *       knot then closes through some other event: two barriers synced in opposite orders.</li>
     * </ol>
     * Returns true when it reported, so the caller stops rather than re-reporting through the channel path.
     */
    private boolean checkBarriers(MethodNode node, ParCtx ctx) {
        // Phase 278 — the enrolment DISCIPLINE, which holds whether or not the count is static: a process
        // that has resigned its party has none to arrive with, so a later sync (or a second resign) is an
        // error the runtime raises. Tracked per process in program order — a process is assumed enrolled
        // to begin with (it is one of the parties the barrier was constructed for), register() re-enrols
        // it, arriveAndDeregister() gives the party up. This is exactly c14's enroll/resign pairing.
        Map<String, Boolean> enrolled = new HashMap<String, Boolean>()
        List<ChanUse> inOrder = new ArrayList<ChanUse>(ctx.barrierUses)
        inOrder.sort { ChanUse a, ChanUse b -> a.proc.is(b.proc) ? (a.seq <=> b.seq) : (a.ord <=> b.ord) }
        for (ChanUse u : inOrder) {
            if (u.conditional) continue                          // not guaranteed to run: no claim either way
            String key = u.chan + '@' + (u.proc == null ? 'main' : System.identityHashCode(u.proc))
            boolean on = enrolled.containsKey(key) ? enrolled.get(key) : true
            if (u.method == 'register') { enrolled.put(key, true); continue }
            if (!on) {
                addStaticTypeError(Reporter.formatBarrierResigned(node.name, u.chan, u.method, u.line), u.anchor)
                return true
            }
            if (u.method == 'arriveAndDeregister') enrolled.put(key, false)
        }
        Set<String> dyn = dynamicBarriers(ctx)
        for (Map.Entry<String, Integer> e : ctx.phaserParties.entrySet()) {
            if (dyn.contains(e.key)) continue                    // Phase 278 — the count is a runtime value
            Set<Object> procs = new HashSet<Object>()
            ChanUse first = null
            for (ChanUse u : barrierSyncs(ctx)) if (u.chan == e.key) {
                procs.add(u.proc == null ? 'main' : u.proc)
                if (first == null) first = u
            }
            if (first == null) continue                          // declared but never synced
            if (procs.size() < e.value) {
                addStaticTypeError(Reporter.formatBarrierParties(node.name, e.key, e.value, procs.size()), first.anchor)
                return true
            }
        }
        // Phase 278 — with enrolment moving at runtime the party set of a round is not static, so neither
        // the count nor deadlock-freedom is claimed for such a barrier. Said out loud, once, per barrier.
        for (String bar : dyn) {
            ChanUse at = null
            for (ChanUse u : ctx.barrierUses) if (u.chan == bar && u.method != 'sync') { at = u; break }
            if (at != null) addStaticTypeError(Reporter.formatBarrierDynamic(node.name, bar), at.anchor)
        }
        if (!dyn.isEmpty()) return true
        List<ChanUse> evs = new ArrayList<ChanUse>(barrierSyncs(ctx))
        Map<ChanUse, Integer> id = new IdentityHashMap<ChanUse, Integer>()
        for (int i = 0; i < evs.size(); i++) id.put(evs.get(i), i)
        List<List<Integer>> adj = new ArrayList<List<Integer>>()
        for (int i = 0; i < evs.size(); i++) adj.add(new ArrayList<Integer>())
        for (ChanUse u : evs) {                                   // program order within each process
            for (ChanUse b : evs) {
                if (b.is(u)) continue
                boolean sameProc = (u.proc == null && b.proc == null) || (u.proc != null && b.proc != null && b.proc.is(u.proc))
                if (sameProc && b.seq < u.seq) adj.get(id.get(u)).add(id.get(b))
            }
        }
        Map<Integer, List<Integer>> merged = new HashMap<Integer, List<Integer>>()
        for (List<ChanUse> round : barrierRounds(ctx)) {
            List<Integer> ids = new ArrayList<Integer>()
            for (ChanUse u : round) { Integer i = id.get(u); if (i != null) ids.add(i) }
            if (ids.size() < 2) continue
            List<Integer> u = new ArrayList<Integer>()
            for (Integer i : ids) for (Integer x : adj.get(i)) if (!ids.contains(x) && !u.contains(x)) u.add(x)
            for (Integer i : ids) merged.put(i, new ArrayList<Integer>(u))
        }
        for (Map.Entry<Integer, List<Integer>> e : merged.entrySet()) adj.set(e.key, e.value)
        List<Integer> cycle = findWaitCycle(adj, new int[evs.size()], new ArrayList<Integer>())
        if (cycle == null) return false
        List<String> parts = new ArrayList<String>()
        for (Integer i : cycle) {
            ChanUse u = evs.get(i)
            parts.add("the sync on '${u.chan}' (line ${u.line}${u.proc == null ? '' : " in the task forked at line ${u.proc.line}"})".toString())
        }
        addStaticTypeError(Reporter.formatBarrierDeadlock(node.name,
            'circular wait: ' + parts.join(', which waits for ') + ', which waits for the first'), evs.get(cycle.get(0)).anchor)
        true
    }

    /** Phase 278 — the SYNCS among the barrier ops (the list also carries register / arriveAndDeregister). */
    private static List<ChanUse> barrierSyncs(ParCtx ctx) {
        List<ChanUse> out = new ArrayList<ChanUse>()
        for (ChanUse u : ctx.barrierUses) if (u.method == 'sync') out.add(u)
        out
    }

    /** Phase 278 — barriers whose enrolment changes at runtime: their party count is not the constructor's,
     *  so neither the count check nor the round structure applies to them. */
    private static Set<String> dynamicBarriers(ParCtx ctx) {
        Set<String> out = new LinkedHashSet<String>()
        for (ChanUse u : ctx.barrierUses) if (u.method != 'sync') out.add(u.chan)
        out
    }

    /** Phase 277 — the barrier rounds of a method: for each phaser, the j-th sync of every process that
     *  syncs it. With static enrollment each process arrives once per round, so grouping by ordinal is
     *  exactly the round structure — the same "j-th receive pairs with the j-th send" idea the channel
     *  model uses, lifted from two parties to n. */
    private static List<List<ChanUse>> barrierRounds(ParCtx ctx) {
        List<List<ChanUse>> out = new ArrayList<List<ChanUse>>()
        Set<String> dynamic = dynamicBarriers(ctx)
        for (String bar : ctx.phaserParties.keySet()) {
            if (dynamic.contains(bar)) continue                  // Phase 278 — no static round structure
            Map<Object, List<ChanUse>> byProc = new LinkedHashMap<Object, List<ChanUse>>()
            for (ChanUse u : barrierSyncs(ctx)) {
                if (u.chan != bar) continue
                Object k = u.proc == null ? 'main' : u.proc
                List<ChanUse> l = byProc.get(k)
                if (l == null) { l = new ArrayList<ChanUse>(); byProc.put(k, l) }
                l.add(u)
            }
            if (byProc.size() < 2) continue
            for (List<ChanUse> l : byProc.values()) l.sort { ChanUse a, ChanUse b -> a.seq <=> b.seq }
            int rounds = Integer.MAX_VALUE
            for (List<ChanUse> l : byProc.values()) rounds = Math.min(rounds, l.size())
            for (int j = 0; j < rounds; j++) {
                List<ChanUse> round = new ArrayList<ChanUse>()
                for (List<ChanUse> l : byProc.values()) round.add(l.get(j))
                out.add(round)
            }
        }
        out
    }

    private void checkNetworkWellFormedness(MethodNode node, ParCtx ctx, BlockStatement body,
                                            Map<String, String> chanParent, Set<String> broadcastChans) {
        List<ChanUse> uses = ctx.chanUses
        // Phase 277 — barriers first: the enrolment check needs nothing else, and a network of barriers
        // and nothing else (two processes and a Phaser is already deadlockable) never reaches the channel
        // machinery below, whose every path is about sends and receives.
        if (!ctx.barrierUses.isEmpty()) {
            if (checkBarriers(node, ctx)) return
        }
        if (uses.isEmpty()) return
        // Phase 252 — a consumer loop's sanctioned receives are decided by the value model (the element-exists
        // obligation under the producer's summary), not by the wait-for graph: they leave it here.
        Set<Expression> sanctionedReceives = Collections.newSetFromMap(new IdentityHashMap<Expression, Boolean>())
        Map<String, StreamInfo> infiniteProducers = new HashMap<String, StreamInfo>()
        Map<String, String> loopLiveness = new HashMap<String, String>()     // Phase 255 — root → why its liveness is undecided
        guardedReplyOf.clear()                                              // Phase 256 — per method
        try {
            Map<String, String> parent = new HashMap<String, String>()
            Set<String> subscribers = new HashSet<String>()
            collectChannelParents(body, ctx.chanVars, parent, subscribers)
            BlockStatement modelBody = desugarPartnerDrains(body, ctx.chanVars, paramNames(node))   // Phase 262 — as the rewrite sees it
            StreamScan sc = scanStreams(modelBody, ctx.chanVars, parent, subscribers, paramNames(node), currentScalarTypes)
            checkServedWithin(node, servedWithinOf(node), sc)                 // Phase 265 — the quantitative bound claim
            checkDeliveredWithin(node, deliveredWithinOf(node), sc, parent)   // Phase 266 — the multi-hop service bound
            sanctionedReceives.addAll(sc.sanctionedReceives)
            sanctionedReceives.addAll(sc.sanctionedFroms)                     // Phase 253 — a looping ALT's from() call is its anchor
            for (StreamInfo p : sc.streams.values()) if (p.infinite) infiniteProducers.put(p.root, p)   // Phase 254
            loopLiveness = analyseLoopLiveness(node, modelBody, sc, parent)  // Phase 255 — liveness under weak fairness
        } catch (Throwable ignored) {
        }
        Set<String> livenessNoted = new HashSet<String>()
        Set<String> paramChans = new HashSet<String>()
        for (Parameter p : node.parameters) {
            String tn = p.type?.nameWithoutPackage
            if (tn == 'AsyncChannel' || tn == 'BroadcastChannel') paramChans.add(p.name)
        }
        Set<String> escaping = collectEscapingChannels(body, ctx.chanVars)

        List<ChanUse> blockingReads = new ArrayList<ChanUse>()   // single-element receives (first / awaited receive)
        List<ChanUse> iterates = new ArrayList<ChanUse>()        // Phase 245 — whole-stream receives (block until close)
        List<ChanUse> selects = new ArrayList<ChanUse>()         // Phase 249 — ALT nodes (one representative per from() call)
        Map<Expression, ChanUse> selectByAnchor = new IdentityHashMap<Expression, ChanUse>()
        List<ChanUse> sends = new ArrayList<ChanUse>()
        List<ChanUse> closes = new ArrayList<ChanUse>()
        Map<String, List<ChanUse>> sendsByRoot = new HashMap<String, List<ChanUse>>()   // Phase 247 — in FIFO order
        Map<String, ChanUse> closeByRoot = new HashMap<String, ChanUse>()
        Set<String> selectedChans = new HashSet<String>()
        Map<String, ChanUse> unknownCount = new HashMap<String, ChanUse>()   // Phase 250 — roots with a loop / if send
        ChanUse condUse = null
        for (ChanUse u : uses) {
            String root = chanBaseOf(u.chan, chanParent)
            if (paramChans.contains(root) || escaping.contains(root) || escaping.contains(u.chan)) continue
            boolean isSend = u.method == 'send'
            boolean isClose = u.method == 'close'
            boolean isRead = u.method == 'first' || u.method == 'receive'
            boolean isIter = isIterateUse(u)
            boolean isSelect = u.method == 'select'
            if (!isSend && !isClose && !isRead && !isIter && !isSelect) continue
            if ((isRead || isSelect) && sanctionedReceives.contains(u.anchor)) {           // Phase 252/253
                // Phase 256/257/258 — a reply guarded by an ALT's choice (now a conditional stream, so the read is
                // sanctioned): its liveness is the selection policy's business — withheld with the policy's reason,
                // or certified for a held fair() when the request precedes the wait.
                Object[] g = isRead ? guardedReplyOf.get(root) : null
                if (g != null) {
                    String why = guardedReplyReason(g)
                    if (why != null) {
                        addStaticTypeError(Reporter.formatNetworkSkipped(node.name,
                            "the receive on '${u.chan}' (line ${u.line}) is served only when the ALT in the loop at line ${g[0]} " +
                            "takes branch ${g[1]} — " + why), u.anchor)
                        return
                    }
                    if (!requestPrecedes(u, g, uses, chanParent)) {
                        addStaticTypeError(Reporter.formatNetworkSkipped(node.name,
                            "the receive on '${u.chan}' (line ${u.line}) is served by the reply the ALT in the loop at line ${g[0]} " +
                            "guards (branch ${g[1]}), but this process sends no request on a branch of that ALT before it — " +
                            "the request must precede the wait; per-client liveness is not certified"), u.anchor)
                        return
                    }
                    continue
                }
                // Phase 254 — served by a non-terminating producer: that it IS served is liveness, not claimed.
                StreamInfo p = infiniteProducers.get(root)
                // Phase 255 — the note stands only where the loop-liveness analysis could not certify the root
                if (p != null && loopLiveness.containsKey(root) && livenessNoted.add(root)) {
                    addStaticTypeError(Reporter.formatNetworkSkipped(node.name,
                        "the ${isSelect ? 'ALT' : 'receive'} on '${u.chan}' (line ${u.line}) is served by a non-terminating producer " +
                        "(the while (true) at line ${((Statement) p.loop).lineNumber}) — that it is eventually served is a liveness " +
                        "property, not certified here (${loopLiveness.get(root)}); the safety of the values received is certified " +
                        "under that assumption"), u.anchor)
                }
                continue
            }
            if (u.conditional || (u.proc != null && u.proc.conditional)) {
                // Phase 250 — a conditional SEND (inside a loop / if / catch) never blocks and stalls
                // nobody: it only makes its root's element COUNT non-static. It leaves the graph, and
                // the root is remembered — a blocking receive on it cannot be paired with a send
                // (uncertifiable, named below), while an iteration, which waits for the CLOSE, is
                // unaffected: a symbolic-count producer loop plus an unconditional close certifies
                // its drain. Every other conditional op still voids the certificate.
                if (isSend) { if (!unknownCount.containsKey(root)) unknownCount.put(root, u); continue }
                // Phase 257 — a client's looping receive on a reply guarded by a HELD fair() select: every ready
                // branch is taken within n calls and the request precedes the wait, so the reply is served once
                // the server loop is live — certified with it (analyseLoopLiveness); any other policy is named below.
                if (isRead) {
                    Object[] g = guardedReplyOf.get(root)
                    if (g != null && guardedReplyReason(g) == null) {
                        if (requestPrecedes(u, g, uses, chanParent)) continue
                        addStaticTypeError(Reporter.formatNetworkSkipped(node.name,
                            "the receive on '${u.chan}' (line ${u.line}) is served by the reply the ALT in the loop at line ${g[0]} " +
                            "guards (branch ${g[1]}), but this process sends no request on a branch of that ALT before it — " +
                            "the request must precede the wait; per-client liveness is not certified"), u.anchor)
                        return
                    }
                }
                condUse = u; continue
            }
            if (isSend) {
                sends.add(u)
                List<ChanUse> l = sendsByRoot.get(root)
                if (l == null) { l = new ArrayList<ChanUse>(); sendsByRoot.put(root, l) }
                l.add(u)
            }
            else if (isClose) { closes.add(u); if (!closeByRoot.containsKey(root)) closeByRoot.put(root, u) }
            else if (isIter) iterates.add(u)
            else if (isSelect) {
                // One node per ALT: the first recorded channel use represents it, carrying the branch list.
                ChanUse rep = selectByAnchor.get(u.anchor)
                if (rep == null) { rep = u; rep.alts = new ArrayList<String>(); selectByAnchor.put(u.anchor, rep); selects.add(rep) }
                rep.alts.add(u.chan)
                selectedChans.add(u.chan)
            }
            else blockingReads.add(u)
        }
        if (condUse != null) {
            Object[] guarded = guardedReplyOf.get(chanBaseOf(condUse.chan, chanParent))   // Phase 256 — a client of a selecting server
            if (guarded != null && (condUse.method == 'first' || condUse.method == 'receive')) {
                String why = guardedReplyReason(guarded)
                if (why != null) {
                    addStaticTypeError(Reporter.formatNetworkSkipped(node.name,
                        "the receive on '${condUse.chan}' (line ${condUse.line}) is served only when the ALT in the loop at line ${guarded[0]} " +
                        "takes branch ${guarded[1]} — " + why), condUse.anchor)
                    return
                }
                // Phase 257 — a held fair() select: every ready branch is taken within n calls, the request is
                // sent before the wait, so the reply arrives once the server loop is live: certified with it.
            }
            addStaticTypeError(Reporter.formatNetworkSkipped(node.name,
                "the channel operation on '${condUse.chan}' (line ${condUse.line}) is conditional " +
                "(inside an if / loop / catch)"), condUse.anchor)
            return
        }
        // Phase 249 — a one-shot ALT must be the LAST receive on each of its channels: a later receive
        // on a selected channel is satisfied by the j-th or the (j+1)-th send depending on the choice,
        // which the graph cannot represent — uncertifiable, loudly.
        if (!selectedChans.isEmpty()) {
            List<ChanUse> later = new ArrayList<ChanUse>(blockingReads)
            later.addAll(iterates)
            for (ChanUse r : later) {
                if (selectedChans.contains(r.chan)) {
                    addStaticTypeError(Reporter.formatNetworkSkipped(node.name,
                        "the receive on '${r.chan}' (line ${r.line}) follows an ALT over it — whether the ALT " +
                        "consumed the element depends on its choice (a one-shot ALT must be the last receive on " +
                        "each of its channels)"), r.anchor)
                    return
                }
            }
            for (int i = 0; i < selects.size(); i++) for (int j = i + 1; j < selects.size(); j++) {
                for (String c : selects.get(i).alts) if (selects.get(j).alts.contains(c)) {
                    addStaticTypeError(Reporter.formatNetworkSkipped(node.name,
                        "two ALTs (lines ${selects.get(i).line} and ${selects.get(j).line}) both select over '${c}' — " +
                        "the second's readiness depends on the first's choice"), selects.get(j).anchor)
                    return
                }
            }
        }
        List<ChanUse> blockers = new ArrayList<ChanUse>(blockingReads)   // ops a process stalls at
        blockers.addAll(iterates)
        blockers.addAll(selects)
        if (blockers.isEmpty()) return               // nothing blocks → nothing to certify

        // A read whose root channel is never sent to can never be satisfied; an iteration over a
        // root that is never CLOSED can never finish (Phase 245 — the forgotten-close hang).
        // Phase 247 — FIFO pairing: the j-th receive on a stream is satisfied by the j-th send on its
        // root (uses are recorded in program order, and a race-free network's receives on one stream
        // are sequential), so a receive past the last send can never be satisfied either.
        Map<String, Integer> readOrdinal = new HashMap<String, Integer>()
        Map<ChanUse, ChanUse> pairedSend = new IdentityHashMap<ChanUse, ChanUse>()
        for (ChanUse r : blockingReads) {
            String root = chanBaseOf(r.chan, chanParent)
            List<ChanUse> ss = sendsByRoot.get(root)
            Integer seen = readOrdinal.get(r.chan)
            int j = (seen == null ? 0 : seen) + 1
            readOrdinal.put(r.chan, j)
            String where = root == r.chan ? "'${root}'" : "its source channel '${root}'"
            ChanUse loopSend = unknownCount.get(root)
            if (loopSend != null) {                                  // Phase 250 — count not static: no pairing
                Object[] guarded = guardedReplyOf.get(root)          // Phase 256 — the fair-server reply: withheld, with the runtime's reason
                if (guarded != null) {
                    String why = guardedReplyReason(guarded)
                    if (why != null) {
                        addStaticTypeError(Reporter.formatNetworkSkipped(node.name,
                            "the receive on '${r.chan}' (line ${r.line}) is served only when the ALT in the loop at line ${guarded[0]} " +
                            "takes branch ${guarded[1]} — " + why), r.anchor)
                        return
                    }
                    continue                                          // Phase 257 — held fair(): certified with the server loop
                }
                addStaticTypeError(Reporter.formatNetworkSkipped(node.name,
                    "the receive on '${r.chan}' (line ${r.line}) is served by a send inside a loop / if (line " +
                    "${loopSend.line}) — the element count of " + where + " is not static, so the receive cannot " +
                    "be paired with a send (a drain — for-in / toList — waits for the close instead and is certifiable)"), r.anchor)
                return
            }
            if (ss == null) {
                addStaticTypeError(Reporter.formatNetworkDeadlock(node.name,
                    "the receive on '${r.chan}' (line ${r.line}) can never be satisfied — no send on " +
                    where + " anywhere in the method"), r.anchor)
                return
            }
            if (j > ss.size()) {
                addStaticTypeError(Reporter.formatNetworkDeadlock(node.name,
                    "the ${ordinalWord(j)} receive on '${r.chan}' (line ${r.line}) can never be satisfied — only " +
                    "${ss.size()} send${ss.size() == 1 ? '' : 's'} on " + where + " anywhere in the method"), r.anchor)
                return
            }
            pairedSend.put(r, ss.get(j - 1))
        }
        // Phase 272 — RENDEZVOUS channels (`AsyncChannel.create(0)`, JCSP's plain one2one). Everywhere else
        // the certificate rests on "a send never blocks" (buffered: queued, the Awaitable discarded), so a
        // send is a graph node nothing waits behind. At capacity 0 that is false — the send completes only
        // when its receive does — and the send-send cycle it makes possible is the deadlock the books teach
        // first (a producer and a consumer that both write before they read). So on a rendezvous channel a
        // send becomes a blocking event too, waiting for the receive that will take its element.
        Set<String> chanNames = new HashSet<String>()
        for (ChanUse u : uses) { chanNames.add(u.chan); chanNames.add(chanBaseOf(u.chan, chanParent)) }
        Set<String> rendezvousRoots = SessionChecker.rendezvousChans(body, chanNames)
        Map<ChanUse, ChanUse> pairedReceive = new IdentityHashMap<ChanUse, ChanUse>()
        List<ChanUse> rvSends = new ArrayList<ChanUse>()
        for (Map.Entry<ChanUse, ChanUse> e : pairedSend.entrySet()) {
            ChanUse snd = e.value
            if (snd == null || !rendezvousRoots.contains(chanBaseOf(snd.chan, chanParent))) continue
            if (!pairedReceive.containsKey(snd)) { pairedReceive.put(snd, e.key); rvSends.add(snd) }
        }
        for (ChanUse it : iterates) {
            String root = chanBaseOf(it.chan, chanParent)
            StreamInfo forever = infiniteProducers.get(root)
            if (!closeByRoot.containsKey(root) && forever != null) {
                // Phase 262 — a drain of a `while (true)` producer's stream never finishes by design: a
                // non-terminating drain, not a deadlock — said, and the certificate withheld rather than claimed.
                addStaticTypeError(Reporter.formatNetworkSkipped(node.name,
                    "the iteration over '${it.chan}' (line ${it.line}) never finishes — its producer is a while (true) " +
                    "(line ${((Statement) forever.loop).lineNumber}) that never closes it: a non-terminating drain (the values it " +
                    "drains are certified under that; no deadlock is claimed)"), it.anchor)
                return
            }
            if (!closeByRoot.containsKey(root)) {
                addStaticTypeError(Reporter.formatNetworkDeadlock(node.name,
                    "the iteration over '${it.chan}' (line ${it.line}) can never finish — no close() on " +
                    (root == it.chan ? "'${root}'" : "its source channel '${root}'") +
                    " anywhere in the method"), it.anchor)
                return
            }
        }
        // Phase 249 — an ALT's alternatives: for each branch, the send that would satisfy its next
        // receive (the ALT is the last receive on the branch, so that is the (j+1)-th send). A branch
        // with no send left is never ready; an ALT with no ready branch at all can never be satisfied.
        Map<ChanUse, List<ChanUse>> selectAlts = new IdentityHashMap<ChanUse, List<ChanUse>>()
        for (ChanUse sel : selects) {
            List<ChanUse> alts = new ArrayList<ChanUse>()
            for (String c : sel.alts) {
                ChanUse loopSend = unknownCount.get(chanBaseOf(c, chanParent))
                if (loopSend != null) {                              // Phase 250 — a branch with a non-static count
                    addStaticTypeError(Reporter.formatNetworkSkipped(node.name,
                        describeChanEvent(sel) + " has a branch ('${c}') served by a send inside a loop / if (line " +
                        "${loopSend.line}) — its readiness is not static"), sel.anchor)
                    return
                }
                List<ChanUse> ss = sendsByRoot.get(chanBaseOf(c, chanParent))
                Integer seen = readOrdinal.get(c)
                int j = (seen == null ? 0 : seen) + 1
                if (ss != null && j <= ss.size()) alts.add(ss.get(j - 1))
            }
            if (alts.isEmpty()) {
                addStaticTypeError(Reporter.formatNetworkDeadlock(node.name,
                    describeChanEvent(sel) + " can never be satisfied — no send left on any of its channels"), sel.anchor)
                return
            }
            selectAlts.put(sel, alts)
        }

        // The wait-for graph: nodes are the channel ops (reads, iterations, ALTs, sends, closes) plus
        // each awaited arm's join.
        List<Object> evs = new ArrayList<Object>()
        Map<Object, Integer> id = new IdentityHashMap<Object, Integer>()
        List<ChanUse> evUses = new ArrayList<ChanUse>(blockers)
        evUses.addAll(sends)
        evUses.addAll(closes)
        evUses.addAll(barrierSyncs(ctx))                                     // Phase 277 — barrier syncs
        for (ChanUse u : evUses) { id.put(u, evs.size()); evs.add(u) }
        List<ParArm> joined = new ArrayList<ParArm>()
        for (ParArm a : ctx.arms) if (a.join != Integer.MAX_VALUE) { joined.add(a); id.put(a, evs.size()); evs.add(a) }
        List<List<Integer>> adj = new ArrayList<List<Integer>>()
        for (int i = 0; i < evs.size(); i++) adj.add(new ArrayList<Integer>())
        Map<Integer, List<Integer>> orAlts = new HashMap<Integer, List<Integer>>()   // Phase 249 — an ALT completes if ANY alternative does

        // Main's blocking points before ordinal o: its blockers and the joins it has passed.
        // (X → Y means "X cannot complete until Y has".)
        // Phase 272 — a rendezvous send blocks, so it joins the blockers for program-order purposes: an
        // operation later in the same process cannot run until that send has been taken.
        List<ChanUse> ordered = new ArrayList<ChanUse>(blockers)
        ordered.addAll(rvSends)
        ordered.addAll(barrierSyncs(ctx))                                    // Phase 277 — a sync blocks too
        for (ChanUse u : evUses) {
            if (u.proc == null) {
                for (ChanUse b : ordered) if (b.proc == null && b.ord < u.ord) adj.get(id.get(u)).add(id.get(b))
                for (ParArm a : joined) if (a.join < u.ord) adj.get(id.get(u)).add(id.get(a))
            } else {
                for (ChanUse b : ordered) if (b.proc != null && b.proc.is(u.proc) && b.seq < u.seq) adj.get(id.get(u)).add(id.get(b))
                for (ChanUse b : ordered) if (b.proc == null && b.ord < u.proc.fork) adj.get(id.get(u)).add(id.get(b))
                for (ParArm a : joined) if (a.join < u.proc.fork) adj.get(id.get(u)).add(id.get(a))
            }
        }
        for (ChanUse r : blockingReads) {                       // the j-th receive waits for the j-th send
            ChanUse s = pairedSend.get(r)
            if (s != null && !s.is(r) && !pairedReceive.containsKey(s)) adj.get(id.get(r)).add(id.get(s))
        }
        // Phase 272 — a rendezvous send and its receive are ONE synchronisation, not two events waiting on
        // each other (that would make every matched pair a two-cycle, and every rendezvous a "deadlock").
        // They complete together, so each waits for exactly what the other waits for: the union of the two
        // program-order predecessor sets, with no edge between them. A real cycle then has to close through
        // some OTHER event — which is precisely the send-send knot when both processes write before reading.
        List<int[]> rvPairs = new ArrayList<int[]>()
        for (ChanUse snd : rvSends) {
            ChanUse r = pairedReceive.get(snd)
            if (r != null && !r.is(snd)) rvPairs.add(new int[] { id.get(snd), id.get(r) })
        }
        Map<Integer, List<Integer>> merged = new HashMap<Integer, List<Integer>>()
        for (int[] pr : rvPairs) {
            List<Integer> u = new ArrayList<Integer>()
            for (Integer x : adj.get(pr[0])) if (x != pr[0] && x != pr[1] && !u.contains(x)) u.add(x)
            for (Integer x : adj.get(pr[1])) if (x != pr[0] && x != pr[1] && !u.contains(x)) u.add(x)
            merged.put(pr[0], u); merged.put(pr[1], new ArrayList<Integer>(u))
        }
        // Phase 277 — a barrier ROUND is the same coalescing, n-way: every party's j-th sync completes
        // exactly when all of them do, so each inherits the union of the round's program-order
        // predecessors and none waits on another (which would make every barrier its own cycle). A knot
        // then has to close through some other event — two barriers synced in opposite orders, say.
        for (List<ChanUse> round : barrierRounds(ctx)) {
            List<Integer> ids = new ArrayList<Integer>()
            for (ChanUse u : round) { Integer i = id.get(u); if (i != null) ids.add(i) }
            if (ids.size() < 2) continue
            List<Integer> u = new ArrayList<Integer>()
            for (Integer i : ids) for (Integer x : adj.get(i)) if (!ids.contains(x) && !u.contains(x)) u.add(x)
            for (Integer i : ids) merged.put(i, new ArrayList<Integer>(u))
        }
        for (Map.Entry<Integer, List<Integer>> e : merged.entrySet()) adj.set(e.key, e.value)
        for (ChanUse it : iterates) {                            // Phase 245 — an iteration finishes at close
            ChanUse c = closeByRoot.get(chanBaseOf(it.chan, chanParent))
            if (c != null && !c.is(it)) adj.get(id.get(it)).add(id.get(c))
        }
        for (ChanUse sel : selects) {                            // Phase 249 — an ALT proceeds on any ready branch
            List<Integer> alts = new ArrayList<Integer>()
            for (ChanUse s : selectAlts.get(sel)) alts.add(id.get(s))
            orAlts.put(id.get(sel), alts)
        }
        for (ParArm a : joined) {
            for (ChanUse u : evUses) if (u.proc != null && u.proc.is(a)) adj.get(id.get(a)).add(id.get(u))
            for (ChanUse b : blockers) if (b.proc == null && b.ord < a.join) adj.get(id.get(a)).add(id.get(b))
            for (ParArm o : joined) if (!o.is(a) && o.join < a.join) adj.get(id.get(a)).add(id.get(o))
        }

        // Well-foundedness as a completion fixpoint: an event completes once everything it waits for
        // has (AND), an ALT additionally once ANY of its alternatives has (OR). Without ALTs this is
        // exactly "acyclic"; with them a cycle through an ALT is a deadlock only if every branch is
        // stuck. What is left over is the deadlocked set — explained by the cycle its wait-for edges
        // (an ALT's edges to its stuck branches included) close.
        int n = evs.size()
        boolean[] done = new boolean[n]
        boolean changed = true
        while (changed) {
            changed = false
            for (int i = 0; i < n; i++) {
                if (done[i]) continue
                boolean ok = true
                for (Integer d : adj.get(i)) if (!done[d]) { ok = false; break }
                if (ok && orAlts.containsKey(i)) {
                    ok = false
                    for (Integer d : orAlts.get(i)) if (done[d]) { ok = true; break }
                }
                if (ok) { done[i] = true; changed = true }
            }
        }
        boolean allDone = true
        for (int i = 0; i < n; i++) if (!done[i]) { allDone = false; break }
        if (allDone) return
        List<List<Integer>> stuckAdj = new ArrayList<List<Integer>>()
        for (int i = 0; i < n; i++) {
            List<Integer> es = new ArrayList<Integer>()
            if (!done[i]) {
                for (Integer d : adj.get(i)) if (!done[d]) es.add(d)
                List<Integer> alts = orAlts.get(i)
                if (alts != null) for (Integer d : alts) if (!done[d]) es.add(d)
            }
            stuckAdj.add(es)
        }
        int[] color = new int[n]                          // 0 white, 1 grey, 2 black
        List<Integer> stack = new ArrayList<Integer>()
        List<Integer> cycle = findWaitCycle(stuckAdj, color, stack)
        if (cycle != null) {
            List<String> parts = new ArrayList<String>()
            for (Integer i : cycle) parts.add(describeChanEvent(evs.get(i)))
            Object first = evs.get(cycle.get(0))
            Expression anchor = first instanceof ChanUse ? ((ChanUse) first).anchor : ((ParArm) first).anchor
            boolean rvCycle = false                       // Phase 272 — a knot that closes through a rendezvous send
            for (Integer i : cycle) { Object ev = evs.get(i); if (ev instanceof ChanUse && pairedReceive.containsKey(ev)) rvCycle = true }
            addStaticTypeError(Reporter.formatNetworkDeadlock(node.name,
                'circular wait: ' + parts.join(', which waits for ') + ', which waits for the first', rvCycle), anchor)
        } else {
            for (int i = 0; i < n; i++) if (!done[i]) {           // defensive: a stuck event without a cycle to show
                Object ev = evs.get(i)
                Expression anchor = ev instanceof ChanUse ? ((ChanUse) ev).anchor : ((ParArm) ev).anchor
                addStaticTypeError(Reporter.formatNetworkDeadlock(node.name,
                    describeChanEvent(ev) + ' can never complete'), anchor)
                return
            }
        }
    }

    // ── Phase 255 — liveness of a looping network under weak fairness ─────────────────────────
    //
    // ASSUMPTION (weak fairness): a process whose next operation is enabled eventually executes it.
    // Under it, the looping network is live — every receive eventually served, every process
    // making progress forever or to its own end — exactly when no operation waits, in every
    // iteration, on something that transitively waits on itself in the SAME iteration. Lift the
    // Phase 243 wait-for graph to the iteration index: a receive of element k on channel c waits on
    // the producer's iteration k − pre (pre = its priming sends before the loop), program order
    // within an iteration has weight 0, and the wrap to the previous iteration weight −1. Every
    // weight is ≤ 0, so a cycle of weight ≥ 0 — a real deadlock — exists iff the WEIGHT-0 subgraph
    // has a cycle: the mutual receive-first loops ("no message is ever ahead of the cycle"), while
    // the client–server loop (send then receive) and the primed cycle are live. An ALT is live when
    // some branch is fed by a pure generator (a producer loop with no receives of its own); ALTs
    // over dependent branches only are left undecided, loudly — fairness of the ALT's CHOICE is not
    // assumed. Sends never block (Phase 243), one-shot receives are the Phase 252 element-exists
    // obligations, and the base case — iteration 0 — is the pre-loop straight-line code.

    private static class LoopOp { int kind; String chan; int pos; int line; List<String> alts; String policy; boolean held }
    private static class LoopProc { LoopingStatement loop; List<Statement> block; int line; final List<LoopOp> ops = new ArrayList<LoopOp>(); boolean generator; boolean infinite; ConsumerInfo consumer }
    /** Phase 256 — a receive served by an ALT-guarded send: channel → [the selecting loop's line, the branch]. */
    private final Map<String, Object[]> guardedReplyOf = new HashMap<String, Object[]>()

    /** Returns root → reason for every stream whose liveness is NOT certified (deadlocks are reported here). */
    private Map<String, String> analyseLoopLiveness(MethodNode node, BlockStatement body, StreamScan sc, Map<String, String> parent) {
        Map<String, String> undecided = new LinkedHashMap<String, String>()
        List<LoopProc> procs = new ArrayList<LoopProc>()
        Map<String, LoopProc> producerOf = new HashMap<String, LoopProc>()
        Map<String, Integer> sendPos = new HashMap<String, Integer>()
        for (List<Statement> block : topLevelBlocks(body)) {
            for (Statement st : block) {
                if (!(st instanceof LoopingStatement)) continue
                List<StreamInfo> produced = new ArrayList<StreamInfo>()
                for (StreamInfo info : sc.streams.values()) if (info.loop.is(st)) produced.add(info)
                ConsumerInfo ci = sc.consumers.get(st)
                if (produced.isEmpty() && ci == null) continue
                LoopProc lp = new LoopProc()
                lp.loop = (LoopingStatement) st; lp.block = block; lp.line = st.lineNumber
                Statement lb = lp.loop.loopBlock
                List<Statement> top = lb instanceof BlockStatement ? ((BlockStatement) lb).statements : Collections.singletonList(lb)
                for (int pos = 0; pos < top.size(); pos++) {
                    Statement inner = top.get(pos)
                    MethodCallExpression sendCall = sendCallOf(inner, sc.streams.keySet())
                    if (sendCall != null) {
                        String c = ((VariableExpression) stripCasts(sendCall.objectExpression)).name
                        LoopOp op = new LoopOp(); op.kind = CHAN_SEND; op.chan = c; op.pos = pos; op.line = inner.lineNumber
                        lp.ops.add(op); producerOf.put(c, lp); sendPos.put(c, pos)
                    }
                    if (ci != null) {
                        final List<String> reads = new ArrayList<String>()
                        inner.visit(new CodeVisitorSupport() {
                            @Override void visitMethodCallExpression(MethodCallExpression m) {
                                String v = ci.readOf(m)                          // first() or (awaited) receive()
                                if (v != null) reads.add(v)
                                super.visitMethodCallExpression(m)
                            }
                        })
                        for (String v : reads) {
                            LoopOp op = new LoopOp(); op.kind = CHAN_RECV; op.chan = rootVia(v, parent); op.pos = pos; op.line = inner.lineNumber
                            lp.ops.add(op)
                        }
                        if (ci.altVar != null && inner instanceof ExpressionStatement && ((ExpressionStatement) inner).expression instanceof DeclarationExpression &&
                            ((DeclarationExpression) ((ExpressionStatement) inner).expression).leftExpression instanceof VariableExpression &&
                            ((VariableExpression) ((DeclarationExpression) ((ExpressionStatement) inner).expression).leftExpression).name == ci.altVar) {
                            LoopOp op = new LoopOp(); op.kind = CHAN_SUB; op.pos = pos; op.line = inner.lineNumber
                            op.alts = new ArrayList<String>()
                            for (String c : ci.altChans) op.alts.add(rootVia(c, parent))
                            op.policy = ci.altPolicy; op.held = ci.altHeld
                            lp.ops.add(op)
                        }
                    }
                }
                lp.generator = ci == null
                lp.infinite = isForever(lp.loop)
                lp.consumer = ci
                if (ci != null) {
                    List<String> altRoots = new ArrayList<String>()
                    for (String c : ci.altChans) altRoots.add(rootVia(c, parent))
                    for (Map.Entry<String, Integer> gs : ci.guardedSends.entrySet()) guardedReplyOf.put(gs.key, [lp.line, gs.value, ci.altPolicy, ci.altHeld, altRoots] as Object[])
                }
                procs.add(lp)
            }
        }
        if (procs.isEmpty()) return undecided
        // Nodes: (proc, op) in op order; the weight-0 edges.
        List<Object[]> nodes = new ArrayList<Object[]>()
        Map<LoopProc, Integer> base = new IdentityHashMap<LoopProc, Integer>()
        for (LoopProc lp : procs) { base.put(lp, nodes.size()); for (LoopOp op : lp.ops) nodes.add([lp, op] as Object[]) }
        List<List<Integer>> adj = new ArrayList<List<Integer>>()
        Map<Integer, List<Integer>> orAlts = new HashMap<Integer, List<Integer>>()     // Phase 256 — an ALT waits on ANY branch
        for (int i = 0; i < nodes.size(); i++) adj.add(new ArrayList<Integer>())
        for (LoopProc lp : procs) {
            int b = base.get(lp)
            for (int i = 1; i < lp.ops.size(); i++) adj.get(b + i).add(b + i - 1)      // program order, same iteration (weight 0)
            for (int i = 0; i < lp.ops.size(); i++) {
                LoopOp op = lp.ops.get(i)
                if (op.kind == CHAN_RECV) {
                    LoopProc prod = producerOf.get(op.chan)
                    StreamInfo info = sc.streams.get(op.chan)
                    if (prod == null || info == null) continue                          // a one-shot producer: Phase 252's obligation decides
                    if (info.pre > 0) continue                                          // primed: weight −pre, never part of a 0-cycle
                    adj.get(b + i).add(base.get(prod) + prod.ops.indexOf(prod.ops.find { LoopOp o -> o.kind == CHAN_SEND && o.chan == op.chan }))
                } else if (op.kind == CHAN_SUB) {
                    // Phase 256 — the general OR: a 0-weight alternative per branch whose producer loop is in the
                    // set and unprimed; a branch with no such edge (a one-shot or primed producer, a pure generator)
                    // is an alternative that completes on its own, so the ALT completes.
                    List<Integer> alts = new ArrayList<Integer>()
                    boolean free = false
                    for (String c : op.alts) {
                        LoopProc prod = producerOf.get(c)
                        StreamInfo info = sc.streams.get(c)
                        if (prod == null || info == null || info.pre > 0 || prod.generator) { free = true; continue }
                        alts.add(base.get(prod) + prod.ops.indexOf(prod.ops.find { LoopOp o -> o.kind == CHAN_SEND && o.chan == c }))
                    }
                    if (!free && !alts.isEmpty()) orAlts.put(b + i, alts)
                    // Phase 256/257 — STARVATION under priority: ChannelSelect prefers the lowest ready index, so a
                    // branch behind one whose producer is an infinite pure generator (always ahead, never blocking)
                    // may never be taken. `fair()` on a HELD instance rotates from the last winner (taken within n
                    // calls — no hazard); `fair()` on a fresh instance each iteration keeps no rotation state and is
                    // priority in effect (named); `random()` has no deterministic starvation (no hazard, no bound).
                    boolean effectivePriority = op.policy == 'priority' || (op.policy == 'fair' && !op.held)
                    if (effectivePriority) for (int j = 1; j < op.alts.size(); j++) {
                        for (int k = 0; k < j; k++) {
                            LoopProc ahead = producerOf.get(op.alts.get(k))
                            if (ahead != null && ahead.generator && ahead.infinite) {
                                addStaticTypeError(Reporter.formatSelectionStarvation(node.name, op.alts.get(j), op.alts.get(k), op.line,
                                    ahead.line, op.policy == 'fair'), (Statement) lp.loop)
                                break
                            }
                        }
                    }
                }
            }
        }
        // Completion fixpoint on the weight-0 graph (Phase 249's, per iteration): an op completes once its
        // same-iteration waits have, an ALT once ANY alternative has; what is left over is deadlocked.
        int n = nodes.size()
        boolean[] done = new boolean[n]
        boolean changed = true
        while (changed) {
            changed = false
            for (int i = 0; i < n; i++) {
                if (done[i]) continue
                boolean ok = true
                for (Integer d : adj.get(i)) if (!done[d]) { ok = false; break }
                if (ok && orAlts.containsKey(i)) { ok = false; for (Integer d : orAlts.get(i)) if (done[d]) { ok = true; break } }
                if (ok) { done[i] = true; changed = true }
            }
        }
        List<List<Integer>> stuckAdj = new ArrayList<List<Integer>>()
        for (int i = 0; i < n; i++) {
            List<Integer> es = new ArrayList<Integer>()
            if (!done[i]) {
                for (Integer d : adj.get(i)) if (!done[d]) es.add(d)
                List<Integer> alts = orAlts.get(i)
                if (alts != null) for (Integer d : alts) if (!done[d]) es.add(d)
            }
            stuckAdj.add(es)
        }
        int[] color = new int[n]
        List<Integer> cycle = findWaitCycle(stuckAdj, color, new ArrayList<Integer>())
        if (cycle != null) {
            List<String> parts = new ArrayList<String>()
            Set<String> roots = new HashSet<String>()
            for (Integer i : cycle) {
                LoopProc lp = (LoopProc) nodes.get(i)[0]; LoopOp op = (LoopOp) nodes.get(i)[1]
                String what = op.kind == CHAN_SEND ? "the send on '${op.chan}'" : op.kind == CHAN_SUB ?
                    "the ALT over ${op.alts.collect { "'" + it + "'" }.join(', ')}" : "the receive on '${op.chan}'"
                parts.add("${what} (line ${op.line}, in the loop at line ${lp.line})".toString())
                if (op.chan != null) roots.add(op.chan)
                if (op.alts != null) roots.addAll(op.alts)
            }
            LoopProc first = (LoopProc) nodes.get(cycle.get(0))[0]
            addStaticTypeError(Reporter.formatNetworkDeadlock(node.name,
                'circular wait in every iteration: ' + parts.join(', which waits for ') + ', which waits for the first — ' +
                'no message is ever ahead of this cycle (a priming send before one of the loops would break it)'), (Statement) first.loop)
            for (String r : roots) undecided.put(r, 'deadlocked, reported above')
        }
        undecided
    }

    /** Phase 257 — why a client of a selecting server is NOT certified, per policy; null when it is (held fair()). */
    /** Phase 257 — the request must PRECEDE the wait: a send by this process on a branch of the guarding ALT
     *  earlier in program order (in the loop body before the receive, or a priming send before the loop). */
    private static boolean requestPrecedes(ChanUse u, Object[] g, List<ChanUse> uses, Map<String, String> chanParent) {
        List<String> altRoots = (List<String>) g[4]
        for (ChanUse v : uses) {
            if (v.method == 'send' && v.proc.is(u.proc) && v.seq < u.seq && altRoots.contains(chanBaseOf(v.chan, chanParent))) return true
        }
        false
    }

    private static String guardedReplyReason(Object[] guarded) {
        String policy = guarded.length > 2 ? (String) guarded[2] : 'priority'
        boolean held = guarded.length > 3 && (Boolean) guarded[3]
        if (!CLAIM_SELECT) return "ChannelSelect prefers the lowest ready index, so whether this client is ever chosen depends on timing; per-client liveness is not certified (a fair selection needs GROOVY-12320, Groovy 6.0.0-beta-4+)"
        if (policy == 'fair' && held) return null
        if (policy == 'fair') return "fair() on a fresh ChannelSelect instance each iteration keeps no rotation state (priority in effect) — hoist the instance before the loop and reuse it; per-client liveness is not certified as written"
        if (policy == 'random') return "random() offers no bound on how long a ready branch may be passed over (fair only in expectation) — use fair() for a bounded wait; per-client liveness is not certified"
        return "ChannelSelect prefers the lowest ready index, so whether this client is ever chosen depends on timing; per-client liveness is not certified (use a held fair() instance for a bounded wait)"
    }

    private static String rootVia(String v, Map<String, String> parent) {
        String r = v; int g = 0
        while (parent.containsKey(r) && g++ < 100) r = parent.get(r)
        r
    }

    /** 1st, 2nd, 3rd, 4th … (Phase 247 — the FIFO position of a receive in a diagnostic). */
    private static String ordinalWord(int n) {
        int m = n % 100
        String sfx = (m >= 11 && m <= 13) ? 'th' : (n % 10 == 1 ? 'st' : n % 10 == 2 ? 'nd' : n % 10 == 3 ? 'rd' : 'th')
        n + sfx
    }

    /** DFS over the wait-for graph; returns the node cycle if one exists, else null. */
    private static List<Integer> findWaitCycle(List<List<Integer>> adj, int[] color, List<Integer> stack) {
        for (int s = 0; s < adj.size(); s++) {
            if (color[s] != 0) continue
            List<Integer> found = waitDfs(s, adj, color, stack)
            if (found != null) return found
        }
        null
    }

    private static List<Integer> waitDfs(int v, List<List<Integer>> adj, int[] color, List<Integer> stack) {
        color[v] = 1
        stack.add(v)
        for (Integer w : adj.get(v)) {
            if (color[w] == 1) {
                int at = stack.indexOf(w)
                return new ArrayList<Integer>(stack.subList(at, stack.size()))
            }
            if (color[w] == 0) {
                List<Integer> found = waitDfs(w, adj, color, stack)
                if (found != null) return found
            }
        }
        stack.remove(stack.size() - 1)
        color[v] = 2
        null
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
                    if (enc.tryBindChannelSelect(a.name, a.rhs)) {              // Phase 249 — an ALT's index / value
                        continue
                    }
                    if (enc.tryBindAwaitAny(a.name, a.rhs)) {
                        continue
                    }
                    // Phase 242 — the modular channel receive: `v = ch.first()` / `v = await ch.receive()`
                    // on a channel-typed param binds a fresh value carrying the channel's declared element
                    // bounds — the consumer's half of the channel contract (the producer's sends are
                    // checked in its own compilation; an unconstrained channel binds unconstrained fresh,
                    // so a stronger postcondition honestly refutes).
                    if (enc.tryBindChannelReceive(a.name, a.rhs, currentChannelRecvParams)) {
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
            String[] rgConf = (String[]) node.getNodeMetaData(RG_CONF_KEY)
            if (rgConf != null) {
                addStaticTypeError(Reporter.formatGuaranteeConformanceFailure(rgConf[0], rgConf[1], rgConf[2], r), anchor)
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
