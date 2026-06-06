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
import org.codehaus.groovy.ast.ClassNode
import org.codehaus.groovy.ast.FieldNode
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.Parameter
import org.codehaus.groovy.ast.Variable
import org.codehaus.groovy.ast.builder.AstBuilder
import org.codehaus.groovy.ast.expr.ArgumentListExpression
import org.codehaus.groovy.ast.expr.BinaryExpression
import org.codehaus.groovy.ast.expr.BooleanExpression
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.ListExpression
import org.codehaus.groovy.ast.expr.MethodCall
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.NotExpression
import org.codehaus.groovy.ast.expr.PropertyExpression
import org.codehaus.groovy.ast.expr.StaticMethodCallExpression
import org.codehaus.groovy.ast.expr.DeclarationExpression
import org.codehaus.groovy.ast.expr.TernaryExpression
import org.codehaus.groovy.ast.expr.UnaryMinusExpression
import org.codehaus.groovy.ast.expr.TupleExpression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.EmptyStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.IfStatement
import org.codehaus.groovy.ast.stmt.ReturnStatement
import org.codehaus.groovy.ast.stmt.Statement
import org.codehaus.groovy.ast.stmt.ThrowStatement
import org.codehaus.groovy.control.CompilePhase
import org.codehaus.groovy.control.SourceUnit
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
class VerifyChecker extends TypeCheckingExtension {

    private static final ClassNode REQUIRES_TYPE = ClassHelper.make(Requires)
    private static final ClassNode ENSURES_TYPE = ClassHelper.make(Ensures)
    private static final ClassNode CONTRACT_SOURCE_TYPE = ClassHelper.make(ContractSource)
    private static final ClassNode CLASS_INVARIANT_SOURCE_TYPE = ClassHelper.make(ClassInvariantSource)

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
     * Phase 45 — class-typed parameter names visible to the current method (each value is the
     * parameter's declared {@link ClassNode}). Used by the cross-class reasoning machinery: a
     * read {@code b.field} translates to a receiver-qualified entity {@code b$field}; the
     * receiver's class invariants are assumed at method entry and re-assumed after a
     * {@code b.method()} call. Only non-primitive, non-collection types end up here — sets, maps,
     * lists, and the primitive wrappers have their own dispatch (collectSetElementTypes etc.).
     */
    private Map<String, ClassNode> currentObjectParams = new LinkedHashMap<String, ClassNode>()

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
        new Encoder(session, currentEvaluator, currentSetElementTypes, currentMapTypes,
                    currentListElementTypes, currentScalarTypes, currentEnumDomainSizes,
                    currentNestedSetValueTypes, currentListNames, currentObjectParams,
                    currentBooleanLocals)
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
    private static Map<String, ClassNode> collectObjectParams(MethodNode node) {
        Map<String, ClassNode> out = new LinkedHashMap<String, ClassNode>()
        ClassNode declaring = node.declaringClass
        for (Parameter p : node.parameters) {
            if (isCrossClassObjectType(p.type, declaring)) out.put(p.name, p.type)
        }
        out
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
     * Phase 37 — annotation simple-names that mark a type use as <em>nullable</em>. Currently no-op
     * (the unannotated default already triggers the implicit obligation), but tracked so a future
     * "non-null-by-default" mode could distinguish "explicitly nullable" from "unspecified".
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
     * For a list-typed {@code ClassNode}, return true if its element generic carries a non-null
     * annotation. Reads annotations off the element {@link GenericsType}'s inner ClassNode — the
     * shape Groovy's parser leaves for {@code List<@NonNull String>}.
     */
    private static boolean hasNonNullElementAnnotation(ClassNode listType) {
        try {
            def gens = listType?.genericsTypes
            if (gens == null || gens.length < 1) return false
            ClassNode elemNode = gens[0]?.type
            return elemNode != null && hasAnnotationNamed(elemNode.annotations, NON_NULL_ANNOTATION_NAMES)
        } catch (Throwable ignored) {
            return false
        }
    }

    /** Same shape as {@link #hasNonNullElementAnnotation} but for the component type of an array. */
    private static boolean hasNonNullComponentAnnotation(ClassNode arrType) {
        try {
            ClassNode comp = arrType?.componentType
            return comp != null && hasAnnotationNamed(comp.annotations, NON_NULL_ANNOTATION_NAMES)
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
            }
        }
        ClassNode dc = node.declaringClass
        if (dc != null) for (FieldNode f : dc.fields) {
            if (isListType(f.type)) {
                ClassNode elem = firstGenericOrInt(f.type)
                if (!isIntElement(elem)) out.put(f.name, elem)
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
                    if (de.leftExpression instanceof VariableExpression) {
                        ClassNode t = ((VariableExpression) de.leftExpression).originType
                        if (t == null) t = de.leftExpression.type
                        if (t != null && isListType(t)) {
                            ClassNode elem = firstGenericOrInt(t)
                            if (!isIntElement(elem)) {
                                out.putIfAbsent(((VariableExpression) de.leftExpression).name, elem)
                            }
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
            if (isNonIntScalar(t)) out.put(p.name, t)
        }
        ClassNode dc = node.declaringClass
        if (dc != null) for (FieldNode f : dc.fields) {
            ClassNode t = f.type
            if (isNonIntScalar(t)) out.put(f.name, t)
        }
        // Phase 47h — the implicit {@code result} variable in {@code @Ensures} takes the
        // method's return type. Without this entry, a {@code @Ensures({ result.startsWith(…) })}
        // postcondition on a String-returning method would fall through {@link Encoder#isStringReceiver}
        // (not a parameter / field / typed local) and skip honestly.
        ClassNode retType = node.returnType
        if (retType != null && isNonIntScalar(retType)) out.put('result', retType)
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
                    if (de.leftExpression instanceof VariableExpression) {
                        ClassNode t = ((VariableExpression) de.leftExpression).originType
                        if (t == null) t = de.leftExpression.type
                        if (t != null && isNonIntScalar(t)) {
                            out.putIfAbsent(((VariableExpression) de.leftExpression).name, t)
                        }
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
    private static Set<String> collectBooleanLocals(MethodNode node) {
        Set<String> out = new HashSet<String>()
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
                    if (de.leftExpression instanceof VariableExpression) {
                        ClassNode t = ((VariableExpression) de.leftExpression).originType
                        if (t == null) t = de.leftExpression.type
                        if (t != null && (t.name == 'boolean' || t.name == 'java.lang.Boolean')) {
                            out.add(((VariableExpression) de.leftExpression).name)
                        }
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
        Map<String, Integer> out = new LinkedHashMap<String, Integer>()
        ClassNode dc = node.declaringClass
        if (dc == null || dc.module == null) return out
        for (ClassNode cn : dc.module.classes) {
            if (!cn.isEnum()) continue
            int count = countEnumConstants(cn)
            if (count <= 0) continue
            out.put(cn.nameWithoutPackage, count)
            String simple = simpleEnumName(cn)   // strips C$ from C$Color → Color (nested-class case)
            if (simple != cn.nameWithoutPackage) out.put(simple, count)
        }
        out
    }

    /**
     * Count actual enum constants on a ClassNode by walking its fields for declarations with the
     * JVM {@code ACC_ENUM} modifier bit set. Filters out the synthetic same-type fields Groovy
     * adds (notably {@code MIN_VALUE}/{@code MAX_VALUE}) and the array-typed {@code $VALUES}.
     */
    private static int countEnumConstants(ClassNode t) {
        int count = 0
        for (FieldNode f : t.fields) {
            if ((f.modifiers & 0x4000) != 0) count++   // 0x4000 = ACC_ENUM
        }
        count
    }

    /** True for non-Int scalar types we model under an uninterpreted Z3 sort: String, enums. */
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
        Map<String, Long> display = new LinkedHashMap<String, Long>()
        r.counterexample.each { String k, Long v ->
            // internal keys: nullity flag, array element, SSA version — surfaced via failingCall / the
            // base (entry) variable, not shown raw.
            if (k.endsWith('?null') || k.endsWith(']') || k.contains('#')) return
            if (k.endsWith('.size')) {
                String recv = k.substring(0, k.length() - '.size'.length())
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
        String n = t.nameWithoutPackage
        int dollar = n.lastIndexOf('$')
        dollar >= 0 ? n.substring(dollar + 1) : n
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
        node.parameters.each { visible.add(it.name) }
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

    @Override
    void setup() {
        backend = new Z3Backend(2000)
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
        currentBooleanLocals = collectBooleanLocals(node)
        currentEnumDomainSizes = collectEnumDomainSizes(node)
        currentIsConstructor = (node instanceof ConstructorNode)
        currentOverflowChecking = methodOrClassHasAnnotation(node, 'CheckOverflow')
        currentObjectParams = collectObjectParams(node)
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
        try {
            Statement body = (Statement) node.getNodeMetaData(
                ContractExpansionTransform.ORIGINAL_BODY_KEY)
            if (body == null) body = node.code

            LoopSite site
            try {
                site = findLoopSite(body)
            } catch (UnsupportedConstructException e) {
                addStaticTypeError(Reporter.formatLoopSkipped(node.name, e.message), node)
                return
            }

            // Implicit safety obligations (array bounds, division by zero, null
            // dereference) fire on every method, contract or not. For an
            // annotated loop they are discharged *with the invariant in scope*
            // (Phase 5b); otherwise via the per-method value-flow/havoc pass
            // (Phase 5a). Best-effort: never fail the build over them.
            try {
                if (site != null) verifyLoopObligations(node, site)
                else verifyImplicitObligations(node)
            } catch (Throwable ignored) {
            }

            if (site != null) verifyLoop(node, site)
            else verifyPostcondition(node)

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
        } finally {
            currentFacts = null
            currentMethod = null
            currentEvaluator = null
            sizeAccessors = [:]
            currentClassInvariants = Collections.<Expression> emptyList()
            currentIsConstructor = false
            currentOverflowChecking = false
            currentObjectParams = new LinkedHashMap<String, ClassNode>()
            currentSetElementTypes = new HashMap<String, ClassNode>()
            currentMapTypes = new HashMap<String, ClassNode[]>()
            currentNestedSetValueTypes = new HashMap<String, ClassNode>()
            currentNonNullElementContainers = new HashSet<String>()
            currentListNames = new HashSet<String>()
            currentListElementTypes = new HashMap<String, ClassNode>()
            currentScalarTypes = new HashMap<String, ClassNode>()
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
        try {
            List<VfObligation> sites = new ArrayList<VfObligation>()
            collectVfObligations(topStatements(body),
                new ArrayList<Object>(),
                new HashSet<String>(), sites)
            for (VfObligation v : sites) dischargeVfObligation(node, v, reqAst)
        } catch (UnsupportedConstructException ignored) {
            dischargeObligationsHavoc(node, body, reqAst)
        }
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
        List<Object> steps          // Assign | Guard | LemmaCall, in source order
    }

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
                if (elseBlk != null && !(elseBlk instanceof EmptyStatement)) {
                    collectVfObligations(topStatements(elseBlk),
                        appendStep(steps, new Guard(cond, false)),
                        new HashSet<String>(assigned), out)
                }
                continue
            }
            if (st instanceof ReturnStatement) {
                scanObligations(((ReturnStatement) st).expression, steps, out)
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
                if (e instanceof MethodCallExpression) {
                    steps.add(new LemmaCall(e))
                }
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
            col.stringCharAtSites.isEmpty() && col.stringSubstringSites.isEmpty()) return
        List<Object> snap = new ArrayList<Object>(steps)
        for (IndexSite s : col.indexSites)  out.add(mkVf(s, snap))
        for (DivideSite s : col.divideSites) out.add(mkVf(s, snap))
        for (DerefSite s : col.derefSites)  out.add(mkVf(s, snap))
        for (OverflowSite s : col.overflowSites) out.add(mkVf(s, snap))
        for (StringCharAtSite s : col.stringCharAtSites) out.add(mkVf(s, snap))
        for (StringSubstringSite s : col.stringSubstringSites) out.add(mkVf(s, snap))
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
                Object pre = enc.translate(reqAst)
                if (pre != null) s.assertExpr(pre)
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
                    Object rhs = enc.translate(a.rhs)
                    if (rhs != null) s.assertExpr(s.eq(enc.varFor(a.name), rhs))
                } else if (step instanceof Guard) {
                    Guard g = (Guard) step
                    Object c = enc.translate(g.cond)
                    if (c != null) s.assertExpr(g.positive ? c : s.not(c))
                } else if (step instanceof LemmaCall) {
                    Expression call = ((LemmaCall) step).call
                    if (applySetMutation(s, enc, call)) continue
                    if (applyMapPut(s, enc, call)) continue
                    applyListMutation(s, enc, call, Collections.<Object>emptyList())
                    // Note: countVals are scoped to a postcondition's @Ensures, not relevant for
                    // implicit obligations (bounds/null/div) — pass empty so the bcount boundary
                    // law just skips for unrelated v's. The size-thread is what we need here.
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
            Object pre = enc.translate(reqAst)
            if (pre != null) s.assertExpr(pre)
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
    }

    private void assumeIntJvmBounds(SmtSession s, Encoder enc) {
        if (currentMethod == null) return
        Object intMin = s.intLit(-2147483648L)
        Object intMax = s.intLit(2147483647L)
        for (Parameter p : currentMethod.parameters) {
            if (isJvmInt(p.type)) {
                Object v = enc.varFor(p.name)
                s.assertExpr(s.and([s.le(intMin, v), s.le(v, intMax)]))
            }
        }
        ClassNode dc = currentMethod.declaringClass
        if (dc != null) {
            for (FieldNode f : dc.fields) {
                if (isJvmInt(f.type)) {
                    Object v = enc.varFor(f.name)
                    s.assertExpr(s.and([s.le(intMin, v), s.le(v, intMax)]))
                }
            }
        }
    }

    private static boolean isJvmInt(ClassNode t) {
        String n = t?.name
        n == 'int' || n == 'java.lang.Integer'
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

    /**
     * Assert the negation of one implicit obligation against an already-seeded
     * session (context assumptions added by the caller) and report if it is not
     * discharged. Shared by the havoc pass and the Phase 5 value-flow pass.
     */
    private void dischargeObligationUnder(SmtSession s, Encoder enc, Object site) {
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
                addStaticTypeError(Reporter.formatIndexBounds(
                    ix.index.text, ix.receiver + sizeAccessor(ix.receiver), r), ix.node)
            }
            return
        }
        if (site instanceof DivideSite) {
            DivideSite dv = (DivideSite) site
            Object divisor = enc.translate(dv.divisor)
            if (divisor == null) {
                addStaticTypeError(Reporter.formatImplicitSkipped("division",
                    "divisor '${dv.divisor.text}' is outside fragment"), dv.node)
                return
            }
            s.assertExpr(s.not(s.ne(divisor, s.intLit(0L))))   // negation of (divisor != 0)
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(Reporter.formatDivisionByZero(dv.divisor.text, r), dv.node)
            }
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
                    addStaticTypeError(Reporter.formatNullDereference(
                        "${df.receiver}[${df.indexExpr.text}]", df.method, r), df.node)
                }
                return
            }
            // Obligation: ¬isNull(recv). Assert its negation, isNull(recv), and
            // check: SAT means the receiver can be null on this path.
            s.assertExpr(enc.nullityOf(df.receiver))
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(Reporter.formatNullDereference(df.receiver, df.method, r), df.node)
            }
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
                addStaticTypeError(Reporter.formatIndexBounds(
                    cs.indexExpr.text, cs.receiver + '.length()', r), cs.node)
            }
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
                addStaticTypeError(Reporter.formatIndexBounds(
                    accessor, ss.receiver + '.length()', r), ss.node)
            }
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
            if (ov.op == 'div') {
                Object intMinLit = s.intLit(-2147483648L)
                Object negOneLit = s.intLit(-1L)
                s.assertExpr(s.and([s.eq(L, intMinLit), s.eq(R, negOneLit)]))
                CheckResult r = shown(s.check())
                if (r.status != CheckResult.Status.VERIFIED) {
                    addStaticTypeError(Reporter.formatOverflow(ov.text, ov.op, r), ov.node)
                }
                return
            }
            Object result = (ov.op == '+')   ? s.plus(L, R) :
                            (ov.op == '-')   ? s.minus(L, R) :
                            (ov.op == '*')   ? s.times(L, R) :
                            (ov.op == 'neg') ? s.neg(L) :
                                               null
            if (result == null) return    // unrecognised op shouldn't happen, but be defensive
            Object intMin = s.intLit(-2147483648L)
            Object intMax = s.intLit(2147483647L)
            // ¬(INT_MIN ≤ result ∧ result ≤ INT_MAX)  ≡  result < INT_MIN ∨ result > INT_MAX
            s.assertExpr(s.or([s.lt(result, intMin), s.gt(result, intMax)]))
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(Reporter.formatOverflow(ov.text, ov.op, r), ov.node)
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
    private void verifyLoopObligations(MethodNode node, LoopSite site) {
        Expression reqAst = findRequires(node) != null ? contractAstFor(node, 'requires') : null
        LoopSpec spec = site.spec
        // 1. Prefix: @Requires + the straight-line prefix store; no invariant yet.
        dischargeRegion(site.prefix, reqAst, Collections.<Expression>emptyList(), null)
        // 2. Guard expression: evaluated whenever the invariant holds.
        for (Object s : sitesInExpression(spec.guard)) {
            dischargeSeeded(s, reqAst, spec.invariants, null, Collections.<Statement>emptyList())
        }
        // 3. Body: invariant ∧ guard, threaded through the (straight-line) body.
        List<Expression> bodyAssumed = new ArrayList<Expression>(spec.invariants)
        bodyAssumed.add(spec.guard)
        dischargeRegion(spec.body, reqAst, bodyAssumed, null)
        // 4. Suffix: invariant ∧ ¬guard (the loop has exited).
        dischargeRegion(site.suffix, reqAst, spec.invariants, spec.guard)
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
                                 List<Expression> assumePos, Expression assumeNeg) {
        if (stmts == null) return
        for (int i = 0; i < stmts.size(); i++) {
            Statement st = stmts.get(i)
            List<Statement> preceding = stmts.subList(0, i)
            if (st instanceof IfStatement) {
                IfStatement ifs = (IfStatement) st
                // Obligations in the if-condition itself: discharge with short-circuit awareness —
                // {@code xs[i] != null && xs[i].m()} needs the right deref to see the left guard.
                dischargeExpression(ifs.booleanExpression, reqAst, assumePos, assumeNeg, preceding)
                List<Expression> thenAssume = new ArrayList<Expression>(assumePos)
                thenAssume.add(ifs.booleanExpression)
                dischargeRegion(topStatements(ifs.ifBlock), reqAst, thenAssume, assumeNeg)
                Statement elseBlk = ifs.elseBlock
                if (elseBlk != null && !(elseBlk instanceof EmptyStatement)) {
                    List<Expression> elseAssume = new ArrayList<Expression>(assumePos)
                    elseAssume.add(new NotExpression(ifs.booleanExpression))
                    dischargeRegion(topStatements(elseBlk), reqAst, elseAssume, assumeNeg)
                }
                continue
            }
            // Non-if statement: walk each top-level expression with short-circuit awareness too,
            // not just {@code sitesInStatement}, so an inline {@code a != null && a.m()} in any
            // statement gets the same treatment.
            dischargeStatementShortCircuit(st, reqAst, assumePos, assumeNeg, preceding)
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
                                                List<Statement> preceding) {
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
            if (reqAst != null) {
                Object p = enc.translate(reqAst)
                if (p != null) s.assertExpr(p)
            }
            // Phase 15a — class invariants are method-entry facts, in scope across the loop's
            // prefix/guard/body/suffix regions just like @Requires.
            assumeIntJvmBounds(s, enc)
            assumeClassInvariants(s, enc)
            if (assumePos != null) {
                for (Expression e : assumePos) {
                    Object h = enc.translate(e)
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
            dischargeObligationUnder(s, enc, site)
        } finally {
            try { s.close() } catch (Throwable ignored) {}
        }
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
        r.addAll(col.stringSubstringSites)
        return r
    }

    @CompileStatic private static class IndexSite  { ASTNode node; String receiver; Expression index }
    @CompileStatic private static class DivideSite { ASTNode node; Expression divisor }
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
                divideSites.add(new DivideSite(node: be, divisor: be.rightExpression))
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
            if (!mce.implicitThis && recv instanceof VariableExpression) {
                VariableExpression v = (VariableExpression) recv
                Variable accessed = v.accessedVariable
                // Only real value variables (parameters / locals) — never a class
                // name (static call) or an unresolved dynamic reference.
                boolean realVar = accessed instanceof Parameter || accessed instanceof VariableExpression
                if (realVar && v.name != 'this' && v.name != 'super') {
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
                        mName == 'removeLast' || mName == 'pop') && margs.isEmpty()) {
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

        if (ens == null && classInvs.isEmpty()) return
        if (node.code == null) return

        Expression postAst = ens != null ? contractAstFor(node, 'ensures') : null
        if (ens != null && postAst == null) {
            addStaticTypeError(
                Reporter.formatPostconditionSkipped(node.name,
                    "contract source was not captured by ContractExpansionTransform"),
                node)
            return
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

    private void checkPath(MethodNode node, Path p, Expression postAst, Expression reqAst,
                           List<Expression> classInvs) {
        SmtSession session = backend.session()
        try {
            Encoder enc = mkEncoder(session)
            int ssaVersion = 0   // mints fresh versions for re-assigned names (SSA, see the Assign step)

            if (reqAst != null) {
                Object pre = enc.translate(reqAst)
                if (pre == null) {
                    throw new UnsupportedConstructException(
                        "precondition '${reqAst.text}' is outside fragment")
                }
                session.assertExpr(pre)
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
            // The `k` bounds of any Sets.boundedCount(_, k) in the postcondition drive the bcount per-add law.
            currentBcountKExprs = bcountKArgs(postAst)

            for (Object step : p.steps) {
                if (step instanceof Guard) {
                    Guard g = (Guard) step
                    Object c = enc.translate(g.cond)
                    if (c == null) {
                        throw new UnsupportedConstructException(
                            "guard '${g.cond.text}' is outside fragment")
                    }
                    session.assertExpr(g.positive ? c : session.not(c))
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
                    Object rhs = enc.translate(a.rhs)
                    ClassNode declaredType = currentScalarTypes.get(a.name)
                    Object fresh
                    if (declaredType != null && !isIntElement(declaredType)) {
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
                    } else if (isCallExpr(a.rhs) &&
                               assumeCalleeEnsures(session, enc, a.rhs, node, fresh, hasDecreases(node))) {
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
                } else if (step instanceof ArrayStore) {
                    ArrayStore st = (ArrayStore) step
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
                        if (valSort == session.intSort()) {
                            Object one = session.intLit(1L), zero = session.intLit(0L)
                            boolean isList = enc.isListName(st.arr)
                            Object size = isList ? enc.sizeOf(st.arr) : null
                            for (Object v : countVals) {
                                Object removed = session.ite(session.eq(session.select(oldA, idx), v), one, zero)
                                Object added = session.ite(session.eq(val, v), one, zero)
                                if (isList) {
                                    Object oldBc = session.bcount(oldA, v, zero, size)
                                    Object newBc = session.bcount(newA, v, zero, size)
                                    session.assertExpr(session.eq(newBc, session.plus(session.minus(oldBc, removed), added)))
                                } else {
                                    Object rhs = session.plus(session.minus(session.count(oldA, v), removed), added)
                                    session.assertExpr(session.eq(session.count(newA, v), rhs))
                                }
                            }
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
                    if (!applySetMutation(session, enc, call) &&
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
                Object resHandle = enc.translate(p.result)
                if (resHandle == null) {
                    throw new UnsupportedConstructException(
                        "return expression '${p.result.text}' is outside fragment")
                }
                enc.bind('result', resHandle)
                // Phase 45b — when the return expression is a list-typed local, also alias the
                // size/array oracles so {@code result.size()} and {@code result[i]} in @Ensures
                // resolve to the same threaded state the local carries. Without this, the result
                // is a bare Int handle that doesn't connect to the size/contents oracles —
                // postconditions about a returned collection couldn't reference its shape.
                aliasResultToReturnedListLocal(session, enc, p.result)
            }

            // Exit obligation: postcondition (if any) AND each class invariant. A single
            // combined check keeps the body-replay cost flat; refutation diagnostic picks
            // the message based on which obligations are in play.
            List<Object> conjuncts = new ArrayList<Object>()
            if (postAst != null) {
                Object post = enc.translate(postAst)
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

            CheckResult r = shown(session.check())
            if (r.status == CheckResult.Status.VERIFIED) return

            ASTNode anchor = (p.result != null && p.result.lineNumber > 0) ?
                (ASTNode) p.result : (ASTNode) node
            if (postAst != null) {
                // Combined or pure @Ensures failure — keep the existing message; the
                // counterexample distinguishes whether the @Ensures or an invariant clause
                // broke (a per-clause attribution is a future polish).
                addStaticTypeError(
                    Reporter.formatPostconditionFailure(node.name, postAst.text, r), anchor)
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
     * Apply a set mutation {@code s.add(x)} / {@code s.remove(x)} on a known set-typed receiver,
     * threading the set as a store on its characteristic array and asserting the per-mutation
     * cardinality law — the set analogue of the per-store {@code count} law:
     * {@code card(add(s,x)) = card(s) + (x in s ? 0 : 1)}, {@code card(remove(s,x)) = card(s) - (x in s ? 1 : 0)}.
     * Membership reads of the post-state ride Z3's array theory directly. Returns false (so the caller
     * falls through to lemma handling) when this is not a recognised set mutation.
     */
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
        enc.putMapVals(logical, s.store(enc.mapValsFor(logical), key, val))
        Object oldKeys = enc.mapKeysFor(logical)
        Object memOld = enc.member(oldKeys, key)
        Object newKeys = s.store(oldKeys, key, s.intLit(1L))
        s.assertExpr(s.eq(enc.cardOf(newKeys),
            s.plus(enc.cardOf(oldKeys), s.ite(memOld, s.intLit(0L), s.intLit(1L)))))
        enc.putMapKeys(logical, newKeys)
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
        return (direct != null && !direct.isEmpty()) ? direct[0] : null
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
    private static class LoopSite {
        Statement loopStmt
        LoopSpec spec
        /** Non-exit prefix statements only — what {@link LoopEncoder#symExec} executes. */
        List<Statement> prefix
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
        boolean beforeLoop
        Statement node
    }

    /**
     * Locate the single top-level annotated loop, returning its {@link LoopSpec}
     * plus the straight-line prefix/suffix around it, or null if there is none.
     * Raises {@link UnsupportedConstructException} (→ "skipped") if the body has
     * more than one — the spike models a single loop.
     */
    private static LoopSite findLoopSite(Statement body) {
        List<Statement> top = topStatements(body)
        int idx = -1
        for (int i = 0; i < top.size(); i++) {
            if (top.get(i).getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY) != null) {
                if (idx != -1) {
                    throw new UnsupportedConstructException(
                        "more than one annotated loop in the method body")
                }
                idx = i
            }
        }
        if (idx == -1) return null
        LoopSite site = new LoopSite()
        site.loopStmt = top.get(idx)
        site.spec = (LoopSpec) site.loopStmt.getNodeMetaData(ContractExpansionTransform.LOOP_SPEC_KEY)
        site.originalPrefix = new ArrayList<Statement>(top.subList(0, idx))
        site.originalSuffix = new ArrayList<Statement>(top.subList(idx + 1, top.size()))
        // Phase 49 (Slice A) — prefix early-exits are partitioned and verified per-path;
        // suffix exits aren't yet supported (would need state-aware {@code ¬guard} interleaving
        // at the right point in the suffix walk; the existing {@code LoopEncoder.resultExpr}
        // will reject return-shaped if-statements with its standard "unsupported statement"
        // diagnostic, which is the right honest-skip behaviour for Slice A's scope).
        site.prefix = partitionEarlyExits(site.originalPrefix, true, site.earlyExits)
        site.suffix = new ArrayList<Statement>(site.originalSuffix)
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
    private static List<Statement> partitionEarlyExits(List<Statement> stmts, boolean beforeLoop,
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
                ex.beforeLoop = beforeLoop
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
    private void verifyLoop(MethodNode node, LoopSite site) {
        Expression reqAst = findRequires(node) != null ? contractAstFor(node, 'requires') : null
        Expression postAst = findEnsures(node) != null ? contractAstFor(node, 'ensures') : null
        try {
            checkEstablishment(node, site, reqAst)
            checkPreservation(node, site)
            if (site.spec.variant != null) checkProgress(node, site)
            if (postAst != null) checkUse(node, site, reqAst, postAst)
            // Phase 49 — discharge each early-exit's @Ensures on its own path (only relevant
            // when the method has an @Ensures to prove).
            if (postAst != null) {
                for (EarlyExit ex : site.earlyExits) {
                    checkEarlyExit(node, site, ex, reqAst, postAst)
                }
            }
        } catch (UnsupportedConstructException e) {
            addStaticTypeError(Reporter.formatLoopSkipped(node.name, e.message), site.loopStmt)
        }
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
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            if (reqAst != null) s.assertExpr(LoopEncoder.tr(enc, reqAst, "precondition"))
            assumeIntJvmBounds(s, enc)
            assumeClassInvariants(s, enc)
            if (ex.beforeLoop) {
                // Assume each earlier prefix-exit's guard is false (we got here, not there).
                for (Expression g : ex.priorGuards) {
                    Object gh = enc.translate(g)
                    if (gh != null) s.assertExpr(s.not(gh))
                }
                LoopEncoder.symExec(ex.priorStmts, enc, s)
            } else {
                // Full prefix runs (no prefix exit taken), then the loop completes, then the
                // suffix priors before this exit. Loop's effect is captured by assuming the
                // invariant and ¬guard at the post-loop point.
                for (EarlyExit pe : site.earlyExits) {
                    if (pe.beforeLoop) {
                        Object gh = enc.translate(pe.guard)
                        if (gh != null) s.assertExpr(s.not(gh))
                    }
                }
                LoopEncoder.symExec(site.prefix, enc, s)
                s.assertExpr(LoopEncoder.conj(enc, s, site.spec.invariants))
                s.assertExpr(s.not(LoopEncoder.tr(enc, site.spec.guard, "guard")))
                for (Expression g : ex.priorGuards) {
                    Object gh = enc.translate(g)
                    if (gh != null) s.assertExpr(s.not(gh))
                }
                LoopEncoder.symExec(ex.priorStmts, enc, s)
            }
            // Assume the exit's own guard (we did take this exit).
            Object guardH = enc.translate(ex.guard)
            if (guardH != null) s.assertExpr(guardH)
            // Bind result to the return expression, then assert ¬postcondition.
            Object resH = enc.translate(ex.result)
            if (resH != null) enc.bind('result', resH)
            aliasResultToReturnedListLocal(s, enc, ex.result)
            Object post = enc.translate(postAst)
            if (post == null) {
                addStaticTypeError(Reporter.formatPostconditionSkipped(node.name,
                    "early-exit postcondition is outside fragment"), ex.node)
                return
            }
            s.assertExpr(s.not(post))
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(
                    Reporter.formatPostconditionFailure(node.name, postAst.text, r), ex.node)
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
            if (h != null) s.assertExpr(h)
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
            s.assertExpr(s.not(LoopEncoder.conj(enc, s, site.spec.invariants)))
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(
                    Reporter.formatLoopEstablishment(node.name, invText(site), r), site.loopStmt)
            }
        } finally { try { s.close() } catch (Throwable ignored) {} }
    }

    /** Preservation: invariant ∧ guard ∧ class invariants ∧ one body iteration ⇒ invariant still holds. */
    private void checkPreservation(MethodNode node, LoopSite site) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            s.assertExpr(LoopEncoder.conj(enc, s, site.spec.invariants))
            s.assertExpr(LoopEncoder.tr(enc, site.spec.guard, "guard"))
            assumeClassInvariants(s, enc)
            LoopEncoder.symExec(site.spec.body, enc, s)
            // Re-translating the invariant reads the post-body bindings → inv'.
            s.assertExpr(s.not(LoopEncoder.conj(enc, s, site.spec.invariants)))
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(
                    Reporter.formatLoopPreservation(node.name, invText(site), r), site.loopStmt)
            }
        } finally { try { s.close() } catch (Throwable ignored) {} }
    }

    /** Progress: invariant ∧ guard ∧ class invariants ⇒ the variant strictly decreases and stays ≥ 0. */
    private void checkProgress(MethodNode node, LoopSite site) {
        SmtSession s = backend.session()
        try {
            Encoder enc = mkEncoder(s)
            s.assertExpr(LoopEncoder.conj(enc, s, site.spec.invariants))
            s.assertExpr(LoopEncoder.tr(enc, site.spec.guard, "guard"))
            assumeClassInvariants(s, enc)
            Object oldV = LoopEncoder.tr(enc, site.spec.variant, "variant")
            LoopEncoder.symExec(site.spec.body, enc, s)
            Object newV = LoopEncoder.tr(enc, site.spec.variant, "variant")
            s.assertExpr(s.not(s.and([s.lt(newV, oldV), s.ge(newV, s.intLit(0L))])))
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                addStaticTypeError(
                    Reporter.formatLoopProgress(node.name, site.spec.variant.text, r), site.loopStmt)
            }
        } finally { try { s.close() } catch (Throwable ignored) {} }
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
            enc.bind('result', LoopEncoder.tr(enc, resultExpr, "return expression"))
            // Phase 45b — alias result's size/array oracles to the returned list local so
            // {@code result.size()} in the postcondition resolves to the local's threaded state.
            aliasResultToReturnedListLocal(s, enc, resultExpr)
            s.assertExpr(s.not(LoopEncoder.tr(enc, postAst, "postcondition")))
            CheckResult r = shown(s.check())
            if (r.status != CheckResult.Status.VERIFIED) {
                ASTNode anchor = (resultExpr != null && resultExpr.lineNumber > 0) ?
                    (ASTNode) resultExpr : (ASTNode) site.loopStmt
                addStaticTypeError(
                    Reporter.formatPostconditionFailure(node.name, postAst.text, r), anchor)
            }
        } finally { try { s.close() } catch (Throwable ignored) {} }
    }

    private static String invText(LoopSite site) {
        site.spec.invariants.collect { it.text }.join(' && ')
    }

    @Override
    void onMethodSelection(Expression expression, MethodNode target) {
        // We only care about resolvable, method-call-shaped expressions.
        if (!(expression instanceof MethodCall)) return
        if (target == null) return

        // Find @Requires on the callee. Walk superclasses too — a child
        // can inherit a contract via overriding.
        AnnotationNode req = findRequires(target)
        if (req == null) return

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

    private void verifyCallSite(MethodNode target,
                                Parameter[] formals,
                                List<Expression> argExprs,
                                Expression contractAst,
                                Expression callExpr) {

        SmtSession session = backend.session()
        try {
            Encoder enc = mkEncoder(session)

            Map<String, Object> formalBindings = [:]
            // Reference-typed formals bound to a named actual: candidates for
            // tying the size/nullity oracles across the boundary (see below).
            Map<String, String> oracleActuals = [:]

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
            if (currentMethod != null && callExpr.lineNumber > 0) {
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
            Object contractSmt = crossClassRecv != null ?
                enc.translateUnderReceiver(contractAst, crossClassRecv, crossClassFields) :
                enc.translate(contractAst)
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
                Object pre = enc.translate(reqAst)
                if (pre != null) s.assertExpr(pre)
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
    private static MethodNode resolveContractedCallee(MethodNode caller, String name, int arity, boolean allowSelf) {
        ClassNode dc = caller?.declaringClass
        if (dc == null || name == null) return null
        for (MethodNode m : dc.getMethods(name)) {
            // A self-call is the inductive hypothesis; only honour it when the caller carries a
            // termination measure (@Decreases) — its well-foundedness is checked separately.
            if (m == caller && !allowSelf) continue
            if (m.parameters.length != arity) continue
            // Usable if it has an @Ensures to assume, or an @Modifies whose effect (a havoc) we model.
            if (findEnsures(m) == null && contractAstFor(m, 'modifies') == null) continue
            return m
        }
        null
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

    /** True if every path through {@code s} ends by returning or throwing. */
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
                Object rhs = enc.translate(de.rightExpression)
                if (rhs != null) enc.bind(name, rhs) else havocLocation(enc, name)
                return true
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
                if (rhs != null) enc.bind(name, rhs) else havocLocation(enc, name)
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

    private boolean assumeCalleeEnsures(SmtSession s, Encoder enc, Expression callExpr,
                                        MethodNode caller, Object resultHandle, boolean allowSelf) {
        if (!(callExpr instanceof MethodCall)) return false
        String name = ((MethodCall) callExpr).methodAsString
        List<Expression> actuals = collectArgumentExpressions((MethodCall) callExpr)
        if (name == null || actuals == null) return false
        MethodNode callee = resolveContractedCallee(caller, name, actuals.size(), allowSelf)
        if (callee == null) return false
        Expression ensuresAst = contractAstFor(callee, 'ensures')
        Set<String> modSet = modifiedNames(callee)
        // Nothing to model — no @Ensures and no @Modifies — so we can't account for the call's effect.
        if (ensuresAst == null && (modSet == null || modSet.isEmpty())) return false

        Parameter[] formals = callee.parameters
        Map<String, Object> bindings = new LinkedHashMap<String, Object>()
        for (int i = 0; i < formals.length; i++) {
            Object h = enc.translate(actuals.get(i))
            if (h == null) return false   // can't faithfully substitute → don't assume
            bindings.put(formals[i].name, h)
        }
        if (resultHandle != null) bindings.put('result', resultHandle)

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
            }
        }

        Object post = ensuresAst != null ? enc.translateWith(ensuresAst, bindings) : null

        // Restore the caller's own `old$X` bindings; the havoced locations stay havoced.
        savedVar.each { String k, Object v -> if (v != null) enc.bind(k, v) }
        savedArr.each { String k, Object v -> if (v != null) enc.bindArray(k, v) }
        savedSet.each { String k, Object v -> if (v != null) enc.bindSet(k, v) }
        savedMapVals.each { String k, Object v -> if (v != null) enc.putMapVals(k, v) }
        savedMapKeys.each { String k, Object v -> if (v != null) enc.putMapKeys(k, v) }

        if (ensuresAst != null && post == null) return false   // @Ensures outside the fragment → skip
        if (post != null) s.assertExpr(post)
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

    /** Find a @Requires on the method, walking declared and inherited methods. */
    private static AnnotationNode findRequires(MethodNode m) {
        List<AnnotationNode> direct = m.getAnnotations(REQUIRES_TYPE)
        if (direct != null && !direct.isEmpty()) return direct[0]
        // Inheritance: simplistic, just walk superclass.
        ClassNode dc = m.declaringClass
        ClassNode sc = dc?.superClass
        if (sc != null && sc != ClassHelper.OBJECT_TYPE) {
            MethodNode inherited = sc.getMethod(m.name, m.parameters)
            if (inherited != null) return findRequires(inherited)
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
        return text != null ? parseContract(text) : null
    }

    /** Read @ContractSource's member, walking the superclass for inherited contracts. */
    private static String findContractText(MethodNode m, String kind) {
        List<AnnotationNode> sources = m.getAnnotations(CONTRACT_SOURCE_TYPE)
        if (sources != null && !sources.isEmpty()) {
            Expression member = sources[0].getMember(kind)
            if (member instanceof ConstantExpression) {
                Object v = ((ConstantExpression) member).value
                if (v instanceof String && !((String) v).isEmpty()) return (String) v
            }
        }
        ClassNode dc = m.declaringClass
        ClassNode sc = dc?.superClass
        if (sc != null && sc != ClassHelper.OBJECT_TYPE) {
            MethodNode inherited = sc.getMethod(m.name, m.parameters)
            if (inherited != null) return findContractText(inherited, kind)
        }
        return null
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
        out
    }

    /** Recursive helper: walk superclass first, then add this class's invariants (super-first order). */
    private static void walkClassInvariants(ClassNode cn, List<Expression> out) {
        if (cn == null || cn == ClassHelper.OBJECT_TYPE) return
        walkClassInvariants(cn.superClass, out)
        List<AnnotationNode> sources = cn.getAnnotations(CLASS_INVARIANT_SOURCE_TYPE)
        if (sources == null || sources.isEmpty()) return
        Expression member = sources[0].getMember('invariants')
        if (!(member instanceof ListExpression)) return
        for (Expression item : ((ListExpression) member).expressions) {
            if (item instanceof ConstantExpression) {
                Object v = ((ConstantExpression) item).value
                if (v instanceof String && !((String) v).isEmpty()) {
                    Expression parsed = parseContract((String) v)
                    if (parsed != null) out.add(parsed)
                }
            }
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
