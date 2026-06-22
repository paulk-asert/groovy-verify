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
import org.codehaus.groovy.ast.ClassHelper
import org.codehaus.groovy.ast.ClassNode
import org.codehaus.groovy.ast.FieldNode
import org.codehaus.groovy.ast.AnnotationNode
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.Parameter
import org.codehaus.groovy.ast.expr.ArgumentListExpression
import org.codehaus.groovy.ast.expr.ArrayExpression
import org.codehaus.groovy.ast.expr.BinaryExpression
import org.codehaus.groovy.ast.expr.BooleanExpression
import org.codehaus.groovy.ast.expr.CastExpression
import org.codehaus.groovy.ast.expr.ListExpression
import org.codehaus.groovy.ast.expr.MapEntryExpression
import org.codehaus.groovy.ast.expr.MapExpression
import org.codehaus.groovy.ast.expr.ClassExpression
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.ConstructorCallExpression
import org.codehaus.groovy.ast.expr.DeclarationExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.GStringExpression
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.BitwiseNegationExpression
import org.codehaus.groovy.ast.expr.NotExpression
import org.codehaus.groovy.ast.expr.PostfixExpression
import org.codehaus.groovy.ast.expr.PrefixExpression
import org.codehaus.groovy.ast.expr.PropertyExpression
import org.codehaus.groovy.ast.expr.RangeExpression
import org.codehaus.groovy.ast.expr.StaticMethodCallExpression
import org.codehaus.groovy.ast.expr.ElvisOperatorExpression
import org.codehaus.groovy.ast.expr.TernaryExpression
import org.codehaus.groovy.ast.expr.TupleExpression
import org.codehaus.groovy.ast.expr.UnaryMinusExpression
import org.codehaus.groovy.ast.expr.UnaryPlusExpression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.CaseStatement
import org.codehaus.groovy.ast.stmt.EmptyStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.ReturnStatement
import org.codehaus.groovy.ast.stmt.Statement
import org.codehaus.groovy.ast.stmt.SwitchStatement
import org.codehaus.groovy.ast.stmt.Statement
import org.codehaus.groovy.syntax.Token
import org.codehaus.groovy.syntax.Types

/**
 * Translates the supported fragment of Groovy expressions into SMT
 * via {@link SmtSession}. Returns {@code null} for anything outside
 * the fragment — the caller treats that as "skipped: outside
 * fragment" and emits a warning rather than passing silently.
 *
 * Supported:
 *   - integer literals
 *   - variable references (declared on demand as integer constants)
 *   - unary +/-
 *   - binary +, -, * (multiplication only if at least one side is
 *     a literal; pure NIA is a documented non-goal of v1)
 *   - comparisons ==, !=, <, <=, >, >=
 *   - boolean &&, ||, !
 *   - collection/array size: {@code xs.size()}, {@code xs.length},
 *     {@code xs.isEmpty()} via a {@link #sizeOf size oracle} (an integer
 *     constant {@code <name>.size >= 0} shared with the array-bounds checks)
 *   - nullity: {@code x == null} / {@code x != null} via a {@link #nullityOf
 *     nullity oracle} (a boolean "is null" flag per reference)
 *   - {@code x.equals(y)} as a synonym for {@code x == y}
 *   - {@code xs.contains(y)} as precise membership over the modelled contents
 *   - finite {@code Set<Integer>} membership ({@code x in s}, {@code s.contains(x)}),
 *     mutation ({@code s.add(x)}/{@code s.remove(x)}) and cardinality ({@code s.size()}):
 *     a set is a characteristic {@code Array Int -> Int}, and {@code size()} carries a
 *     per-mutation update law (see {@link #cardOf}); set names are supplied by the checker
 *   - finite {@code Map<Integer,Integer>}: value lookup ({@code m[k]}, {@code m.get(k)}),
 *     key membership ({@code k in m}, {@code m.containsKey(k)}) and size ({@code m.size()}) —
 *     a value array plus a key-set (so size and its law come from the set machinery above)
 *

 * Not supported (yet, deliberately):
 *   - the *value* of an indexed access {@code arr[i]} or a quotient
 *     {@code a / b} (only their safety side-conditions are checked, in
 *     {@link VerifyChecker}); array contents are not modelled
 *   - bitwise ops, shifts
 *   - quantifiers
 */
@CompileStatic
class Encoder {

    final SmtSession session
    /** Variable name in source scope -> SMT handle. */
    private final Map<String, Object> env = [:]
    /**
     * Phase 75 — stream-{@code every} call nodes (by identity) sitting in <em>positive</em> polarity of
     * the proof goal currently being translated (set by {@link #translateGoal}). The unbounded-stream
     * induction encoding ({@code base ∧ step}) is only <em>sound</em> when proven, not when assumed, so
     * it fires only for nodes in this set; elsewhere an unbounded stream {@code every} skips loudly.
     */
    private final Set<Expression> goalPositiveEvery =
        Collections.newSetFromMap(new IdentityHashMap<Expression, Boolean>())
    /** Max element count for the bounded-unroll path; a larger / symbolic limit takes the induction path. */
    private static final int STREAM_UNROLL_CAP = 256
    /** Cache of size-oracle constants, keyed by their SMT name. */
    private final Map<String, Object> sizeEnv = [:]
    /** Cache of nullity-oracle booleans, keyed by reference name. */
    private final Map<String, Object> nullEnv = [:]
    /** Cache of array-content handles ({@code Array Int -> Int}), keyed by source name. */
    private final Map<String, Object> arrEnv = [:]
    /** Cache of set handles (characteristic {@code Array Int -> Int}), keyed by source name / {@code old$name}. */
    private final Map<String, Object> setEnv = [:]
    /**
     * Source-level names known to be {@code java.util.Set}-typed (params/fields), each mapped to its
     * declared element type (Phase 27). Membership/size/{@code contains} on these names lower to set
     * semantics rather than the list/array oracles — the one place the otherwise shape-based encoder
     * needs a type hint, because set operations are syntactically indistinguishable from list ones.
     * The element type drives non-Int sort routing: a {@code Set<String>}'s element constants live in
     * an uninterpreted Z3 {@code String!Sort}, a {@code Set<Integer>}'s in {@code Int} (the default).
     */
    private final Map<String, ClassNode> setElementTypes
    /**
     * Source-level names known to be {@code java.util.Map}-typed, each mapped to its declared
     * {@code [keyType, valueType]} pair (Phase 27). A map is modelled as a value array (its contents,
     * {@code m[k]}) <em>plus</em> a key-set (a characteristic array, giving {@code m.containsKey}/
     * {@code m.size()} and the cardinality law) — so it builds directly on the set machinery.
     */
    private final Map<String, ClassNode[]> mapTypes
    /**
     * Phase 36 — for each {@code Map<K, Set<V>>} param/field, the inner {@code Set}'s element type
     * {@code V}. The map's value sort routes through {@link SmtSession#arraySort} to the
     * characteristic-array sort {@code Array<V, Int>}, so {@code m[k]} reads as an array term the
     * encoder lowers downstream membership/{@code containsAll} through.
     */
    private final Map<String, ClassNode> nestedSetValueTypes
    /**
     * Phase 41 — every {@link java.util.List}-typed parameter/field, regardless of element type.
     * The {@code .count(v)} dispatch routes List receivers through bounded count
     * {@code bcount(arr, v, 0, sizeOf)}; arrays keep the unbounded {@link SmtSession#count}.
     */
    private final Set<String> listNames
    /**
     * Source-level names known to be {@code java.util.List}-typed, each mapped to its declared
     * element type (Phase 27). The encoder defaults Lists to Int-element when no type hint is supplied
     * (today's behaviour), so this map is populated only for non-Int element domains.
     */
    private final Map<String, ClassNode> listElementTypes
    /**
     * Non-Int scalar parameter/field names (Phase 27 step 9). A {@code String s} parameter looked up
     * via {@link #varFor} dispatches to {@link #varForOfSort} on the declared sort here, so
     * {@code s == "admin"} translates as {@code (String!Sort eq String!Sort)} rather than the
     * sort-mismatched {@code (Int eq String!Sort)}.
     */
    private final Map<String, ClassNode> scalarTypes
    /**
     * Phase 28 — same-module enum classes, mapped from simple name (and inner-class-stripped
     * name) to value count. Used by {@link #enumValuesCountFor} to fold a
     * {@code Color.values().length} (or {@code .size()}) re-parsed-contract expression to the
     * literal constant count when the receiver appears as an unresolved {@link VariableExpression}.
     * The post-resolution {@link ClassExpression} shape doesn't need this map — the count comes
     * from walking the type's fields directly.
     */
    private final Map<String, Integer> enumDomainSizes
    /**
     * Phase 38b — local variables bound to a recognised immutable-container factory: {@code xs}
     * after {@code xs = List.of(1, 2, 3)} (or {@code [1, 2, 3]} / {@code Map.of(…)} / {@code Set.of(…)}).
     * The Assign-step handler in {@link VerifyChecker} calls {@link #tryRecordFactoryAssign} on
     * each declaration before falling through to the int-SSA path, so subsequent receiver lookups
     * by {@link #factoryContainerFor} resolve the local to its recorded factory and the same
     * peephole folds (.size, .contains, .get(literal_i), …) apply across the variable boundary.
     * Per-session — fresh on each new {@link Encoder} — which matches the body-replay rhythm.
     */
    private final Map<String, FactoryContainer> localFactories = new LinkedHashMap<String, FactoryContainer>()
    /**
     * Phase 31 — side-effect populated by {@link #translateSetsBounded}: when the user writes
     * {@code Sets.boundedBy(t, n)} for an Int-element set, the translator records {@code t}'s set key
     * → {@code n}'s Z3 handle here. Then a later {@code s.containsAll(t)} translation on Int sets
     * consults this map to bound the universal {@code ∀i. 0<=i<n ⟹ (i ∈ t ⟹ i ∈ s)}. Without a
     * registered bound, Int subset skips honestly (the universal would be unbounded — the
     * trigger-cliff non-goal).
     */
    private final Map<String, Object> intSubsetBounds = new LinkedHashMap<String, Object>()
    /**
     * Phase 151 — a variable name → the JSR 385 Quantity *expression* it was bound from (e.g. {@code result}
     * → the method's return expression {@code 1.km * 1.km}). The magnitude/dimension readers ({@link #siMagnitude},
     * {@link #dimensionOf}, {@link #currentUnitScale}) resolve such a name back to its source expression, so a
     * quantity-to-quantity {@code @Ensures({ result == 1.km })} can reason about the returned quantity's value and
     * dimension. A quantity has no scalar Z3 handle (it's value × dimension), so this aliasing — not a handle bind —
     * is how {@code result} participates.
     */
    private final Map<String, Expression> quantitySource = new LinkedHashMap<String, Expression>()
    /**
     * Phase 153 — Groovy 6 async/await. A local name → the value-expression of the `async { e }` it was bound from.
     * `async { e }` lowers (at parse time) to {@code AsyncSupport.async({ e })}, and `await x` to
     * {@code AsyncSupport.await(x)}. A *safe* async closure — one that returns a pure value (the discipline the
     * Groovy async docs prescribe) — is observationally just its value, driven synchronously, so a later `await fa`
     * reads out `e`. This proves the functional contract while *assuming* the structural (scheduling) half — the same
     * posture as the lock/agent examples. A closure that mutates shared state is the unsafe/structural case and skips.
     */
    private final Map<String, Expression> asyncSource = new LinkedHashMap<String, Expression>()
    /** Set handles whose {@code card >= 0} has already been asserted (mint-once, like the size oracle). */
    private final Set<Object> cardConstrained = new HashSet<Object>()
    /**
     * While translating a quantifier body, the {@code (select arr i)} terms are
     * collected here to serve as the quantifier's instantiation triggers; null
     * outside a quantifier.
     */
    private List<Object> triggerSink = null
    /** Counter for minting unique bound-variable names across nested/multiple quantifiers. */
    private int quantCounter = 0

    /**
     * Phase 45 — receiver-qualified field translation context. While translating a contract
     * expression on behalf of a foreign receiver (e.g. assuming {@code b}'s class invariants
     * after a call), bare {@code field} references that name a field of the receiver's class
     * are rewritten to {@code recv$field} entities. Empty context (the default) is the normal
     * "this-class" translation regime: bare {@code field} means {@code this.field}.
     */
    private String receiverPrefix = null
    private Set<String> receiverFields = Collections.<String>emptySet()
    /**
     * Phase 45 — class-typed (object) parameter names visible to the current method, each
     * paired with its declared {@link ClassNode}. Lets {@code b.field} on a known-class
     * receiver translate to a receiver-qualified entity {@code b$field}, distinct from any
     * same-named field of the declaring class. Sound only under the no-aliasing assumption
     * the project takes as a non-goal.
     */
    private final Map<String, ClassNode> objectParams
    /**
     * Phase 80 — tuple-typed parameters/fields ({@code Tuple2<Integer,String> t}), name → the {@code TupleN}
     * {@link ClassNode}. Unlike a constructed/returned tuple (a factory container with known slot
     * expressions), a tuple parameter's slots are the caller's values, so {@code t.vN}/{@code t[k]} mint a
     * fresh typed entity {@code t$vN} in the slot's sort (the slot type from the generic arguments).
     */
    private final Map<String, ClassNode> tupleParams
    /**
     * Phase 116 — equational *combiner* registry: a same-unit method `f(a, b)` with no `@Requires` and an
     * `@Ensures({ result == E(a, b) })` (a monoid/semigroup combiner). Keyed `name/arity` → `[formalNames, E]`.
     * A call `f(x, y)` is translated as `E[a:=x, b:=y]`, so a reduction `acc = f(acc, x)` matches the inline
     * sum/product/extremum patterns. Sound: `f`'s `@Ensures` is verified when `f` is checked, no `@Requires`.
     */
    private final Map<String, Object[]> combiners

    /** Phase B — wrapper-carrier types in scope: simple name → resolved {@link ClassNode}. A single-field
     *  immutable {@code @Monadic} carrier is modelled as a one-constructor datatype (see {@link #wrapperContentField}). */
    private final Map<String, ClassNode> carrierTypes

    /** Phase C — declared return type of a {@code Function}-typed parameter (its second generic), so {@code
     *  f.apply(x)} can range over the right sort (e.g. a bind function returns the carrier). */
    private final Map<String, ClassNode> functionReturnTypes

    /** Optional pure-function evaluator/unfolder (Phase 8a); null disables both. */
    private final PureEvaluator pureEvaluator
    /**
     * Per-*term* unfolding depth for the defining-equation expansion (Phase 8a). A {@code f#(args)} term
     * asserts its equation and unfolds its body's recursive calls to {@code depth - 1}, restoring the
     * counter afterwards — so each *top-level* call (e.g. the goal {@code chain(u,d)} and the hypothesis's
     * {@code chain(next[u],d-1)}) gets the same depth independently, rather than draining one shared budget
     * (which the drifting recursion of an inductive function would exhaust before the goal is even defined).
     */
    private static final int MAX_UNFOLD_DEPTH = 6
    private int unfoldDepth = MAX_UNFOLD_DEPTH
    /** Call terms {@code f#(args)} whose defining equation has already been asserted (assert-once per term). */
    private final Set<Object> definedCalls = new HashSet<Object>()

    /**
     * Phase 48b — names of boolean locals (set by VerifyChecker from a clean-body scan). Used
     * by {@link #varFor} so a fresh-session reference to a body-local boolean mints a
     * {@code boolVar} rather than the default {@code intVar} — without this, a loop guard
     * like {@code !composite} hits {@code session.not(intExpr)} and crashes Z3.
     */
    private final Set<String> booleanLocals
    /**
     * Phase 61 — names (params, fields, locals, and {@code result}) whose declared type is a decimal
     * (BigDecimal / Double / Float / double / float). A reference to one of these — or any {@code /}
     * operation, or arithmetic touching a decimal literal — is translated in Z3's Real sort.
     */
    private final Set<String> decimalNames

    Encoder(SmtSession session, PureEvaluator pureEvaluator = null,
            Map<String, ClassNode> setElementTypes = null,
            Map<String, ClassNode[]> mapTypes = null,
            Map<String, ClassNode> listElementTypes = null,
            Map<String, ClassNode> scalarTypes = null,
            Map<String, Integer> enumDomainSizes = null,
            Map<String, ClassNode> nestedSetValueTypes = null,
            Set<String> listNames = null,
            Map<String, ClassNode> objectParams = null,
            Set<String> booleanLocals = null,
            Set<String> decimalNames = null,
            Map<String, Boolean> fpNames = null,
            Map<String, ClassNode> tupleParams = null,
            Map<String, Object[]> combiners = null,
            Map<String, ClassNode> carrierTypes = null,
            Map<String, ClassNode> functionReturnTypes = null) {
        this.session = session
        this.combiners = combiners != null ? combiners : new LinkedHashMap<String, Object[]>()
        this.carrierTypes = carrierTypes != null ? carrierTypes : new HashMap<String, ClassNode>()
        this.functionReturnTypes = functionReturnTypes != null ? functionReturnTypes : new HashMap<String, ClassNode>()
        this.pureEvaluator = pureEvaluator
        this.setElementTypes = setElementTypes != null ? setElementTypes : new HashMap<String, ClassNode>()
        this.mapTypes = mapTypes != null ? mapTypes : new HashMap<String, ClassNode[]>()
        this.listElementTypes = listElementTypes != null ? listElementTypes : new HashMap<String, ClassNode>()
        this.scalarTypes = scalarTypes != null ? scalarTypes : new HashMap<String, ClassNode>()
        this.enumDomainSizes = enumDomainSizes != null ? enumDomainSizes : new HashMap<String, Integer>()
        this.nestedSetValueTypes = nestedSetValueTypes != null ? nestedSetValueTypes : new HashMap<String, ClassNode>()
        this.listNames = listNames != null ? listNames : new HashSet<String>()
        this.objectParams = objectParams != null ? objectParams : new LinkedHashMap<String, ClassNode>()
        this.booleanLocals = booleanLocals != null ? booleanLocals : new HashSet<String>()
        this.decimalNames = decimalNames != null ? decimalNames : new HashSet<String>()
        this.fpNames = fpNames != null ? fpNames : new HashMap<String, Boolean>()
        this.tupleParams = tupleParams != null ? tupleParams : new LinkedHashMap<String, ClassNode>()
    }

    /** Phase 73 — {@code double}/{@code float} names mapped to precision ({@code true} = double/Float64,
     *  {@code false} = float/Float32). Modelled with Z3's faithful IEEE-754 FP theory in straight-line
     *  code; an FP construct outside the fragment (a loop, a transcendental, int-mixing) still skips. */
    private final Map<String, Boolean> fpNames

    /**
     * Phase 45 — run a translation under a foreign-receiver context: bare {@code field} references
     * that name a field of the receiver's class are rewritten to {@code recv$field}. Used when
     * assuming foreign-class invariants, asserting a callee's @Ensures across classes, or
     * discharging a callee's @Requires from the call site. The context is unwound on return so
     * subsequent translations resume the normal this-class regime.
     */
    Object translateUnderReceiver(Expression e, String recvName, Set<String> fieldNames) {
        String savedPrefix = receiverPrefix
        Set<String> savedFields = receiverFields
        try {
            receiverPrefix = recvName
            receiverFields = fieldNames ?: Collections.<String>emptySet()
            return translate(e)
        } finally {
            receiverPrefix = savedPrefix
            receiverFields = savedFields
        }
    }

    /** Phase 45 — true if {@code name} is a known class-typed parameter visible to the current method. */
    boolean isObjectParam(String name) { objectParams.containsKey(name) }

    /** Phase 45 — declared field names of an object parameter, used to drive the receiver-context substitution. */
    Set<String> fieldsOfObjectParam(String name) {
        ClassNode t = objectParams.get(name)
        if (t == null) return Collections.<String>emptySet()
        Set<String> out = new LinkedHashSet<String>()
        List<FieldNode> fs = t.fields
        if (fs != null) for (FieldNode f : fs) out.add(f.name)
        out
    }

    // ── Phase 89 (slice 1) — reference identity + identity-keyed field reads ──────────────────────
    // An object parameter whose class is shared by *another* object parameter is "alias-modelled":
    // its Int fields are read through a per-(class, field) heap map indexed by the object's identity,
    // so `a.f` and `b.f` coincide *exactly* when `a === b` / `a.is(b)` (identity equality). Methods with
    // a single object param (or distinct classes) keep the per-name `b$field` model untouched — zero
    // regression. Slice 1 is read-only (Int fields): field *writes* through references are a follow-on.
    private Set<String> aliasModeledCache = null
    private Set<String> aliasModeledParams() {
        if (aliasModeledCache != null) return aliasModeledCache
        Map<String, Integer> byClass = new LinkedHashMap<String, Integer>()
        for (ClassNode c : objectParams.values()) {
            String k = c?.name
            if (k != null) byClass.put(k, (byClass.containsKey(k) ? byClass.get(k) : 0) + 1)
        }
        Set<String> out = new LinkedHashSet<String>()
        for (Map.Entry<String, ClassNode> e : objectParams.entrySet()) {
            String k = e.value?.name
            if (k != null && byClass.get(k) >= 2) out.add(e.key)
        }
        aliasModeledCache = out
        out
    }

    /** Phase 89 — true if {@code name} is an object param whose class is shared by another object param. */
    private boolean isAliasModeled(String name) { aliasModeledParams().contains(name) }

    /** Phase 89 — the object identity of an alias-modelled reference: an unconstrained {@code name$id} Int. */
    private Object objId(String name) { varForRaw(name + '$id') }

    /** Phase 89 — the per-(class, field) heap map for an Int field — an {@code Int → Int} array.
     *  Routed through {@link #arrayFor} (the SSA-able array env) so a field *write* (Phase 89 slice 2)
     *  rebinds it and subsequent reads — including through an aliased reference — see the store. */
    private String fieldMapKey(String className, String field) { '$fmap$' + className + '$' + field }
    private Object fieldMap(String className, String field) { arrayFor(fieldMapKey(className, field)) }

    /**
     * Phase 89 slice 2 — {@code obj.field = val} for an alias-modelled object's Int field: store into
     * the identity-keyed heap map, so a later read of {@code obj.field} (or {@code other.field} when
     * {@code other === obj}) sees it. Returns false when not applicable (caller then skips loudly).
     */
    boolean storeField(String objName, String field, Object valHandle) {
        if (valHandle == null || !isAliasModeled(objName)) return false
        ClassNode ft = fieldTypeOfObjectParam(objName, field)
        if (ft == null || !isIntLikeType(ft)) return false
        String key = fieldMapKey(objectParams.get(objName).name, field)
        bindArray(key, session.store(arrayFor(key), objId(objName), valHandle))
        true
    }

    /** Phase 89 — declared type of {@code field} on object parameter {@code name}, or null. */
    private ClassNode fieldTypeOfObjectParam(String name, String field) {
        ClassNode t = objectParams.get(name)
        if (t == null || t.fields == null) return null
        for (FieldNode f : t.fields) if (f.name == field) return f.type
        null
    }

    /** Phase 89 — {@code id(a) == id(b)} when both sides are object-parameter references; null otherwise. */
    private Object refIdentityEq(Expression l, Expression r) {
        if (!(l instanceof VariableExpression) || !(r instanceof VariableExpression)) return null
        String ln = ((VariableExpression) l).name
        String rn = ((VariableExpression) r).name
        if (!objectParams.containsKey(ln) || !objectParams.containsKey(rn)) return null
        session.eq(objId(ln), objId(rn))
    }

    /**
     * Phase 46a — true if {@code recv} is a String-typed expression: a String parameter / local
     * recorded in {@link #scalarTypes}, or a String literal. {@code translateMethodCall} consults
     * this to route {@code startsWith} / {@code endsWith} / {@code contains} / {@code isEmpty} to
     * the string-predicate uninterpreted functions instead of the list-style array dispatch.
     * {@code PropertyExpression} forms (a String field on a known object) are intentionally not
     * routed here yet — they'd need to compose with the receiver-context machinery; out of scope
     * for this slice.
     */
    private boolean isStringReceiver(Expression recv) {
        if (recv == null) return false
        if (recv instanceof ConstantExpression) {
            return ((ConstantExpression) recv).value instanceof String
        }
        // Phase 47h — a GString {@code "hello $name"} produces a {@code CharSequence} at runtime
        // and equals a {@code String} by content. The encoder translates GString to chained
        // {@code stringConcat}, yielding a Seq Char term — same sort, same equality semantics.
        if (recv instanceof GStringExpression) return true
        if (recv instanceof VariableExpression) {
            String n = ((VariableExpression) recv).name
            ClassNode t = scalarTypes.get(n)
            return t != null && t.name == 'java.lang.String'
        }
        // {@code xs[i].startsWith(...)} where {@code xs} is a {@code List<String>} — the GDK
        // {@code getAt} shape and the bracketed binary form both reach here. Routing on element
        // type lets the user filter strings without first assigning to a String-typed local
        // (locals aren't recorded in {@code scalarTypes}).
        if (recv instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) recv
            if (be.operation.type == Types.LEFT_SQUARE_BRACKET) {
                Expression listRecv = be.leftExpression
                if (listRecv instanceof VariableExpression) {
                    ClassNode et = listElementTypes.get(((VariableExpression) listRecv).name)
                    return et != null && et.name == 'java.lang.String'
                }
            }
            // Phase 47 — {@code s + t} yields a String when both operands are String-typed.
            // Lets {@code (s + "x").length()} translate through, with the encoder's binary-
            // dispatch then routing to {@code stringConcat}.
            if (be.operation.type == Types.PLUS) {
                return isStringReceiver(be.leftExpression) && isStringReceiver(be.rightExpression)
            }
        }
        if (recv instanceof MethodCallExpression) {
            MethodCallExpression mc = (MethodCallExpression) recv
            String m = mc.methodAsString
            if (m == 'get' && argList(mc).size() == 1 &&
                mc.objectExpression instanceof VariableExpression) {
                ClassNode et = listElementTypes.get(((VariableExpression) mc.objectExpression).name)
                return et != null && et.name == 'java.lang.String'
            }
            // Phase 47 — string-returning methods on a String receiver. {@code substring},
            // {@code concat}, and {@code replace} all return String, so a chained
            // {@code s.substring(1, 4).length()} or {@code s.replace("a", "b").length()}
            // resolves correctly through the string-receiver path.
            if ((m == 'substring' || m == 'concat' || m == 'replace' || m == 'replaceAll' ||
                 m == 'toUpperCase' || m == 'toLowerCase' || m == 'reverse') &&
                isStringReceiver(mc.objectExpression)) {
                return true
            }
            // Phase 47e — static int→string conversions also produce String values.
            Expression mcRecv = mc.objectExpression
            boolean isIntCls = (mcRecv instanceof VariableExpression && ((VariableExpression) mcRecv).name == 'Integer') ||
                               (mcRecv instanceof PropertyExpression && ((PropertyExpression) mcRecv).propertyAsString == 'Integer') ||
                               (mcRecv instanceof ClassExpression && ((ClassExpression) mcRecv).type?.nameWithoutPackage == 'Integer')
            boolean isStrCls = (mcRecv instanceof VariableExpression && ((VariableExpression) mcRecv).name == 'String') ||
                               (mcRecv instanceof PropertyExpression && ((PropertyExpression) mcRecv).propertyAsString == 'String') ||
                               (mcRecv instanceof ClassExpression && ((ClassExpression) mcRecv).type?.nameWithoutPackage == 'String')
            if (isIntCls && m == 'toString' && argList(mc).size() == 1) return true
            if (isStrCls && m == 'valueOf' && argList(mc).size() == 1) return true
        }
        return false
    }

    /**
     * Phase 47h — translate a {@link GStringExpression} ({@code "hello $name"}) to chained
     * {@code stringConcat}. The expression carries parallel lists of static text
     * ({@code strings}, all {@code ConstantExpression}s of String type) and interpolated
     * values ({@code values}, arbitrary expressions). Interleaved as
     * {@code strings[0] · values[0] · strings[1] · values[1] · … · strings[n]}, the static
     * texts always sandwiching the values. Empty static parts are common at the start / end
     * ({@code "$name"} produces {@code strings=["", ""]}, {@code values=[name]}).
     *
     * <p>Returns null if any value can't be coerced to a String term — the dispatch then
     * surfaces "outside fragment" cleanly.
     */
    private Object translateGString(GStringExpression gs) {
        Object strSort = session.declareSort('String')
        List<ConstantExpression> strs = gs.strings
        List<Expression> vals = gs.values
        List<Object> parts = new ArrayList<Object>(strs.size() + vals.size())
        for (int i = 0; i < strs.size(); i++) {
            Object lit = translateInSort(strs.get(i), strSort)
            if (lit == null) return null
            parts.add(lit)
            if (i < vals.size()) {
                Object val = translateValueAsString(vals.get(i))
                if (val == null) return null
                parts.add(val)
            }
        }
        // Fold concat from left. Z3's varargs accepts the whole list; we chain pairwise
        // through the existing {@link SmtSession#stringConcat} which already handles the
        // {@code mkConcat} overload disambiguation.
        Object acc = parts.get(0)
        for (int i = 1; i < parts.size(); i++) {
            acc = session.stringConcat(acc, parts.get(i))
        }
        acc
    }

    /**
     * Phase 47h — coerce an interpolated value into a String term. Strategy:
     * <ul>
     *   <li>If {@link #isStringReceiver} recognises the expression (String literal, String
     *       parameter, {@code s + t}, {@code s.substring(...)}, etc., plus a nested GString),
     *       translate as String via {@link #translateInSort}.</li>
     *   <li>Otherwise try {@link #translate} (yielding an Int handle in the common case) and
     *       convert via {@link SmtSession#stringFromInt} — same Z3 {@code intToString} the
     *       Phase 47e {@code Integer.toString} dispatch uses. Carries the same semantic gap
     *       for negative inputs (Z3 yields the empty string).</li>
     * </ul>
     * Boolean and other types aren't recognised yet; null returned → honest skip.
     */
    private Object translateValueAsString(Expression v) {
        if (isStringReceiver(v)) {
            Object strSort = session.declareSort('String')
            return translateInSort(v, strSort)
        }
        Object h = translate(v)
        if (h == null) return null
        return session.stringFromInt(h)
    }

    /**
     * Phase 47c — translate a Groovy regex literal to a Z3 {@code ReExpr}. Recursive-descent
     * parser supporting the most common features: literal characters, escapes, alternation
     * ({@code re1 | re2}), concatenation ({@code re1 re2}), quantifiers ({@code re*},
     * {@code re+}, {@code re?}), groups ({@code (re)}), and character classes
     * ({@code [abc]}, {@code [a-z]}). Returns null on any unsupported feature (anchors
     * {@code ^}/{@code $}, predefined classes {@code \d}/{@code \w}/{@code \s},
     * quantified-ranges {@code {n,m}}, negated classes {@code [^…]}, lookahead/lookbehind,
     * backreferences) — the caller surfaces the null as an honest skip.
     *
     * <p>Argument must be a String literal {@code ConstantExpression} — dynamic regex
     * strings can't be statically parsed. The dispatch already returns null for those.
     */
    private Object parseRegexLiteral(Expression arg) {
        if (!(arg instanceof ConstantExpression)) return null
        Object v = ((ConstantExpression) arg).value
        if (!(v instanceof String)) return null
        String pattern = (String) v
        try {
            RegexParser p = new RegexParser(pattern, session)
            Object re = p.parseAlt()
            if (p.pos != pattern.length()) return null   // didn't consume all — malformed or unsupported
            return re
        } catch (Throwable t) {
            return null   // any parse error or unsupported-feature trap → honest skip
        }
    }

    /** The String value of a {@code ConstantExpression}, or null if {@code e} isn't a compile-time string. */
    private static String constStr(Expression e) {
        (e instanceof ConstantExpression && ((ConstantExpression) e).value instanceof String) ?
            (String) ((ConstantExpression) e).value : null
    }

    /**
     * True when {@code p} is a regex with no metacharacters — i.e. it matches exactly itself, so a
     * {@code replaceFirst}/{@code replaceAll} regex coincides with a literal-substring match and the
     * string model is sound. Any of {@code \ . [ ] {@literal {} } ( ) * + ? ^ $ |} makes it a real regex.
     */
    private static boolean isPlainLiteralRegex(String p) {
        for (char c : p.toCharArray()) if ('\\.[]{}()*+?^$|'.indexOf((int) c) >= 0) return false
        true
    }

    /**
     * Phase 47c — small recursive-descent regex parser. Builds a Z3 {@code ReExpr} bottom-up
     * via the {@link SmtSession} regex constructors. Grammar:
     * <pre>
     *   regex  ::= alt
     *   alt    ::= concat ( '|' concat )*
     *   concat ::= quant *                              -- empty concat = empty-string regex
     *   quant  ::= atom ( '*' | '+' | '?' )?
     *   atom   ::= LIT | '.' | '\' ANY | '(' regex ')' | '[' charclass ']'
     *   charclass ::= ( LIT | LIT '-' LIT )+            -- no negation, no \d/\w/\s
     * </pre>
     */
    @CompileStatic
    private static class RegexParser {
        final String src
        int pos = 0
        final SmtSession session
        final Object strSort

        RegexParser(String src, SmtSession session) {
            this.src = src
            this.session = session
            this.strSort = session.declareSort('String')
        }

        private char peek() { src.charAt(pos) }
        private boolean done() { pos >= src.length() }
        private Object reLit(char c) {
            session.reToRe(session.litOfSort(strSort, String.valueOf(c)))
        }
        private Object reLitStr(String s) {
            session.reToRe(session.litOfSort(strSort, s))
        }

        /** Phase 47d — {@code \d} → range {@code '0'..'9'}. */
        private Object reDigit() {
            session.reRange(
                session.litOfSort(strSort, '0'),
                session.litOfSort(strSort, '9'))
        }

        /** Phase 47d — {@code \w} → {@code [a-zA-Z0-9_]}. */
        private Object reWordChar() {
            Object lower = session.reRange(session.litOfSort(strSort, 'a'), session.litOfSort(strSort, 'z'))
            Object upper = session.reRange(session.litOfSort(strSort, 'A'), session.litOfSort(strSort, 'Z'))
            Object digit = reDigit()
            Object underscore = reLitStr('_')
            session.reUnion(session.reUnion(session.reUnion(lower, upper), digit), underscore)
        }

        /** Phase 47d — {@code \s} → ASCII whitespace set (space, tab, LF, CR, FF, VT). */
        private Object reSpace() {
            Object[] chars = [
                reLitStr(' '),
                reLitStr('\t'),
                reLitStr('\n'),
                reLitStr('\r'),
                reLitStr('\f'),
                reLitStr(''),   // vertical tab
            ]
            Object acc = chars[0]
            for (int i = 1; i < chars.length; i++) acc = session.reUnion(acc, chars[i])
            acc
        }

        /** Phase 47d — single-char complement: any one character not in {@code re}. */
        private Object reNotSingle(Object re) {
            session.reIntersect(session.reAllChar(), session.reComplement(re))
        }

        Object parseAlt() {
            Object first = parseConcat()
            while (!done() && peek() == '|' as char) {
                pos++
                Object next = parseConcat()
                first = session.reUnion(first, next)
            }
            first
        }

        Object parseConcat() {
            Object acc = null
            while (!done() && peek() != ')' as char && peek() != '|' as char) {
                Object q = parseQuantified()
                acc = (acc == null) ? q : session.reConcat(acc, q)
            }
            // Empty concat → the empty-string regex (matches only "").
            acc == null ? reLitStr('') : acc
        }

        Object parseQuantified() {
            Object atom = parseAtom()
            if (!done()) {
                char c = peek()
                if (c == '*' as char) { pos++; return session.reStar(atom) }
                if (c == '+' as char) { pos++; return session.rePlus(atom) }
                if (c == '?' as char) { pos++; return session.reOption(atom) }
                // Phase 47d — {@code {n}}, {@code {n,m}}, {@code {n,}} quantified ranges.
                if (c == '{' as char) return parseBraceQuantified(atom)
            }
            atom
        }

        /** Phase 47d — parse {@code {n}} / {@code {n,m}} / {@code {n,}} following an atom. */
        Object parseBraceQuantified(Object atom) {
            pos++   // consume '{'
            int lo = parseInt()
            int hi = lo
            boolean hasHi = false
            boolean openUpper = false
            if (!done() && peek() == ',' as char) {
                pos++
                if (!done() && peek() == '}' as char) {
                    openUpper = true
                } else {
                    hi = parseInt()
                    hasHi = true
                }
            }
            if (done() || peek() != '}' as char) throw new IllegalStateException('expected }')
            pos++
            if (openUpper) return session.reLoopAtLeast(atom, lo)
            return session.reLoop(atom, lo, hasHi ? hi : lo)
        }

        private int parseInt() {
            int start = pos
            while (!done() && Character.isDigit(peek())) pos++
            if (start == pos) throw new IllegalStateException('expected digits')
            Integer.parseInt(src.substring(start, pos))
        }

        Object parseAtom() {
            if (done()) throw new IllegalStateException('unexpected end')
            char c = peek()
            if (c == '(' as char) {
                pos++
                Object inner = parseAlt()
                if (done() || peek() != ')' as char) throw new IllegalStateException('expected )')
                pos++
                return inner
            }
            if (c == '[' as char) {
                pos++
                return parseCharClass()
            }
            if (c == '.' as char) {
                pos++
                return session.reAllChar()
            }
            if (c == '\\' as char) {
                pos++
                if (done()) throw new IllegalStateException('dangling backslash')
                char esc = src.charAt(pos)
                pos++
                // Phase 47d — predefined character classes. Each is a one-character regex; the
                // capital-letter variants are single-char complements.
                if (esc == 'd' as char) return reDigit()
                if (esc == 'D' as char) return reNotSingle(reDigit())
                if (esc == 'w' as char) return reWordChar()
                if (esc == 'W' as char) return reNotSingle(reWordChar())
                if (esc == 's' as char) return reSpace()
                if (esc == 'S' as char) return reNotSingle(reSpace())
                // Word-boundary anchors aren't a single-character regex; honest skip.
                if (esc == 'b' as char || esc == 'B' as char) {
                    throw new IllegalStateException('word boundary not supported')
                }
                return reLit(esc)
            }
            // Phase 47d — anchors. {@code String.matches} is whole-string-anchored, so a top-
            // level {@code ^}/{@code $} is redundant. Translate as the empty-string regex
            // (matches only ""), which composes correctly with concat: {@code ^foo} becomes
            // empty + foo = foo.
            if (c == '^' as char || c == '$' as char) {
                pos++
                return reLitStr('')
            }
            if (c == ')' as char || c == ']' as char || c == '|' as char || c == '*' as char ||
                c == '+' as char || c == '?' as char) {
                throw new IllegalStateException('unexpected metacharacter')
            }
            if (c == '{' as char) {
                throw new IllegalStateException('quantified range without preceding atom')
            }
            pos++
            reLit(c)
        }

        Object parseCharClass() {
            // Phase 47d — negated character class {@code [^…]}: parse the positive class
            // inside, then complement-and-intersect with allchar to get "any single character
            // that isn't in the class".
            boolean negated = false
            if (!done() && peek() == '^' as char) {
                negated = true
                pos++
            }
            Object acc = null
            while (!done() && peek() != ']' as char) {
                char c = peek()
                pos++
                // {@code c-c} range, but only if the dash isn't the last char of the class.
                if (!done() && peek() == '-' as char && pos + 1 < src.length() &&
                    src.charAt(pos + 1) != ']' as char) {
                    pos++   // consume '-'
                    char hi = peek()
                    pos++
                    Object lo = session.litOfSort(strSort, String.valueOf(c))
                    Object hiStr = session.litOfSort(strSort, String.valueOf(hi))
                    Object range = session.reRange(lo, hiStr)
                    acc = (acc == null) ? range : session.reUnion(acc, range)
                } else {
                    Object single = reLit(c)
                    acc = (acc == null) ? single : session.reUnion(acc, single)
                }
            }
            if (done() || peek() != ']' as char) throw new IllegalStateException('expected ]')
            pos++
            if (acc == null) throw new IllegalStateException('empty character class')
            negated ? reNotSingle(acc) : acc
        }
    }

    /** Phase 41 — true if {@code name} is a List-typed parameter/field (use bcount, not count). */
    boolean isListName(String name) {
        if (name == null) return false
        // Strip old$ for snapshot keys — they still refer to a List.
        String bare = name.startsWith('old$') ? name.substring('old$'.length()) : name
        listNames.contains(bare)
    }

    /**
     * The Z3 sort for a Groovy element type. Int / Integer → the built-in Int sort (the existing
     * default); String → the uninterpreted {@code String!Sort}; an enum class → a per-class
     * uninterpreted sort named after the enum's nameWithoutPackage. {@code null} or any other type
     * falls back to Int (the default-Int policy preserves today's behaviour for unannotated
     * receivers). Used by {@link #setElementSort} / {@link #mapKeySort} / {@link #mapValueSort} /
     * {@link #listElementSort}.
     */
    /**
     * Does a pure function's return type warrant a non-Int range sort for its shared symbol? True for an
     * enum (the security-lattice case) or a Boolean predicate; everything else keeps the historic Int-only
     * declaration path, so existing Int/recurrence helpers are unaffected.
     */
    private static boolean isNonIntPureRange(ClassNode t) {
        if (t == null) return false
        String n = t.name
        n == 'boolean' || n == 'java.lang.Boolean' || t.isEnum() || isEnumLikeType(t)
    }

    private Object sortFor(ClassNode t) {
        if (t == null) return session.intSort()
        String name = t.name
        if (name == 'java.lang.String') return session.declareSort('String')
        if (isDecimalElementType(t)) return session.realSort()   // Phase 70 — List<BigDecimal> contents
        if (isFpElementType(t)) return session.fpSort(isFpDoubleType(t))   // Phase 77 — double/float contents
        if (name == 'boolean' || name == 'java.lang.Boolean') return session.boolSort()
        if (isIntLikeType(t)) return session.intSort()
        if (t.isEnum() || isEnumLikeType(t)) return session.declareSort(enumSortName(t))
        FieldNode cf = wrapperContentField(t)   // Phase B — a wrapper carrier is a one-constructor datatype
        if (cf != null) return session.wrapperSort(t.nameWithoutPackage, contentSortFor(cf))
        Object[] mc = multiCaseInfo(t)          // Phase M-C — a two-case carrier (Some|None) is a two-constructor datatype
        if (mc != null) return multiCaseSort(t, (FieldNode) mc[2])
        List<FieldNode> rc = recordComponents(t) // Phase 142 — a multi-component record is a one-constructor N-field datatype
        if (rc != null) return recordDatatypeSort(t, rc)
        session.intSort()   // default — preserves today's Int-only behaviour for unrecognised types
    }

    /** Phase 142 — declare/get the one-constructor N-field datatype sort for a multi-component record. */
    private Object recordDatatypeSort(ClassNode cn, List<FieldNode> comps) {
        String name = cn.nameWithoutPackage
        List<Object[]> ctorFields = new ArrayList<Object[]>()
        for (FieldNode f : comps) ctorFields.add([f.name, sortFor(f.type)] as Object[])
        session.datatypeSort(name, [[name, ctorFields] as Object[]] as List<Object[]>)
    }

    /** Phase M-C — declare/get the {@code Some(content) | None} datatype sort for a recognised two-case carrier. */
    private Object multiCaseSort(ClassNode carrier, FieldNode contentField) {
        Object cSort = contentSortFor(contentField)
        session.datatypeSort(carrier.nameWithoutPackage, [
            ['Some', [[contentField.name, cSort] as Object[]]] as Object[],
            ['None', []] as Object[]
        ])
    }

    /** Phase C — the SMT sort of a wrapper carrier's content. An {@code Object} content field shares the
     *  {@code f.apply} value sort ({@code declareSort('Object')}) so the bind/map laws (carrier ∘ apply) compose;
     *  a concretely-typed field keeps its natural sort. */
    private Object contentSortFor(FieldNode cf) {
        (cf?.type != null && cf.type.name == 'java.lang.Object') ? session.declareSort('Object') : sortFor(cf.type)
    }

    /** Phase B / 133 — the single content field of a recognised wrapper carrier (one non-static, final field),
     *  or null. Recognised either as a {@code @Monadic} carrier or as a single-component **record** (Phase 133):
     *  both are exactly a one-constructor immutable value, modelled as a one-constructor Z3 datatype so the
     *  construct/read round-trip (`new R(v).f == v`) holds by datatype theory. Static: reads only the ClassNode. */
    static FieldNode wrapperContentField(ClassNode cn) {
        if (cn == null) return null
        List<AnnotationNode> anns = cn.annotations
        boolean monadic = anns != null && anns.any { it?.classNode?.name?.endsWith('Monadic') }
        if (!monadic && !isRecordClass(cn)) return null
        List<FieldNode> inst = new ArrayList<FieldNode>()
        List<FieldNode> fs = cn.fields
        if (fs != null) for (FieldNode f : fs) if (!f.isStatic()) inst.add(f)
        if (inst.size() != 1) return null
        FieldNode f = inst.get(0)
        f.isFinal() ? f : null
    }

    /** Phase 133 — true for a Groovy/Java {@code record} (its components are final, so a single-component record
     *  is a one-constructor immutable value). Detected by its implicit {@code java.lang.Record} supertype. */
    static boolean isRecordClass(ClassNode cn) {
        if (cn == null) return false
        ClassNode sc = cn.getUnresolvedSuperClass(false)
        if (sc != null && sc.name == 'java.lang.Record') return true
        sc = cn.superClass
        sc != null && sc.name == 'java.lang.Record'
    }

    /** The resolved wrapper-carrier ClassNode for a simple name in scope (from {@link #carrierTypes}), or null —
     *  used to recover a re-parsed contract's unresolved {@code new Res(a)} type. */
    private ClassNode carrierByName(String simpleName) {
        ClassNode cn = carrierTypes.get(simpleName)
        cn != null && (wrapperContentField(cn) != null || recordComponents(cn) != null) ? cn : null
    }

    /** The carrier ClassNode of a receiver expression: a carrier-typed variable, a freshly constructed carrier,
     *  a bind function's application {@code f.apply(x)} (returns the carrier), or a chained {@code recv.bind/map(…)}
     *  (also returns the carrier). The last two (Phase D) let an associativity nest like
     *  {@code m.chain(f).chain(g)} / {@code f.apply(x).chain(g)} resolve. */
    private ClassNode carrierTypeOf(Expression obj) {
        if (obj instanceof VariableExpression) {
            ClassNode t = scalarTypes.get(((VariableExpression) obj).name)
            return (wrapperContentField(t) != null || multiCaseInfo(t) != null || recordComponents(t) != null) ? t : null
        }
        if (obj instanceof ConstructorCallExpression && ((ConstructorCallExpression) obj).type != null)
            return carrierByName(((ConstructorCallExpression) obj).type.nameWithoutPackage)
        if (obj instanceof MethodCallExpression) {
            MethodCallExpression mc = (MethodCallExpression) obj
            String mm = mc.methodAsString
            // Phase M-C — some(v)/none() factory of a two-case carrier returns that carrier
            Object[] fac = carrierFactoryMatch(mm, argList(mc).size())
            if (fac != null) return (ClassNode) fac[0]
            // f.apply(x) where f is a Function declared to return a carrier
            if (mm == 'apply' && mc.objectExpression instanceof VariableExpression) {
                ClassNode rt = functionReturnTypes.get(((VariableExpression) mc.objectExpression).name)
                if (rt != null && isCarrier(rt)) return rt
            }
            // recv.bind(…) / recv.map(…) returns recv's carrier type
            ClassNode rct = carrierTypeOf(mc.objectExpression)
            if (rct != null && (mm == bindMethodName(rct) || mm == mapMethodName(rct))) return rct
        }
        null
    }

    /** Phase 145 — select a carrier's content/component field directly from an already-computed handle (the
     *  handle analogue of the {@code r.field} PropertyExpression translation below). A chained call's result
     *  (`a.f().g()`, where the receiver {@code a.f()} is a value with no nameable expression) needs its component
     *  fields bound for the next call's contract; this reads them off the fresh handle. Mirrors the wrapper /
     *  two-case / record cases of the property translation. Returns null if {@code prop} isn't a field of {@code mt}. */
    Object carrierField(ClassNode mt, String prop, Object handle) {
        if (mt == null || prop == null || handle == null) return null
        FieldNode cf = wrapperContentField(mt)
        if (cf != null && cf.name == prop) return session.wrapperContent(mt.nameWithoutPackage, contentSortFor(cf), handle)
        Object[] mc = multiCaseInfo(mt)
        if (mc != null && ((FieldNode) mc[2]).name == prop) {
            sortFor(mt); return session.datatypeSelect(mt.nameWithoutPackage, 'Some', prop, handle)
        }
        List<FieldNode> rc = recordComponents(mt)
        if (rc != null && rc.any { it.name == prop }) {
            sortFor(mt); return session.datatypeSelect(mt.nameWithoutPackage, mt.nameWithoutPackage, prop, handle)
        }
        null
    }

    /** True if {@code pe} reads a carrier's content field (`m.v` for a wrapper, `m.value` for a two-case carrier). */
    private boolean isCarrierContentRead(PropertyExpression pe) {
        ClassNode ct = carrierTypeOf(pe.objectExpression)
        if (ct == null) return false
        FieldNode cf = wrapperContentField(ct)
        if (cf != null) return cf.name == pe.propertyAsString
        Object[] mc = multiCaseInfo(ct)
        if (mc != null) return ((FieldNode) mc[2]).name == pe.propertyAsString
        List<FieldNode> rc = recordComponents(ct)   // Phase 142 — a multi-component record's `.field` read
        rc != null && rc.any { it.name == pe.propertyAsString }
    }

    // ---- Phase M-C: recognise a tightly-scoped two-case carrier (Some(content) | None) ----

    /** Info for a recognised two-case {@code @Monadic} carrier: {@code [someFactory(String), noneFactory(String),
     *  contentField(FieldNode)]}, or null. Tightly scoped: {@code @Monadic}, exactly two non-static fields (one
     *  {@code boolean} discriminant + one content), a static 1-arg unit/some factory and a static 0-arg none
     *  factory, both returning the carrier. (A single-field wrapper is the Phase-B path and is excluded here.) */
    /** True if {@code cn} is a recognised carrier — a single-field wrapper (Phase B) or a two-case carrier (M-C). */
    static boolean isCarrier(ClassNode cn) { wrapperContentField(cn) != null || multiCaseInfo(cn) != null || recordComponents(cn) != null }

    /**
     * Phase 142 — the components of a MULTI-component record (a {@code record} with ≥2 non-static final fields):
     * a one-constructor immutable product, modelled as an N-field Z3 datatype so {@code new R(a, b).f == a} holds
     * by datatype theory. A single-component record stays on the wrapper path ({@link #wrapperContentField}); a
     * non-record, or a record with fewer than two fields, returns null. This is the record analogue of TupleN.
     */
    static List<FieldNode> recordComponents(ClassNode cn) {
        if (cn == null || !isRecordClass(cn)) return null
        List<FieldNode> inst = new ArrayList<FieldNode>()
        List<FieldNode> fs = cn.fields
        if (fs != null) for (FieldNode f : fs) if (!f.isStatic()) inst.add(f)
        if (inst.size() < 2) return null
        for (FieldNode f : inst) if (!f.isFinal()) return null
        inst
    }

    static Object[] multiCaseInfo(ClassNode cn) {
        if (cn == null || wrapperContentField(cn) != null || monadicAnn(cn) == null) return null
        List<FieldNode> inst = new ArrayList<FieldNode>()
        for (FieldNode f : (cn.fields ?: [])) if (!f.isStatic()) inst.add(f)
        if (inst.size() != 2) return null
        FieldNode boolF = null, contentF = null
        for (FieldNode f : inst) {
            String tn = f.type?.name
            if (tn == 'boolean' || tn == 'java.lang.Boolean') boolF = f else contentF = f
        }
        if (boolF == null || contentF == null) return null
        String someName = monadicMember(cn, 'unit', 'some')
        if (staticFactory(cn, someName, 1) == null) return null
        MethodNode noneM = staticFactory(cn, null, 0)
        noneM != null ? [someName, noneM.name, contentF, boolF] as Object[] : null
    }

    /** A static method on {@code cn} returning the carrier itself, with the given arity; {@code name} null matches
     *  any name (used to find the nullary {@code none} factory). */
    private static MethodNode staticFactory(ClassNode cn, String name, int arity) {
        for (MethodNode mn : (cn.methods ?: [])) {
            if (mn.isStatic() && mn.parameters.length == arity && (name == null || mn.name == name) &&
                mn.returnType?.nameWithoutPackage == cn.nameWithoutPackage) return mn
        }
        null
    }

    /** If {@code methodName}/{@code arity} is the some (1-arg) or none (0-arg) factory of a two-case carrier in
     *  scope, return {@code [carrier(ClassNode), ctorName('Some'|'None'), contentField(FieldNode)]}; else null. */
    private Object[] carrierFactoryMatch(String methodName, int arity) {
        for (ClassNode cn : carrierTypes.values()) {
            Object[] mc = multiCaseInfo(cn)
            if (mc == null) continue
            if (arity == 1 && mc[0] == methodName) return [cn, 'Some', mc[2]] as Object[]
            if (arity == 0 && mc[1] == methodName) return [cn, 'None', mc[2]] as Object[]
        }
        null
    }

    // ---- Phase M-D: case-split flatMap/map bodies (`present ? someCase : this`) for a two-case carrier ----

    private static boolean isFieldRef(Expression e, String name) {
        if (e instanceof BooleanExpression) e = ((BooleanExpression) e).expression
        if (e instanceof VariableExpression) return ((VariableExpression) e).name == name
        (e instanceof PropertyExpression && isThisExpr(((PropertyExpression) e).objectExpression) &&
            ((PropertyExpression) e).propertyAsString == name)
    }
    private static boolean isThisExpr(Expression e) {
        e instanceof VariableExpression && ((VariableExpression) e).name == 'this'
    }
    /** The true-branch of a `<discriminant> ? trueExpr : this` body (clean snapshot), or null. */
    private static Expression caseSplitTrueExpr(MethodNode mn, String discrimName) {
        Expression body = soleReturnExpr(mn)
        if (!(body instanceof TernaryExpression)) return null
        TernaryExpression t = (TernaryExpression) body
        (isFieldRef(t.booleanExpression, discrimName) && isThisExpr(t.falseExpression)) ? t.trueExpression : null
    }
    // A factory call in a resolved method body is a StaticMethodCallExpression (`Maybe.some(…)`); in a re-parsed
    // contract it's a MethodCallExpression (`some(…)`). These read either form uniformly.
    private static String callName(Expression e) {
        if (e instanceof StaticMethodCallExpression) return ((StaticMethodCallExpression) e).method
        if (e instanceof MethodCallExpression) return ((MethodCallExpression) e).methodAsString
        null
    }
    private static List<Expression> callArgs(Expression e) {
        Expression a = (e instanceof StaticMethodCallExpression) ? ((StaticMethodCallExpression) e).arguments :
                       (e instanceof MethodCallExpression) ? ((MethodCallExpression) e).arguments : null
        (a instanceof ArgumentListExpression) ? ((ArgumentListExpression) a).expressions : Collections.<Expression>emptyList()
    }
    /** {@code factory(param.apply(content))} — a Some-wrap of the mapped value. */
    private static boolean isFactoryOfApply(Expression e, String factory, String param, String content) {
        if (callName(e) != factory) return false
        List<Expression> as = callArgs(e)
        as.size() == 1 && isApplyOnParamToField(as.get(0), param, content)
    }
    /** A nullary {@code factory()} call (the none-wrap). */
    private static boolean isNullaryFactory(Expression e, String factory) {
        callName(e) == factory && callArgs(e).isEmpty()
    }
    /** {@code param.apply(content) == null}. */
    private static boolean isApplyEqNull(Expression e, String param, String content) {
        if (e instanceof BooleanExpression) e = ((BooleanExpression) e).expression
        if (!(e instanceof BinaryExpression)) return false
        BinaryExpression b = (BinaryExpression) e
        if (b.operation.type != Types.COMPARE_EQUAL) return false
        boolean lnull = b.rightExpression instanceof ConstantExpression && ((ConstantExpression) b.rightExpression).value == null
        Expression other = lnull ? b.leftExpression : b.rightExpression
        boolean otherNull = b.leftExpression instanceof ConstantExpression && ((ConstantExpression) b.leftExpression).value == null
        (lnull || otherNull) && isApplyOnParamToField(lnull ? b.leftExpression : b.rightExpression, param, content)
    }

    /** Phase M-D — verify a carrier's bind is the lawful two-case shape `present ? (C) f.apply(content) : this`. */
    private static boolean isMultiCaseBind(ClassNode ct, String name, Object[] mc) {
        MethodNode mn = singleArgMethod(ct, name)
        if (mn == null) return false
        Expression t = caseSplitTrueExpr(mn, ((FieldNode) mc[3]).name)
        t != null && isApplyOnParamToField(t, mn.parameters[0].name, ((FieldNode) mc[2]).name)
    }
    /** Phase M-D — a carrier's map kind: 'vavr' (`present ? some(g(content)) : this`), 'optional' (`present ?
     *  (g(content)==null ? none() : some(g(content))) : this`), or null. The discriminator for the functor law. */
    private static String multiCaseMapKind(ClassNode ct, String name, Object[] mc) {
        MethodNode mn = singleArgMethod(ct, name)
        if (mn == null) return null
        Expression t = caseSplitTrueExpr(mn, ((FieldNode) mc[3]).name)
        if (t == null) return null
        String p = mn.parameters[0].name, content = ((FieldNode) mc[2]).name, some = (String) mc[0], none = (String) mc[1]
        if (isFactoryOfApply(t, some, p, content)) return 'vavr'
        if (t instanceof TernaryExpression) {
            TernaryExpression tt = (TernaryExpression) t
            if (isApplyEqNull(tt.booleanExpression, p, content) && isNullaryFactory(tt.trueExpression, none) &&
                isFactoryOfApply(tt.falseExpression, some, p, content)) return 'optional'
        }
        null
    }
    /** Phase M-D — the discriminant is wired canonically: {@code some} constructs with the discriminant arg
     *  {@code true}, {@code none} with {@code false}, so {@code present(m) ⟺ is$Some(m)} (model soundness). */
    private static boolean isCanonicalWiring(ClassNode cn, Object[] mc) {
        ctorBoolArg(staticFactory(cn, (String) mc[0], 1), Boolean.TRUE) &&
        ctorBoolArg(staticFactory(cn, (String) mc[1], 0), Boolean.FALSE)
    }
    private static boolean ctorBoolArg(MethodNode factory, Boolean expected) {
        if (factory == null) return false
        Expression body = soleReturnExpr(factory)
        if (!(body instanceof ConstructorCallExpression)) return false
        List<Expression> as = (((ConstructorCallExpression) body).arguments instanceof ArgumentListExpression) ?
            ((ArgumentListExpression) ((ConstructorCallExpression) body).arguments).expressions : Collections.<Expression>emptyList()
        // the boolean discriminant is the first constructor argument in the canonical idiom
        !as.isEmpty() && as.get(0) instanceof ConstantExpression && ((ConstantExpression) as.get(0)).value == expected
    }

    private static final Set<String> NON_NULL_NAMES = ['NonNull', 'NotNull', 'Nonnull', 'MonotonicNonNull'] as Set<String>
    /** Phase M-E — true if the content field (or its type use) carries a NullChecker-style @NonNull annotation
     *  (the Optional contract: {@code Some} never holds null). */
    static boolean hasNonNullContent(FieldNode f) {
        annHasNonNull(f?.annotations) || annHasNonNull(f?.type?.annotations)
    }
    private static boolean annHasNonNull(List<AnnotationNode> anns) {
        if (anns == null) return false
        for (AnnotationNode a : anns) {
            String n = a?.classNode?.nameWithoutPackage
            if (n != null && NON_NULL_NAMES.contains(n.substring(n.lastIndexOf('$') + 1))) return true
        }
        false
    }

    /** Phase M-E — for a *specific* carrier variable {@code handle} (a param), assume the @NonNull-content contract
     *  {@code is$Some(handle) ⟹ content(handle) != null$} (mint-once per name). A *ground* assumption, not a
     *  universal axiom — it constrains the param without forcing every constructed {@code Some(p(c))} subterm
     *  non-null (which would wrongly prove functor composition). Sound: NullChecker enforces the @NonNull. */
    private final Set<String> nnContentAsserted = new HashSet<String>()
    private void assumeNonNullContent(String name, ClassNode declared, Object handle) {
        Object[] mc = multiCaseInfo(declared)
        if (mc == null || !hasNonNullContent((FieldNode) mc[2]) || !nnContentAsserted.add(name)) return
        FieldNode cf = (FieldNode) mc[2]
        String tn = declared.nameWithoutPackage
        Object isSome = session.datatypeRecognize(tn, 'Some', handle)
        Object content = session.datatypeSelect(tn, 'Some', cf.name, handle)
        session.assertExpr(session.implies(isSome,
            session.not(session.eq(content, session.nullValue(contentSortFor(cf))))))
    }

    // ---- Phase C: the bind/map method names a carrier declares, and whether their bodies are Identity-shaped ----

    private static AnnotationNode monadicAnn(ClassNode ct) {
        ct?.annotations?.find { it?.classNode?.name?.endsWith('Monadic') }
    }
    private static String monadicMember(ClassNode ct, String member, String dflt) {
        Expression e = monadicAnn(ct)?.getMember(member)
        (e instanceof ConstantExpression && ((ConstantExpression) e).value instanceof String &&
            !((String) ((ConstantExpression) e).value).isEmpty()) ? (String) ((ConstantExpression) e).value : dflt
    }
    private static String bindMethodName(ClassNode ct) { monadicMember(ct, 'bind', 'flatMap') }
    private static String mapMethodName(ClassNode ct)  { monadicMember(ct, 'map', 'map') }

    /** Phase 136 — true if {@code cn} is a wrapper carrier whose bind AND map are the verified Identity shapes,
     *  i.e. the carrier groovy-verify can model. The auto-synthesis gates on this (others are out of scope). */
    static boolean isIdentityWrapperCarrier(ClassNode cn) {
        FieldNode cf = wrapperContentField(cn)
        cf != null && isIdentityBind(cn, bindMethodName(cn), cf) && isIdentityMap(cn, mapMethodName(cn), cf)
    }

    /** Phase M-E — true if {@code cn} is a modellable two-case carrier (canonical wiring, lawful case-split bind,
     *  a recognised map kind — Vavr or Optional). The auto-synthesis gates on this; the *verdict* (whether the
     *  laws then hold) is the synthesis's job — an Optional-style carrier is modellable yet refutes functor
     *  composition. The some-factory name (its `unit`) is {@code multiCaseInfo(cn)[0]}. */
    static boolean isModellableTwoCaseCarrier(ClassNode cn) {
        Object[] mc = multiCaseInfo(cn)
        mc != null && isCanonicalWiring(cn, mc) &&
            isMultiCaseBind(cn, bindMethodName(cn), mc) && multiCaseMapKind(cn, mapMethodName(cn), mc) != null
    }

    /** Phase M-E — the some-factory (unit) name of a recognised two-case carrier, or null. */
    static String someFactoryName(ClassNode cn) {
        Object[] mc = multiCaseInfo(cn)
        mc != null ? (String) mc[0] : null
    }

    /** The single-argument method named {@code name} on {@code ct}, or null. */
    private static MethodNode singleArgMethod(ClassNode ct, String name) {
        if (ct == null) return null
        for (MethodNode mn : (ct.methods ?: [])) if (mn.name == name && mn.parameters.length == 1) return mn
        null
    }
    /** The (implicit-return) value expression of a single-statement method body, or null. Reads the clean
     *  pre-contract snapshot when groovy-contracts has rewritten the body (e.g. a `@Requires` guard). */
    private static Expression soleReturnExpr(MethodNode mn) {
        if (mn == null) return null
        Statement code = (Statement) mn.getNodeMetaData(ContractExpansionTransform.ORIGINAL_BODY_KEY)
        if (code == null) code = mn.code
        if (code instanceof BlockStatement) {
            List<Statement> ss = ((BlockStatement) code).statements
            if (ss.size() != 1) return null
            code = ss.get(0)
        }
        if (code instanceof ReturnStatement) return ((ReturnStatement) code).expression
        if (code instanceof ExpressionStatement) return ((ExpressionStatement) code).expression
        null
    }
    /** True if {@code e} is {@code <paramName>.apply(<fieldName>)}. */
    private static boolean isApplyOnParamToField(Expression e, String paramName, String fieldName) {
        if (e instanceof CastExpression) e = ((CastExpression) e).expression
        if (!(e instanceof MethodCallExpression)) return false
        MethodCallExpression mc = (MethodCallExpression) e
        if (mc.methodAsString != 'apply' || !(mc.objectExpression instanceof VariableExpression) ||
            ((VariableExpression) mc.objectExpression).name != paramName) return false
        List<Expression> as = argList(mc)
        as.size() == 1 && as.get(0) instanceof VariableExpression && ((VariableExpression) as.get(0)).name == fieldName
    }
    /** The single value expression of a closure literal's body, or null. */
    private static Expression soleClosureExpr(ClosureExpression cl) {
        Statement code = cl?.code
        if (code instanceof BlockStatement) {
            List<Statement> ss = ((BlockStatement) code).statements
            if (ss.size() != 1) return null
            code = ss.get(0)
        }
        if (code instanceof ReturnStatement) return ((ReturnStatement) code).expression
        if (code instanceof ExpressionStatement) return ((ExpressionStatement) code).expression
        null
    }

    /** Phase C — apply a function-valued argument to {@code arg}: an uninterpreted-function symbol for a named
     *  function (the bind/map of left identity), or beta-reduction for a single-parameter closure literal — which
     *  is how the {@code unit} ({@code x -> new C(x)}) and {@code identity} ({@code x -> x}) functions of the
     *  right-/functor-identity laws reach a carrier. Returns null for forms not yet modelled (e.g. method refs). */
    /** The SMT range of {@code f.apply(...)} from {@code f}'s declared return type: an {@code Object} return uses
     *  the shared value sort (not the Int default), a carrier return its datatype, anything else its natural sort;
     *  an unknown return type falls back to {@code defaultRange}. */
    private Object functionRange(String fname, Object defaultRange) {
        ClassNode rt = functionReturnTypes.get(fname)
        if (rt == null) return defaultRange
        if (rt.name == 'java.lang.Object') return session.declareSort('Object')
        sortFor(rt)
    }

    private Object applyFunction(Expression fexpr, Object arg, Object defaultRange) {
        if (fexpr instanceof VariableExpression) {
            String fn = ((VariableExpression) fexpr).name
            return session.applyUF('apply$' + fn, [arg], functionRange(fn, defaultRange))
        }
        if (fexpr instanceof ClosureExpression) {
            ClosureExpression cl = (ClosureExpression) fexpr
            Parameter[] ps = cl.parameters
            Expression body = soleClosureExpr(cl)
            if (ps != null && ps.length == 1 && body != null) {
                Map<String, Object> b = new LinkedHashMap<String, Object>()
                b.put(ps[0].name, arg)
                return translateWith(body, b)
            }
        }
        null
    }

    /** Phase C — verify (not assume) a carrier's bind is the Identity shape `(C) f.apply(field)`. */
    private static boolean isIdentityBind(ClassNode ct, String name, FieldNode cf) {
        MethodNode mn = singleArgMethod(ct, name)
        mn != null && isApplyOnParamToField(soleReturnExpr(mn), mn.parameters[0].name, cf.name)
    }
    /** Phase C — verify a carrier's map is the Identity shape `new C(p.apply(field))`. */
    private static boolean isIdentityMap(ClassNode ct, String name, FieldNode cf) {
        MethodNode mn = singleArgMethod(ct, name)
        if (mn == null) return false
        Expression body = soleReturnExpr(mn)
        if (!(body instanceof ConstructorCallExpression)) return false
        ConstructorCallExpression cce = (ConstructorCallExpression) body
        if (cce.type?.nameWithoutPackage != ct.nameWithoutPackage) return false
        List<Expression> cargs = (cce.arguments instanceof ArgumentListExpression) ?
            ((ArgumentListExpression) cce.arguments).expressions : Collections.<Expression>emptyList()
        cargs.size() == 1 && isApplyOnParamToField(cargs.get(0), mn.parameters[0].name, cf.name)
    }

    /**
     * The Z3 sort name for an enum class — its source-level simple name with any inner-class
     * binary-name prefix stripped (so {@code C$Color} → {@code Color}). The CONTRACT-side enum
     * literal {@code Color.RED} (re-parsed from text, unresolved receiver name "Color") and the
     * BODY-side {@code Color.RED} (resolved to the inner-class binary "C$Color") then agree on
     * the same sort. The known limitation: two enums with the same source-level name in different
     * outer classes collapse into one sort — acceptable for the spike's scale.
     */
    private static String enumSortName(ClassNode t) {
        String n = t.nameWithoutPackage
        int dollar = n.lastIndexOf('$')   // String-overload — finds the last '$' separator if present
        dollar >= 0 ? n.substring(dollar + 1) : n
    }

    private static boolean isIntLikeType(ClassNode t) {
        String n = t?.name
        n == 'int' || n == 'long' || n == 'short' || n == 'byte' || n == 'char' ||
            n == 'java.lang.Integer' || n == 'java.lang.Long' || n == 'java.lang.Short' ||
            n == 'java.lang.Byte' || n == 'java.lang.Character'
    }

    /**
     * Phase 98b — Groovy truth of the first operand {@code a} of an Elvis {@code a ?: b}, as the {@code ite}
     * condition. Type-directed and sound per kind: integral {@code a != 0}; {@code String} non-null ∧
     * non-empty (seq length); a plain object reference non-null. Returns null (caller skips loudly) for
     * anything whose truth this doesn't model — a non-nameable operand (no nullity oracle), a decimal/boolean,
     * an array, a class that customises {@code asBoolean()} (its truth is whatever that returns, not non-null),
     * or a collection/{@code Map} (no single-term SMT value to thread through the {@code ite} — the operand
     * doesn't translate, so the Elvis skips before reaching here).
     */
    private Object groovyTruth(Expression operand, Object aTerm) {
        ClassNode t = operand.getType()
        if (isIntLikeType(t)) return session.ne(aTerm, session.intLit(0L))
        if (!(operand instanceof VariableExpression)) return null      // need a name for the nullity oracle
        String name = ((VariableExpression) operand).name
        if (isStringReceiver(operand)) {
            return session.and([session.not(nullityOf(name)),
                                session.gt(session.stringLength(aTerm), session.intLit(0L))])
        }
        if (isPlainObjectTruth(t)) return session.not(nullityOf(name))
        null
    }

    private static boolean isCollectionOrMapType(ClassNode t) {
        if (t == null) return false
        ClassNode coll = ClassHelper.make(Collection)
        ClassNode map = ClassHelper.make(Map)
        t == coll || t == map || t.implementsInterface(coll) || t.implementsInterface(map) || t.isDerivedFrom(coll)
    }

    /** Phase 98b — a reference whose Groovy truth is exactly non-null: not a primitive/number/boolean, not a
     *  String/GString or collection (those add non-emptiness), and not a class overriding {@code asBoolean()}. */
    private static boolean isPlainObjectTruth(ClassNode t) {
        if (t == null || t.isArray() || ClassHelper.isPrimitiveType(t)) return false
        String n = t.name
        if (n == 'java.lang.String' || n == 'groovy.lang.GString' || n == 'java.lang.Boolean' ||
            n == 'java.lang.Double' || n == 'java.lang.Float' || n == 'java.lang.Number' ||
            n == 'java.math.BigDecimal' || n == 'java.math.BigInteger') return false
        if (isIntLikeType(t) || isCollectionOrMapType(t)) return false
        try { if (!t.getMethods('asBoolean').isEmpty()) return false } catch (Throwable ignored) {}
        true
    }

    private static boolean isEnumLikeType(ClassNode t) {
        try {
            return t != null && t.superClass != null && t.superClass.name == 'java.lang.Enum'
        } catch (Throwable ignored) {
            return false
        }
    }

    /**
     * True if {@code name} matches an enum class that's been seen as a set/map/list element type
     * for the current method (Phase 27). Used by the default {@link #translate} path to recognise
     * a pre-resolution enum literal {@code Color.RED} (which parses as
     * PropertyExpression(VariableExpression("Color"), "RED")) outside the expected-sort dispatch
     * of {@link #translateInSort}. Computed lazily and cached on first use.
     */
    private Set<String> knownEnumNames = null
    /**
     * Phase 28 — if {@code e} is the shape {@code <EnumClass>.values()} (no arguments), return the
     * enum's constant count; null otherwise. Two AST shapes accepted: ClassExpression receiver
     * (post-resolution body) — count by walking the type's static-final fields; and
     * VariableExpression receiver (re-parsed contract) — look up the name in
     * {@link #enumDomainSizes} pre-populated by VerifyChecker. Lets a contract like
     * {@code @Requires({ k < Color.values().length })} fold to {@code k < 3} at translate time.
     */
    private Integer enumValuesCountFor(Expression e) {
        if (!(e instanceof MethodCallExpression)) return null
        MethodCallExpression mce = (MethodCallExpression) e
        if (mce.methodAsString != 'values') return null
        if (!argList(mce).isEmpty()) return null
        Expression recv = mce.objectExpression
        if (recv instanceof ClassExpression) {
            ClassNode t = ((ClassExpression) recv).type
            if (t != null && (t.isEnum() || isEnumLikeType(t))) {
                int count = countEnumConstants(t)
                return count > 0 ? count : null
            }
        }
        if (recv instanceof VariableExpression) {
            return enumDomainSizes.get(((VariableExpression) recv).name)
        }
        null
    }

    /**
     * Count the actual enum constants of {@code t} — fields with the JVM {@code ACC_ENUM}
     * modifier bit set. Filters out synthetic same-type fields Groovy adds (notably
     * {@code MIN_VALUE} / {@code MAX_VALUE}) and the array-typed {@code $VALUES}.
     */
    private static int countEnumConstants(ClassNode t) {
        int count = 0
        for (FieldNode f : t.fields) {
            if ((f.modifiers & 0x4000) != 0) count++   // 0x4000 = ACC_ENUM
        }
        count
    }

    /**
     * Assert that a freshly-minted enum-sorted scalar inhabits its enum's finite domain:
     * {@code v == c1 ∨ … ∨ cN} over the enum's constants. Z3 models an enum as an *open* uninterpreted
     * sort, so without this fact a parameter of type {@code L} could be some element outside the declared
     * constants — which silently defeats any property that holds only because the lattice is finite (e.g.
     * a two-element security lattice's join being an upper bound). Sound (the disjunction is always true)
     * and quantifier-free (asserted per scalar, not as a {@code ∀}), so no trigger fragility. Applies only
     * to enum-typed scalars in {@link #scalarTypes}; set/map element domains keep their own coverage axioms.
     */
    private void assertEnumDomainClosure(String name, Object sort, Object v) {
        ClassNode t = scalarTypes.get(name)
        if (t == null || !(t.isEnum() || isEnumLikeType(t))) return
        List<String> consts = enumConstantNames(t)
        if (consts.isEmpty()) return
        List<Object> disj = new ArrayList<Object>()
        for (String cn : consts) disj.add(session.eq(v, session.litOfSort(sort, cn)))
        session.assertExpr(disj.size() == 1 ? disj.get(0) : session.or(disj))
    }

    private boolean isKnownEnumName(String name) {
        if (knownEnumNames == null) {
            knownEnumNames = new HashSet<String>()
            setElementTypes.values().each { ClassNode t ->
                if (t != null && (t.isEnum() || isEnumLikeType(t))) knownEnumNames.add(enumSortName(t))
            }
            mapTypes.values().each { ClassNode[] pair ->
                if (pair[0] != null && (pair[0].isEnum() || isEnumLikeType(pair[0]))) knownEnumNames.add(enumSortName(pair[0]))
                if (pair[1] != null && (pair[1].isEnum() || isEnumLikeType(pair[1]))) knownEnumNames.add(enumSortName(pair[1]))
            }
            listElementTypes.values().each { ClassNode t ->
                if (t != null && (t.isEnum() || isEnumLikeType(t))) knownEnumNames.add(enumSortName(t))
            }
            scalarTypes.values().each { ClassNode t ->
                if (t != null && (t.isEnum() || isEnumLikeType(t))) knownEnumNames.add(enumSortName(t))
            }
        }
        knownEnumNames.contains(name)
    }

    /** The Z3 sort for the element type of a set receiver name, or Int if unknown / Int-element. */
    Object setElementSort(String name) { sortFor(setElementTypes.get(name)) }
    /** The Z3 sort for a map receiver's key type. */
    Object mapKeySort(String name) {
        ClassNode[] pair = mapTypes.get(name)
        sortFor(pair != null ? pair[0] : null)
    }
    /**
     * The Z3 sort for a map receiver's value type. For a nested-set map {@code Map<K, Set<V>>}
     * (Phase 36), this is the characteristic-array sort {@code Array<V, Int>} so the map's
     * declared handle has the right shape for {@code select(map, k)} to return an array term.
     */
    Object mapValueSort(String name) {
        ClassNode nestedElem = nestedSetValueTypes.get(name)
        if (nestedElem != null) {
            return session.arraySort(sortFor(nestedElem), session.intSort())
        }
        ClassNode[] pair = mapTypes.get(name)
        sortFor(pair != null ? pair[1] : null)
    }

    /**
     * Phase 36 — the inner set's element {@link ClassNode} for a {@code Map<_, Set<V>>}, or null
     * for a non-nested map. Used by the {@code m[k].contains}/{@code m[k].containsAll} lowerings
     * to route the argument through the right element sort.
     */
    ClassNode nestedSetElementTypeFor(String mapName) { nestedSetValueTypes.get(mapName) }
    /** The Z3 sort for the element type of a list receiver name, or Int if unknown. */
    Object listElementSort(String name) { sortFor(listElementTypes.get(name)) }

    /** The Z3 sort for a declared Groovy {@code ClassNode}, mirroring {@link #sortFor}. */
    Object sortForType(ClassNode t) { sortFor(t) }

    /**
     * Get-or-declare an integer SMT variable for a source-level name.
     * Idempotent — the same name returns the same handle, so a
     * variable referenced in both the path condition and the
     * precondition refers to the same SMT constant.
     */
    Object varFor(String name) {
        // Phase 45 — under a foreign-receiver context, a bare field reference (no qualifier)
        // resolves to the receiver-qualified entity. So {@code count} inside a translated copy
        // of {@code b}'s class invariant becomes {@code b$count}, distinct from this-class's
        // own {@code count}.
        if (receiverPrefix != null && receiverFields.contains(name)) {
            // Phase 89 — when the receiver is alias-modelled, a bare field reference in its assumed
            // invariant must read through the SAME identity-keyed map as an explicit `recv.field` read,
            // or the assumed invariant (`count >= 0`) wouldn't constrain the map read `select(count$, id)`.
            ClassNode ft = fieldTypeOfObjectParam(receiverPrefix, name)
            if (isAliasModeled(receiverPrefix) && ft != null && isIntLikeType(ft)) {
                return session.select(fieldMap(objectParams.get(receiverPrefix).name, name), objId(receiverPrefix))
            }
            return varForRaw(receiverPrefix + '$' + name)
        }
        // Phase 27 step 9 — a non-Int scalar (String, Enum) parameter/field dispatches to
        // varForOfSort, which caches in sortedEnv. The standard env stays Int-only so the
        // counterexample model walk (which iterates Z3Backend.vars) keeps pinning Int values
        // unchanged for everything else.
        ClassNode declared = scalarTypes.get(name)
        if (declared != null) {
            Object sort = sortFor(declared)
            if (sort != session.intSort()) {
                Object h = varForOfSort(name, sort)
                assumeNonNullContent(name, declared, h)   // Phase M-E — a @NonNull-content carrier param's content is non-null when Some
                return h
            }
        }
        // Phase 48b — boolean local: mint a Bool variable (not Int) so subsequent {@code not(v)},
        // {@code and([v, …])} etc. translate without a sort-mismatch crash. {@code env} caches
        // it by name, so a follow-up bind to a concrete BoolExpr (e.g. {@code composite = true}
        // in a loop body) replaces it under the same key.
        if (booleanLocals.contains(name)) {
            Object cached = env.get(name)
            if (cached != null) return cached
            Object v = session.boolVar(name)
            env.put(name, v)
            return v
        }
        return varForRaw(name)
    }

    /** Phase 45 — raw Int variable lookup without receiver-context or non-Int-sort routing. */
    private Object varForRaw(String name) {
        Object cached = env.get(name)
        if (cached != null) return cached
        Object v = session.intVar(name)
        env.put(name, v)
        v
    }

    /** Per-sort variable bindings (Phase 27), keyed by {@code name + ':' + sortHandle.toString()}. */
    private final Map<String, Object> sortedEnv = [:]

    /**
     * The non-Int analogue of {@link #varFor} — get-or-declare an SMT constant of the given sort for
     * {@code name}. For the Int sort, delegates to {@link #varFor} so the existing env / counterexample
     * walk continues to pin Int values. Used by {@link #translateInSort} when a variable appears in a
     * known non-Int position (set element, map key, etc.).
     */
    Object varForOfSort(String name, Object sort) {
        if (sort == session.intSort()) return varFor(name)
        // Phase 130 — honour an explicit env binding first, exactly as varForRaw does for the Int path. A
        // `translateWith` overlay (notably combiner inlining, which binds a formal to its actual-argument handle)
        // writes into `env`; without this, a String/Enum-typed name would skip that binding and mint a fresh
        // unconstrained constant from sortedEnv — silently dropping the binding when a combiner formal's name
        // collides with a surrounding String variable (e.g. inlining `op(a,b)` where `a` is also a method param).
        Object bound = env.get(name)
        if (bound != null) return bound
        String key = name + ':' + sort.toString()
        Object cached = sortedEnv.get(key)
        if (cached != null) return cached
        Object v = session.varOfSort(name, sort)
        sortedEnv.put(key, v)
        assertEnumDomainClosure(name, sort, v)
        v
    }

    /**
     * Translate {@code e} with an <em>expected sort</em>: a literal or variable in a known non-Int
     * position (e.g. the argument to {@code Set<String>.contains}) needs to dispatch to {@link
     * #varForOfSort}/{@link SmtSession#litOfSort} rather than the default Int path. For complex
     * expressions or the Int default sort, falls through to the existing {@link #translate}.
     */
    Object translateInSort(Expression e, Object expectedSort) {
        if (e == null) return null
        if (expectedSort == session.intSort()) return translate(e)
        if (expectedSort == session.realSort()) return asReal(e)   // Phase 70 — decimal element value
        // Phase C — a carrier content read (`m.v` / `new C(x).v`) is the datatype selector, not an enum constant;
        // translate it directly so it isn't mis-handled by the PropertyExpression-as-enum branch below.
        if (e instanceof PropertyExpression && isCarrierContentRead((PropertyExpression) e)) return translate(e)
        if (e instanceof ConstantExpression) {
            Object v = ((ConstantExpression) e).value
            if (v instanceof String) return session.litOfSort(expectedSort, (String) v)
            // Other literal kinds in a non-Int position are out of fragment (today).
            return null
        }
        if (e instanceof VariableExpression) {
            return varForOfSort(((VariableExpression) e).name, expectedSort)
        }
        if (e instanceof PropertyExpression) {
            // Enum constant: `Color.RED` reaches the encoder in two AST shapes — pre-resolution
            // `PropertyExpression(VariableExpression(Color), RED)` (the form a re-parsed contract
            // carries) and post-resolution `PropertyExpression(ClassExpression(C$Color), RED)` (the
            // form the live method body carries after type checking). Both must lower to the SAME
            // Z3 constant so a body's `s.add(Color.RED)` connects to a contract's `Color.RED in s`.
            // Solution: intern by the property name alone — the expected sort (passed in by the
            // caller, derived from the receiver type) already disambiguates cross-enum constants
            // (Suit.RED vs Color.RED reach distinct expected sorts, so a property key of "RED"
            // doesn't collide).
            PropertyExpression pe = (PropertyExpression) e
            Expression obj = pe.objectExpression
            if (obj instanceof ClassExpression || obj instanceof VariableExpression) {
                return session.litOfSort(expectedSort, pe.propertyAsString)
            }
        }
        // Anything else: best-effort fall back to the Int path (will likely return null, which the
        // caller treats as outside-fragment).
        translate(e)
    }

    /**
     * Explicit binding, used to wire formal parameters to actual-argument expressions.
     * Phase 47h — when {@code name} is recorded in {@link #scalarTypes} as a non-Int type
     * (String / Enum), also populate {@link #sortedEnv} so subsequent {@link #varForOfSort}
     * lookups (used by the GString interpolation path and other String-typed dispatches)
     * see the bound term rather than minting a fresh unconstrained constant.
     */
    void bind(String name, Object handle) {
        env.put(name, handle)
        ClassNode declared = scalarTypes.get(name)
        if (declared != null) {
            Object sort = sortFor(declared)
            if (sort != session.intSort()) {
                sortedEnv.put(name + ':' + sort.toString(), handle)
            }
        }
    }

    /** Current scalar/array binding, or null if unbound — for save/restore around a call's framing. */
    Object peekVar(String name) { env.get(name) }
    Object peekArray(String name) { arrEnv.get(name) }

    /**
     * Phase 45c — snapshot the encoder's mutable binding state so it can be restored after
     * exploring a side branch. Used by {@code LoopEncoder}'s {@code if}-statement handling to
     * apply each branch in turn and then ITE-combine the resulting bindings. Captures the
     * binding maps that {@link #bind}/{@link #bindArray}/{@link #bindSize}/{@link #bindSet}/
     * {@link #tryRecordFactoryAssign} mutate; the factory record map is captured too so a
     * conditional mutation can roll back the record if the else-branch didn't make the same
     * change.
     */
    @CompileStatic
    static class EncoderSnapshot {
        Map<String, Object> env
        Map<String, Object> arrEnv
        Map<String, Object> sizeEnv
        Map<String, Object> setEnv
        Map<String, Object> nullEnv
        Map<String, FactoryContainer> localFactories
    }

    EncoderSnapshot snapshotState() {
        EncoderSnapshot snap = new EncoderSnapshot()
        snap.env = new LinkedHashMap<String, Object>(env)
        snap.arrEnv = new LinkedHashMap<String, Object>(arrEnv)
        snap.sizeEnv = new LinkedHashMap<String, Object>(sizeEnv)
        snap.setEnv = new LinkedHashMap<String, Object>(setEnv)
        snap.nullEnv = new LinkedHashMap<String, Object>(nullEnv)
        snap.localFactories = new LinkedHashMap<String, FactoryContainer>(localFactories)
        snap
    }

    void restoreState(EncoderSnapshot snap) {
        env.clear(); env.putAll(snap.env)
        arrEnv.clear(); arrEnv.putAll(snap.arrEnv)
        sizeEnv.clear(); sizeEnv.putAll(snap.sizeEnv)
        setEnv.clear(); setEnv.putAll(snap.setEnv)
        nullEnv.clear(); nullEnv.putAll(snap.nullEnv)
        localFactories.clear(); localFactories.putAll(snap.localFactories)
    }

    /**
     * Translate {@code expr} with {@code bindings} (source-name → handle) applied
     * over the current environment, then restore it. Used to assume a callee's
     * {@code @Ensures} in the caller's context — its formal parameters substituted
     * by the actual-argument handles, and {@code result} by the call's result
     * (Phase 7 inter-procedural reasoning).
     */
    Object translateWith(Expression expr, Map<String, Object> bindings) {
        Map<String, Object> prev = new LinkedHashMap<String, Object>()
        List<String> added = new ArrayList<String>()
        for (Map.Entry<String, Object> e : bindings.entrySet()) {
            if (env.containsKey(e.key)) prev.put(e.key, env.get(e.key)) else added.add(e.key)
            env.put(e.key, e.value)
        }
        try {
            return translate(expr)
        } finally {
            for (String k : added) env.remove(k)
            for (Map.Entry<String, Object> e : prev.entrySet()) env.put(e.key, e.value)
        }
    }

    /**
     * Re-bind {@code name} to a fresh, unconstrained integer — "havoc". Used by
     * symbolic execution when an assignment's right-hand side is outside the
     * fragment (e.g. {@code s = s + a[i]}): the variable's value becomes unknown
     * rather than aborting the whole analysis. Sound for the verification
     * conditions, which only ever get harder under havoc.
     */
    Object havoc(String name) {
        Object v = session.intVar(name + '$havoc$' + (havocCounter++))
        env.put(name, v)
        v
    }

    /** Array analogue of {@link #havoc}: re-bind {@code name}'s contents to a fresh, unconstrained array. */
    Object havocArray(String name) {
        String havocName = name + '$havoc$' + (havocCounter++)
        Object[] sorts = arraySortsFor(name)
        Object kSort = sorts[0], vSort = sorts[1]
        Object v = (kSort == session.intSort() && vSort == session.intSort()) ?
            session.arrayVar(havocName) :
            session.arrayVarOfSort(havocName, kSort, vSort)
        arrEnv.put(name, v)
        v
    }
    private int havocCounter = 0

    /**
     * The size oracle: an integer constant {@code <recv>.size}, constrained
     * {@code >= 0} on first mint, modelling the length of an array/list/string
     * named {@code recv}. The same constant backs {@code recv.length},
     * {@code recv.size()}, {@code recv.isEmpty()} in contracts AND the
     * array-bounds obligation {@code i < recv.size} in {@link VerifyChecker},
     * so a contract that bounds the size and an indexing check agree.
     */
    Object sizeOf(String recv) {
        String key = recv + '.size'
        Object cached = sizeEnv.get(key)
        if (cached != null) return cached
        Object v = session.intVar(key)
        // Java's collection contract: 0 ≤ size ≤ Integer.MAX_VALUE. The upper bound (Phase 44c)
        // closes a subtle math-int unsoundness without opt-in: index arithmetic like {@code i + 1}
        // for {@code i ∈ [0, size)} cannot overflow into a wrap-around index under the model,
        // because {@code i + 1 ≤ size ≤ INT_MAX}. Asserted, not checked — the contract holds by
        // the JVM, not by anything the verifier proves.
        session.assertExpr(session.and([
            session.ge(v, session.intLit(0L)),
            session.le(v, session.intLit(2147483647L))]))
        sizeEnv.put(key, v)
        v
    }

    /**
     * Phase 40 — rebind the size oracle for {@code recv} to a fresh handle, threading size-changing
     * mutations (list {@code add}/{@code clear}/{@code removeLast}) the same way {@link #bindArray}
     * threads the array oracle and {@link #bindSet} threads a set's characteristic array. Subsequent
     * {@link #sizeOf(String)} reads return the new handle. Caller is responsible for the equality
     * relating new to old (e.g. {@code newSize == oldSize + 1} for an append).
     */
    void bindSize(String recv, Object handle) {
        sizeEnv.put(recv + '.size', handle)
    }

    /**
     * Phase 45c — raw size-oracle rebind by full key (e.g. {@code xs.size}), bypassing the
     * {@code .size}-suffix manipulation of {@link #bindSize}. Used by the snapshot/restore
     * ITE-combine in {@code LoopEncoder} where snapshot keys already carry the suffix.
     */
    void bindSizeRaw(String fullKey, Object handle) {
        sizeEnv.put(fullKey, handle)
    }

    /** True if a size oracle has already been minted for {@code recv} (i.e. a contract referenced its size). */
    boolean hasSizeOracle(String recv) { sizeEnv.containsKey(recv + '.size') }

    /** True if a nullity oracle has already been minted for {@code recv}. */
    boolean hasNullityOracle(String recv) { nullEnv.containsKey(recv) }

    /**
     * Get-or-declare the array-content handle for a source-level name. Shares its
     * key with nothing else — the size oracle ({@link #sizeOf}) bounds the valid
     * index range, this models the element values. Element sort dispatch via
     * {@link #listElementSort} (Phase 27): a non-Int element list or a non-Int
     * value-side map allocates {@code Array Int -> ElemSort}; Int-element arrays keep
     * the existing {@link SmtSession#arrayVar} storage so the counterexample model walk
     * continues to pin contents the way it does today.
     */
    Object arrayFor(String name) {
        Object cached = arrEnv.get(name)
        if (cached != null) return cached
        Object[] sorts = arraySortsFor(name)
        Object kSort = sorts[0], vSort = sorts[1]
        Object v = (kSort == session.intSort() && vSort == session.intSort()) ?
            session.arrayVar(name) :
            session.arrayVarOfSort(name, kSort, vSort)
        arrEnv.put(name, v)
        v
    }

    /**
     * The {@code [keySort, valueSort]} for an array handle key. Recognises the three name shapes
     * the encoder uses:
     * - {@code map$vals$<logical>} / {@code map$vals$old$<logical>} — a map's value array; key
     *   sort = the map's KEY sort, value sort = the map's VALUE sort (so a Map<String,Integer>
     *   is {@code Array String -> Int}, Map<String,String> is {@code Array String -> String}).
     * - {@code old$<name>} — entry snapshot of a list; Int-indexed, value sort = list's element sort.
     * - {@code <name>} — a regular array/list name; Int-indexed, value sort from {@code listElementTypes}.
     * Default Int/Int when not classified as non-Int, preserving the existing untyped-list path.
     */
    private Object[] arraySortsFor(String name) {
        if (name.startsWith('map$vals$')) {
            String logical = name.substring('map$vals$'.length())
            if (logical.startsWith('old$')) logical = logical.substring('old$'.length())
            // mapValueSort handles the Phase 36 nested-set case (Array<V, Int>) — call it instead
            // of re-deriving from mapTypes so a Map<K, Set<V>> mints with the right value sort.
            return [mapKeySort(logical), mapValueSort(logical)] as Object[]
        }
        String n = name
        if (n.startsWith('old$')) n = n.substring('old$'.length())
        [session.intSort(), sortFor(listElementTypes.get(n))] as Object[]
    }

    /**
     * Re-bind an array name to a new content handle — used to thread an array
     * update {@code a[i] = v} as {@code a := (store a i v)}, so a later read of
     * {@code a[i]} sees the post-update contents (value semantics, no aliasing).
     */
    void bindArray(String name, Object handle) {
        arrEnv.put(name, handle)
    }

    /**
     * Get-or-declare the set handle for a name / {@code old$name} — a characteristic
     * {@code Array <elem-sort> -> Int}. Element sort comes from the receiver type collected by
     * {@link VerifyChecker}: Int-element sets keep the existing {@link SmtSession#setVar} storage
     * (so the counterexample walk still pins them as before); non-Int element sets allocate via
     * {@link SmtSession#arrayVarOfSort}. Map key-sets (keyed {@code map$keys$<logical>}) consult
     * the map's key type, not its value type.
     */
    Object setFor(String key) {
        Object cached = setEnv.get(key)
        if (cached != null) return cached
        Object elemSort = setKeySortForKey(key)
        Object v = (elemSort == session.intSort()) ?
            session.setVar(key) :
            session.arrayVarOfSort(key, elemSort, session.intSort())
        setEnv.put(key, v)
        assertEnumDomainAxioms(key, v)
        v
    }

    /**
     * For an enum-element set, assert the three facts the finite enum domain gives, once per
     * set handle:
     * (a) **pigeonhole** {@code card(s) <= N} (Phase 29),
     * (b) **full-coverage iff** {@code card(s) == N ⟺ c1 ∈ s ∧ … ∧ cN ∈ s} (Phase 29),
     * (c) **empty iff** {@code card(s) == 0 ⟺ c1 ∉ s ∧ … ∧ cN ∉ s} (Phase 30+) — the dual
     *     of (b) at the other endpoint, letting {@code s.size() == 0} reason about (non-)membership
     *     of every constant.
     * All three are theorems of "{@code s} is a set over an N-constant enum domain". No-op for
     * Int-element or non-enum sets, and for map key-sets (which can have enum keys but where the
     * *map's* key bound is the user-visible analog).
     */
    private void assertEnumDomainAxioms(String key, Object setH) {
        if (key.startsWith('map$keys$')) return   // map key-sets handled via the map's own axioms
        ClassNode elemType = elementTypeForSetKey(key)
        if (elemType == null) return
        if (!(elemType.isEnum() || isEnumLikeType(elemType))) return
        List<String> names = enumConstantNames(elemType)
        int n = names.size()
        if (n <= 0) return
        Object nLit = session.intLit((long) n)
        Object zero = session.intLit(0L)
        Object card = cardOf(setH)
        session.assertExpr(session.le(card, nLit))                            // pigeonhole
        Object full = finiteEnumCoverage(setH, elemType)
        session.assertExpr(session.eq(session.eq(card, nLit), full))          // card == N ⟺ full coverage
        // Empty iff: card(s) == 0 ⟺ ¬c1 ∈ s ∧ … ∧ ¬cN ∈ s.
        Object enumSort = session.declareSort(enumSortName(elemType))
        List<Object> noneIn = new ArrayList<Object>()
        for (String constName : names) {
            noneIn.add(session.not(member(setH, session.litOfSort(enumSort, constName))))
        }
        Object empty = noneIn.size() == 1 ? noneIn.get(0) : session.and(noneIn)
        session.assertExpr(session.eq(session.eq(card, zero), empty))
    }

    /**
     * The element sort for a set handle key. Three shapes:
     * - {@code map$keys$<logical>} or {@code map$keys$old$<logical>} — a map's key-set; element sort is
     *   the map's KEY sort.
     * - {@code old$<name>} — a set's entry-state snapshot; element sort is the same as {@code name}'s.
     * - {@code <name>} — a regular set name; element sort comes from {@code setElementTypes}.
     */
    private Object setKeySortForKey(String key) {
        String name = key
        if (name.startsWith('map$keys$')) {
            name = name.substring('map$keys$'.length())
            if (name.startsWith('old$')) name = name.substring('old$'.length())
            ClassNode[] pair = mapTypes.get(name)
            return sortFor(pair != null ? pair[0] : null)
        }
        if (name.startsWith('old$')) name = name.substring('old$'.length())
        sortFor(setElementTypes.get(name))
    }

    /**
     * The Groovy {@link ClassNode} for the element type of a set-handle key (Phase 29). Mirror of
     * {@link #setKeySortForKey} returning the raw type rather than the Z3 sort — used by callers
     * that need to know "is this an enum, and how many constants does it have" to apply the
     * enum-domain {@code Sets.boundedBy}/{@code Sets.boundedCount} specialisation.
     */
    private ClassNode elementTypeForSetKey(String key) {
        String name = key
        if (name.startsWith('map$keys$')) {
            name = name.substring('map$keys$'.length())
            if (name.startsWith('old$')) name = name.substring('old$'.length())
            ClassNode[] pair = mapTypes.get(name)
            return pair != null ? pair[0] : null
        }
        if (name.startsWith('old$')) name = name.substring('old$'.length())
        setElementTypes.get(name)
    }

    /** Phase 29 — enum constant names on a ClassNode (filtered by JVM {@code ACC_ENUM}). */
    private static List<String> enumConstantNames(ClassNode t) {
        List<String> names = new ArrayList<String>()
        for (FieldNode f : t.fields) {
            if ((f.modifiers & 0x4000) != 0) names.add(f.name)
        }
        names
    }

    /**
     * Phase 29 — try to fold {@code e} to a {@code Long} at translate time. Recognises ordinary
     * integer ConstantExpressions and the Phase 28 {@code <EnumClass>.values().length} /
     * {@code .size()} shapes. Used to detect whether a {@code Sets.boundedBy}/{@code Sets.boundedCount}
     * second argument matches an enum's domain size, enabling the finite-conjunction lowering.
     */
    private Long tryFoldToLong(Expression e) {
        if (e instanceof ConstantExpression) {
            Object v = ((ConstantExpression) e).value
            if (v instanceof Number) return ((Number) v).longValue()
        }
        if (e instanceof PropertyExpression && ((PropertyExpression) e).propertyAsString == 'length') {
            Integer cnt = enumValuesCountFor(((PropertyExpression) e).objectExpression)
            if (cnt != null) return cnt.longValue()
        }
        if (e instanceof MethodCallExpression && ((MethodCallExpression) e).methodAsString == 'size') {
            MethodCallExpression mce = (MethodCallExpression) e
            if (argList(mce).isEmpty()) {
                Integer cnt = enumValuesCountFor(mce.objectExpression)
                if (cnt != null) return cnt.longValue()
            }
        }
        null
    }

    /**
     * Lower {@code s.containsAll(t)} for sets sharing an element sort. Two cases:
     *
     * - **Enum** (Phase 30): finite conjunction {@code ∧ (c_i ∈ t ⟹ c_i ∈ s)} over the enum's
     *   constants — the same shape Phase 29 uses for full-coverage, with implication instead of
     *   bare membership.
     * - **Int** (Phase 31): when a bound {@code Sets.boundedBy(t, n)} has been seen earlier in the
     *   same session (registered in {@link #intSubsetBounds}), lower to the bounded universal
     *   {@code ∀i. 0 <= i < n ⟹ (i ∈ t ⟹ i ∈ s)}. Without a registered bound the universal is
     *   unbounded (trigger-cliff territory) — return null and skip.
     *
     * Returns null for sort-mismatch or any other element sort (String, …).
     */
    /**
     * Phase 32b — lower {@code s.equals(t)} to {@code s.containsAll(t) ∧ t.containsAll(s)},
     * composing the existing subset lowering in both directions. Returns null if either subset
     * translation does (the caller treats that as "outside fragment"). Note: writing
     * {@code s == t} directly in a contract uses Z3's array-equality predicate (an unbounded
     * universal on the characteristic functions); this method-form path gives the user a
     * propositionally-decomposed alternative that Z3 reasons about as ground facts.
     */
    /**
     * Phase 33 — a recognised inline set union/intersection: two known set names with matching
     * element sort, combined by {@code +} (union) or {@code .intersect(...)} (intersection).
     * The encoder never mints a new set handle for the result — that's the *materialised* mode
     * and a separate, bigger phase. Instead, methods called on the result are lowered lazily:
     * {@code (s + t).contains(x)} → {@code s.contains(x) ∨ t.contains(x)}, etc.
     */
    @CompileStatic
    private static class SetBinop {
        String leftKey
        String rightKey
        Object elemSort
        ClassNode elemType
        String kind               // 'union' (+), 'intersect' (.intersect), 'difference' (-), 'symdiff' (^)
    }

    /**
     * The membership predicate for {@code x ∈ (a <kind> b)} given {@code x∈a} ({@code inA}) and
     * {@code x∈b} ({@code inB}). The whole set algebra is just this one four-way combine, slotted into
     * the bounded-universal (Int) / finite-conjunction (enum) lowerings below.
     */
    private Object setCombineMembership(String kind, Object inA, Object inB) {
        switch (kind) {
            case 'union':      return session.or([inA, inB])
            case 'intersect':  return session.and([inA, inB])
            case 'difference': return session.and([inA, session.not(inB)])                  // a \ b
            case 'symdiff':    return session.or([session.and([inA, session.not(inB)]),
                                                  session.and([session.not(inA), inB])])     // (a\b) ∪ (b\a)
            default:           return null
        }
    }

    /**
     * True if {@code e} is a known set union ({@code +}), intersection ({@code .intersect}), difference
     * ({@code -}) or symmetric difference ({@code ^}) over two same-element-sort sets. Null otherwise.
     */
    /** Phase 35b — a name recorded as a set binop (e.g. `result` returned as `a & b`, or a local
     *  `Set u = a | b`), so membership / `contains` on the *name* folds to the inline binop. */
    private final Map<String, Expression> setBinopDefs = [:]

    /** Record {@code name = rhs} when rhs is (or aliases) a set binop, so later `x in name` folds inline.
     *  Used for a set-binop *return* (binding `result`) and for set-binop locals. */
    boolean tryRecordSetBinopAssign(String name, Expression rhs) {
        if (rhs instanceof VariableExpression) {
            Expression recorded = setBinopDefs.get(((VariableExpression) rhs).name)   // returning a set-binop local
            if (recorded != null) { setBinopDefs.put(name, recorded); return true }
            return false
        }
        if (setBinopFor(rhs) == null) return false
        setBinopDefs.put(name, rhs)
        true
    }

    private SetBinop setBinopFor(Expression e) {
        // Unwrap an outer cast — e.g. `a.intersect(b) as Set<Role>` (Groovy's GDK intersect returns
        // Collection, so a Set-typed target needs the explicit cast). The cast doesn't change the
        // set semantics; the wrapped expression is the one we recognise.
        if (e instanceof CastExpression) e = ((CastExpression) e).expression
        // A name recorded as a set binop (Phase 35b) resolves to that binop — so `x in result` where
        // `result` was returned as `a & b` folds exactly like the inline `x in (a & b)`.
        if (e instanceof VariableExpression) {
            Expression recorded = setBinopDefs.get(((VariableExpression) e).name)
            if (recorded != null) e = recorded
        }
        if (e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e
            switch (be.operation.type) {
                case Types.PLUS:        return tryMakeSetBinop(be.leftExpression, be.rightExpression, 'union')
                case Types.BITWISE_OR:  return tryMakeSetBinop(be.leftExpression, be.rightExpression, 'union')        // a | b
                case Types.BITWISE_AND: return tryMakeSetBinop(be.leftExpression, be.rightExpression, 'intersect')   // a & b
                case Types.MINUS:       return tryMakeSetBinop(be.leftExpression, be.rightExpression, 'difference')
                case Types.BITWISE_XOR: return tryMakeSetBinop(be.leftExpression, be.rightExpression, 'symdiff')
            }
        }
        if (e instanceof MethodCallExpression) {
            MethodCallExpression mce = (MethodCallExpression) e
            if (argList(mce).size() == 1) {
                // The method forms of the operators: `a & b` is `a.and(b)`, `a | b` is `a.or(b)`,
                // `a ^ b` is `a.xor(b)`, `a - b` is `a.minus(b)`; plus the GDK `a.intersect(b)`.
                String k = null
                switch (mce.methodAsString) {
                    case 'intersect': case 'and': k = 'intersect'; break
                    case 'or':                    k = 'union';     break
                    case 'xor':                   k = 'symdiff';   break
                    case 'minus':                 k = 'difference'; break
                }
                if (k != null) return tryMakeSetBinop(mce.objectExpression, argList(mce).get(0), k)
            }
        }
        null
    }

    private SetBinop tryMakeSetBinop(Expression leftExpr, Expression rightExpr, String kind) {
        String lKey = setKeyFor(leftExpr)
        String rKey = setKeyFor(rightExpr)
        if (lKey == null || rKey == null) return null
        Object lSort = setKeySortForKey(lKey)
        Object rSort = setKeySortForKey(rKey)
        if (lSort != rSort) return null
        SetBinop b = new SetBinop()
        b.leftKey = lKey
        b.rightKey = rKey
        b.elemSort = lSort
        b.elemType = elementTypeForSetKey(lKey)
        b.kind = kind
        b
    }

    /**
     * Phase 33 — lower {@code (s + t).containsAll(u)} / {@code s.intersect(t).containsAll(u)} to
     * a finite conjunction over the enum domain (or bounded Int domain), where each per-constant
     * implication says "constant ∈ u ⟹ constant ∈ s ∨/∧ constant ∈ t". For enum-element sets,
     * the constants come from the enum directly. Int-element binops would need a bound on {@code u}
     * (the universal's domain), same plumbing as Phase 31; not yet wired.
     */
    /**
     * Phase 35 — materialise {@code Set<X> u = a + b} or {@code Set<X> u = a.intersect(b)}: register
     * {@code u} as a known set local with the same element type as the operands, mint its handle,
     * and emit the per-element membership iff axiom relating {@code u} to {@code a} and {@code b}.
     * Once registered, every existing set capability (subset, equals, containsValue via map joins,
     * cardinality update laws on subsequent mutations, pigeonhole/full-coverage iff/empty iff via
     * {@link #assertEnumDomainAxioms}) picks up {@code u} as a first-class set.
     *
     * Enum-element domain only in this slice: the per-constant membership iff is a finite
     * conjunction. Int-element and uninterpreted-sort cases would need an unbounded universal with
     * trigger on {@code select(u, x)} — pulls in quantifier reasoning on every membership query,
     * deferred. Returns {@code true} on success so the caller can short-circuit the int-SSA path.
     */
    boolean tryMaterialiseSetBinopAssign(String name, Expression rhs) {
        SetBinop binop = setBinopFor(rhs)
        if (binop == null) return false
        // Int-element: materialise over the bounded [0, n) domain of a prior {@code Sets.boundedBy} on an
        // operand (the dual of Phase 31's Int subset). Emit {@code ∀i. 0<=i<n ⟹ (i∈u ⟺ i∈a ∨/∧ i∈b)} — a
        // *true sub-fact* of the full union/intersection (sound, though it only pins {@code u} within the
        // bound). {@code u} inherits a bound where provable, so a later {@code u.containsAll}/subset chains.
        if (binop.elemSort == session.intSort()) {
            Object nLeft = intSubsetBounds.get(binop.leftKey)
            Object nRight = intSubsetBounds.get(binop.rightKey)
            Object nDomain = nLeft != null ? nLeft : nRight
            if (nDomain == null) return false                          // no bound in scope → loud skip
            setElementTypes.put(name, binop.elemType)
            Object uH = setFor(name)
            Object aH = setFor(binop.leftKey)
            Object bH = setFor(binop.rightKey)
            Object iv = session.boundIntVar('setmat$i' + (quantCounter++))
            Object inRange = session.and([session.le(session.intLit(0L), iv), session.lt(iv, nDomain)])
            Object combined = setCombineMembership(binop.kind, member(aH, iv), member(bH, iv))
            Object iff = session.eq(member(uH, iv), combined)
            session.assertExpr(session.forall([iv], session.implies(inRange, iff), [session.select(uH, iv)]))
            // u inherits a bound where provable: intersection ⊆ either operand; difference a\b ⊆ a;
            // union / symdiff ⊆ a∪b (needs both operands bounded by the same n).
            Object uBound
            switch (binop.kind) {
                case 'intersect':  uBound = nDomain; break
                case 'difference': uBound = nLeft; break
                default:           uBound = (nLeft != null && nRight != null && nLeft == nRight) ? nLeft : null
            }
            if (uBound != null) intSubsetBounds.put(name, uBound)
            return true
        }
        ClassNode elemType = binop.elemType
        if (elemType == null || !(elemType.isEnum() || isEnumLikeType(elemType))) return false
        // Commit: register u's element type *before* setFor mints the handle, so its enum-domain
        // axioms (pigeonhole + full-coverage iff + empty iff, all theorems of the iff below) fire.
        setElementTypes.put(name, elemType)
        Object uH = setFor(name)
        Object aH = setFor(binop.leftKey)
        Object bH = setFor(binop.rightKey)
        Object enumSort = session.declareSort(enumSortName(elemType))
        for (String constName : enumConstantNames(elemType)) {
            Object c = session.litOfSort(enumSort, constName)
            Object inU = member(uH, c)
            Object inA = member(aH, c)
            Object inB = member(bH, c)
            Object rhsExpr = setCombineMembership(binop.kind, inA, inB)
            session.assertExpr(session.eq(inU, rhsExpr))
        }
        true
    }

    private Object translateContainsAllOnBinop(SetBinop binop, Expression uExpr) {
        String uKey = setKeyFor(uExpr)
        if (uKey == null) return null
        if (setKeySortForKey(uKey) != binop.elemSort) return null
        Object sH = setFor(binop.leftKey)
        Object tH = setFor(binop.rightKey)
        Object uH = setFor(uKey)
        // Int: a bounded universal over [0, n) from a prior {@code Sets.boundedBy} on the *argument* (the
        // universal's domain) — {@code i∈u ⟹ i∈s ∨/∧ i∈t}, the binop dual of Phase 31's Int subset.
        if (binop.elemSort == session.intSort()) {
            Object nH = intSubsetBounds.get(uKey)
            if (nH == null) return null
            Object iv = session.boundIntVar('setbinop$i' + (quantCounter++))
            Object inRange = session.and([session.le(session.intLit(0L), iv), session.lt(iv, nH)])
            Object combined = setCombineMembership(binop.kind, member(sH, iv), member(tH, iv))
            Object body = session.implies(member(uH, iv), combined)
            return session.forall([iv], session.implies(inRange, body), [session.select(uH, iv)])
        }
        // Enum case: finite conjunction over the enum's constants.
        ClassNode elemType = binop.elemType
        if (elemType == null || !(elemType.isEnum() || isEnumLikeType(elemType))) return null
        Object enumSort = session.declareSort(enumSortName(elemType))
        List<Object> conjuncts = new ArrayList<Object>()
        for (String constName : enumConstantNames(elemType)) {
            Object constLit = session.litOfSort(enumSort, constName)
            Object inS = member(sH, constLit)
            Object inT = member(tH, constLit)
            Object rhs = setCombineMembership(binop.kind, inS, inT)
            conjuncts.add(session.implies(member(uH, constLit), rhs))
        }
        conjuncts.isEmpty() ? session.boolLit(true) : session.and(conjuncts)
    }

    /**
     * Phase 36 — a recognised {@code m[k]} receiver on a {@code Map<K, Set<V>>}, resolved to the
     * inner set as an SMT array term. Carries the inner element {@link ClassNode} so containsAll
     * over an enum-V domain knows the constant set to enumerate.
     */
    @CompileStatic
    private static class NestedSetReceiver {
        Object innerSet         // SMT array term: select(map$vals, k)
        Object innerElemSort    // Z3 sort of V
        ClassNode innerElemType // Groovy type of V (for enum-domain dispatch)
    }

    /**
     * If {@code e} is {@code m[k]} for a known {@code Map<K, Set<V>>} (Phase 36), return the
     * resolved nested set; null otherwise. The key is translated in the map's key sort, so
     * an enum key like {@code Role.ADMIN} routes through {@code translateInSort} cleanly.
     */
    private NestedSetReceiver nestedSetReceiverFor(Expression e) {
        if (!(e instanceof BinaryExpression)) return null
        BinaryExpression be = (BinaryExpression) e
        if (be.operation.type != Types.LEFT_SQUARE_BRACKET) return null
        String mapName = mapLogicalFor(be.leftExpression)
        if (mapName == null) return null
        ClassNode innerType = nestedSetValueTypes.get(mapName)
        if (innerType == null) return null
        Object kSort = mapKeySort(mapName)
        Object k = translateInSort(be.rightExpression, kSort)
        if (k == null) return null
        NestedSetReceiver r = new NestedSetReceiver()
        r.innerSet = session.select(mapValsFor(mapName), k)
        r.innerElemSort = sortFor(innerType)
        r.innerElemType = innerType
        r
    }

    /**
     * Phase 36 — lower {@code m[k].containsAll(s)} for a nested-set map with enum-element V:
     * finite conjunction {@code ∧ (c ∈ s ⟹ c ∈ m[k])} over V's constants. Int-element / String-
     * element inner sets would need a bound on the subset operand (Phase 31's intSubsetBounds
     * applied to a transient receiver); not wired in this slice.
     */
    private Object translateNestedContainsAll(NestedSetReceiver nr, Expression tExpr) {
        String tKey = setKeyFor(tExpr)
        if (tKey == null) return null
        if (setKeySortForKey(tKey) != nr.innerElemSort) return null
        ClassNode elemType = nr.innerElemType
        if (elemType == null || !(elemType.isEnum() || isEnumLikeType(elemType))) return null
        Object tH = setFor(tKey)
        Object enumSort = session.declareSort(enumSortName(elemType))
        List<Object> conjuncts = new ArrayList<Object>()
        for (String constName : enumConstantNames(elemType)) {
            Object constLit = session.litOfSort(enumSort, constName)
            conjuncts.add(session.implies(member(tH, constLit), member(nr.innerSet, constLit)))
        }
        conjuncts.isEmpty() ? session.boolLit(true) : session.and(conjuncts)
    }

    /**
     * Phase 38 — a recognised immutable-container factory expression. Carries enough information
     * to fold peephole operations ({@code .size()}, {@code .isEmpty()}, {@code .contains(x)},
     * {@code .get(i)}, {@code .containsKey}, {@code m[k]}) to ground SMT terms without minting
     * any handle. For lists/sets the elements live in {@code args}; for maps the keys and values
     * live in parallel {@code keys}/{@code values} lists.
     */
    @CompileStatic
    static class FactoryContainer {
        String kind                    // 'list' | 'set' | 'map'
        List<Expression> args          // list/set elements; null for maps
        List<Expression> keys          // map keys; null for list/set
        List<Expression> values        // map values; null for list/set
        int entryCount() { args != null ? args.size() : (keys != null ? keys.size() : 0) }
    }

    /** True if {@code e} is the {@code groovy.lang.Tuple} class (the receiver of {@code Tuple.tuple(...)}). */
    private static boolean isTupleReceiver(Expression e) {
        if (e instanceof VariableExpression) return ((VariableExpression) e).name == 'Tuple'
        if (e instanceof ClassExpression) return ((ClassExpression) e).type?.nameWithoutPackage == 'Tuple'
        if (e instanceof PropertyExpression) return ((PropertyExpression) e).propertyAsString == 'Tuple'
        false
    }

    /**
     * The 0-based slot index for a tuple accessor name — {@code v1}/{@code getV1}/{@code first} → 0,
     * {@code v2}/{@code getV2}/{@code second} → 1, … {@code vN}/{@code getVN} → N-1; -1 if not a slot name.
     */
    private static int tupleSlotIndex(String name) {
        if (name == 'first') return 0
        if (name == 'second') return 1
        if (name ==~ /v\d+/) return Integer.parseInt(name.substring(1)) - 1
        if (name ==~ /getV\d+/) return Integer.parseInt(name.substring(4)) - 1
        -1
    }

    /** Arity of a {@code TupleN} type (the N), or -1 if not a tuple type. */
    private static int tupleArity(ClassNode t) {
        String n = t?.nameWithoutPackage
        (n != null && (n ==~ /Tuple\d+/)) ? Integer.parseInt(n.substring(5)) : -1
    }

    /** Phase 113 — is {@code t} a {@code TupleN} type (so its slots `.vN` are addressable)? */
    boolean isTupleType(ClassNode t) { tupleArity(t) >= 2 }

    /**
     * Phase 113 — register a tuple-typed <em>local</em> bound to a tuple-returning call, reusing the Phase-80
     * tuple-parameter machinery: {@code r.vN} then resolves to the per-slot entity {@code r$vN}. The callee's
     * {@code @Ensures}, with {@code result} renamed to this local, constrains those same entities.
     */
    void registerTupleLocal(String name, ClassNode type) { if (isTupleType(type)) tupleParams.put(name, type) }

    /**
     * Phase 133 — temporarily register names as carrier-typed (a callee's carrier formals / {@code result} /
     * {@code this} while assuming its instance @Ensures), so a {@code name.field} read in that contract resolves
     * via {@link #carrierTypeOf}. Returns the prior bindings (null = was absent) for {@link #popScalarTypes}.
     */
    Map<String, ClassNode> pushScalarTypes(Map<String, ClassNode> add) {
        Map<String, ClassNode> prev = new LinkedHashMap<String, ClassNode>()
        add.each { String k, ClassNode v -> prev.put(k, scalarTypes.get(k)); scalarTypes.put(k, v) }
        prev
    }

    /** Restore the type registry saved by {@link #pushScalarTypes}. */
    void popScalarTypes(Map<String, ClassNode> prev) {
        prev.each { String k, ClassNode v -> if (v == null) scalarTypes.remove(k) else scalarTypes.put(k, v) }
    }

    /** Phase 146 — permanently register a (fresh temp) local's carrier type, so a later {@code name.field} read
     *  resolves via {@link #carrierTypeOf}. Used when a chain's call result is hoisted to a temp local so a
     *  read-out in the same expression (`…​.plus(…​).value`) becomes an ordinary component read off the temp. */
    void registerScalarType(String name, ClassNode type) { scalarTypes.put(name, type) }

    /** The declared type of slot {@code i} of a {@code TupleN<...>} (from its generics), or null (→ Int). */
    private static ClassNode tupleSlotType(ClassNode t, int i) {
        try {
            def gens = t?.genericsTypes
            if (gens != null && i < gens.length && gens[i].type != null) return gens[i].type
        } catch (Throwable ignored) {}
        null
    }

    /**
     * Slot {@code slotIndex} of a tuple <em>parameter</em> {@code name}: a fresh typed entity {@code name$vN}
     * minted in the slot's sort (the caller's component value, uninterpreted). Null if {@code name} isn't a
     * tuple parameter or the index is out of range.
     */
    private Object tupleSlotEntity(String name, int slotIndex) {
        ClassNode t = tupleParams.get(name)
        if (t == null || slotIndex < 0 || slotIndex >= tupleArity(t)) return null
        return varForOfSort(name + '$v' + (slotIndex + 1), sortFor(tupleSlotType(t, slotIndex)))
    }

    /** A constant-slot accessor — {@code X.vN}/{@code X.first}/{@code X.second}/{@code X[k]} — as [innerExpr, slotIndex], else null. */
    private Object[] slotAccessor(Expression e) {
        if (e instanceof PropertyExpression) {
            int si = tupleSlotIndex(((PropertyExpression) e).propertyAsString)
            if (si >= 0) return [((PropertyExpression) e).objectExpression, si] as Object[]
        }
        if (e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e
            if (be.operation.type == Types.LEFT_SQUARE_BRACKET &&
                be.rightExpression instanceof ConstantExpression &&
                ((ConstantExpression) be.rightExpression).value instanceof Integer) {
                return [be.leftExpression, (Integer) ((ConstantExpression) be.rightExpression).value] as Object[]
            }
        }
        null
    }

    /**
     * Phase 80/82 — resolve a tuple <em>parameter</em> access chain to [flattenedEntityPrefix, TupleN type],
     * descending through nested tuple slots ({@code t.v1.v2} → {@code [t$v1, Tuple2<...>]}). Null unless the
     * chain bottoms out at a tuple-typed parameter and every step's slot type is itself a tuple.
     */
    private Object[] tupleParamRef(Expression e) {
        Expression t = unwrapImmutableWrap(e)
        if (t instanceof VariableExpression) {
            ClassNode tt = tupleParams.get(((VariableExpression) t).name)
            if (tt != null) return [((VariableExpression) t).name, tt] as Object[]
        }
        Object[] acc = slotAccessor(t)
        if (acc != null) {
            Object[] inner = tupleParamRef((Expression) acc[0])
            if (inner != null) {
                int k = (int) acc[1]
                ClassNode type = (ClassNode) inner[1]
                if (k >= 0 && k < tupleArity(type)) {
                    ClassNode slotType = tupleSlotType(type, k)
                    if (tupleArity(slotType) >= 0) {   // slot is itself a tuple → keep descending
                        return [((String) inner[0]) + '$v' + (k + 1), slotType] as Object[]
                    }
                }
            }
        }
        null
    }

    /** Slot {@code slot} of a (possibly nested) tuple-parameter expression {@code obj} → its typed entity, or null. */
    private Object tupleParamSlot(Expression obj, int slot) {
        Object[] ref = tupleParamRef(obj)
        if (ref == null) return null
        ClassNode type = (ClassNode) ref[1]
        if (slot < 0 || slot >= tupleArity(type)) return null
        return varForOfSort(((String) ref[0]) + '$v' + (slot + 1), sortFor(tupleSlotType(type, slot)))
    }

    /**
     * The component-value handles of {@code e} if it is a fixed-arity product — a factory container
     * (a list literal, {@code Tuple.tuple(...)}, {@code new TupleN(...)}, {@code List.of(...)}) or a tuple
     * <em>parameter</em> (its slot entities) — else null. Each component translates in its own sort.
     */
    private List<Object> tupleComponents(Expression e) {
        Expression t = unwrapImmutableWrap(e)
        FactoryContainer f = factoryContainerFor(t)
        if (f != null && f.kind == 'list' && f.args != null) {
            List<Object> out = new ArrayList<Object>()
            for (Expression a : f.args) {
                Object h = translate(a)
                if (h == null) return null
                out.add(h)
            }
            return out
        }
        if (t instanceof VariableExpression) {
            ClassNode tt = tupleParams.get(((VariableExpression) t).name)
            if (tt != null) {
                int ar = tupleArity(tt)
                List<Object> out = new ArrayList<Object>()
                for (int i = 0; i < ar; i++) {
                    Object h = tupleSlotEntity(((VariableExpression) t).name, i)
                    if (h == null) return null
                    out.add(h)
                }
                return out
            }
        }
        null
    }

    /**
     * Component-wise equality {@code a == b} (or {@code !=}) for two fixed-arity products (Phase 81):
     * a conjunction of pairwise component equalities, or {@code false} for a length mismatch (Groovy's
     * list/tuple equality). Each pairwise {@code eq} is in the component's sort; a sort mismatch (comparing
     * unlike tuple types) is a clean skip. Returns null unless <em>both</em> sides are products.
     */
    private Object translateTupleEquality(BinaryExpression be, boolean isEq) {
        List<Object> lc = tupleComponents(be.leftExpression)
        if (lc == null) return null
        List<Object> rc = tupleComponents(be.rightExpression)
        if (rc == null) return null
        if (lc.size() != rc.size()) {
            Object f = session.boolLit(false)
            return isEq ? f : session.not(f)
        }
        try {
            List<Object> eqs = new ArrayList<Object>()
            for (int i = 0; i < lc.size(); i++) eqs.add(session.eq(lc.get(i), rc.get(i)))
            Object conj = eqs.isEmpty() ? session.boolLit(true) : (eqs.size() == 1 ? eqs.get(0) : session.and(eqs))
            return isEq ? conj : session.not(conj)
        } catch (Exception ignored) {
            return null
        }
    }

    /**
     * Phase 38 — recognise a factory call or Groovy literal that yields an immutable container of
     * known size and elements:
     *   - {@code List.of(a, b, …)} / {@code Set.of(a, b, …)} / {@code Map.of(k1, v1, …)}
     *   - Groovy list literal {@code [a, b, c]} (kind {@code list} by default; the outer cast,
     *     {@code [a, b, c] as Set<X>}, switches the kind)
     *   - Groovy map literal {@code [k1: v1, k2: v2]}
     * Returns null for anything else, so callers fall through to their default receiver handling.
     */
    /**
     * Phase 38c — true if {@code args} contains two {@link ConstantExpression}s with equal values.
     * Used to refuse {@code Set.of} folds where the literal arg list already shows a runtime
     * duplicate. Non-literal args are conservatively treated as distinct (the verifier doesn't
     * try to prove symbolic distinctness — out of scope for this peephole).
     */
    private static boolean hasDuplicateLiteralArgs(List<Expression> args) {
        if (args == null || args.size() < 2) return false
        List<Object> literals = new ArrayList<Object>()
        for (Expression a : args) {
            if (a instanceof ConstantExpression) {
                Object v = ((ConstantExpression) a).value
                if (v != null) literals.add(v)
            }
        }
        for (int i = 0; i < literals.size(); i++) {
            for (int j = i + 1; j < literals.size(); j++) {
                if (literals.get(i) == literals.get(j)) return true
            }
        }
        false
    }

    /**
     * Phase 38c — transparent immutability wrappers: {@code xs.asImmutable()} and
     * {@code Collections.unmodifiableList/Set/Map(xs)} return a wrapper around their argument
     * with identical read behaviour (only writes throw). For verification, the wrapper IS the
     * operand for {@code .size()}/{@code .contains}/{@code .get(i)}/etc. — unwrap and continue
     * dispatch on the inner expression. Returns {@code e} unchanged if it isn't a recognised
     * wrapper, so calls remain idempotent.
     */
    private static Expression unwrapImmutableWrap(Expression e) {
        if (e instanceof MethodCallExpression) {
            MethodCallExpression mce = (MethodCallExpression) e
            String m = mce.methodAsString
            // xs.asImmutable() — Groovy GDK idiom, no args.
            if (m == 'asImmutable' && argList(mce).isEmpty()) {
                return mce.objectExpression
            }
            // Collections.unmodifiableList(xs) / unmodifiableSet(xs) / unmodifiableMap(xs)
            if (mce.objectExpression instanceof ClassExpression) {
                String tn = ((ClassExpression) mce.objectExpression).type?.nameWithoutPackage
                if (tn == 'Collections' &&
                    (m == 'unmodifiableList' || m == 'unmodifiableSet' || m == 'unmodifiableMap')) {
                    List<Expression> a = argList(mce)
                    if (a.size() == 1) return a.get(0)
                }
            }
        }
        e
    }

    private FactoryContainer factoryContainerFor(Expression e) {
        Expression target = e
        String kindOverride = null
        // Phase 38c — strip transparent immutability wrappers before the cast unwrap, so a
        // {@code Collections.unmodifiableList(List.of(1, 2, 3))} still recognises as a list
        // factory of {1, 2, 3} for downstream folds.
        target = unwrapImmutableWrap(target)
        // Phase 38c — keySet / values projection on a map factory: returns a fresh
        // FactoryContainer over the inner keys (as a set) or values (as a list). Composes
        // recursively, so {@code Map.of("a", 1).keySet().contains("a")} folds via this branch
        // into a singleton set factory, then the existing .contains lowering takes over.
        if (target instanceof MethodCallExpression) {
            MethodCallExpression mce = (MethodCallExpression) target
            String mm = mce.methodAsString
            if ((mm == 'keySet' || mm == 'values') && argList(mce).isEmpty()) {
                FactoryContainer inner = factoryContainerFor(mce.objectExpression)
                if (inner != null && inner.kind == 'map') {
                    if (mm == 'keySet') return new FactoryContainer(kind: 'set', args: inner.keys)
                    return new FactoryContainer(kind: 'list', args: inner.values)
                }
            }
        }
        if (target instanceof CastExpression) {
            CastExpression ce = (CastExpression) target
            // Name check rather than isAssignableFrom — we just need to distinguish "cast to Set"
            // from "cast to something else" syntactically; generics don't change the qualifier.
            if (ce.type?.name == 'java.util.Set') kindOverride = 'set'
            target = ce.expression
        }
        // Phase 38b — a local previously bound to a factory carries the same fold across the
        // variable boundary. The kind override from the outer cast (if any) doesn't apply to a
        // recorded local; the kind is what was recorded at the assignment.
        if (target instanceof VariableExpression) {
            FactoryContainer recorded = localFactories.get(((VariableExpression) target).name)
            if (recorded != null) return recorded
        }
        // Phase 79 — Tuple.tuple(a, b, …) and new TupleN(a, b, …) are fixed-arity products; model as a
        // list-kind factory so the index/size/first/last folds apply and (Phase 78) a returned tuple binds
        // result. Heterogeneous slots translate independently — each `args[k]` is its own AST expression.
        if (target instanceof MethodCallExpression) {
            MethodCallExpression tmce = (MethodCallExpression) target
            if (tmce.methodAsString == 'tuple' && isTupleReceiver(tmce.objectExpression)) {
                return new FactoryContainer(kind: 'list', args: argList(tmce))
            }
        }
        if (target instanceof ConstructorCallExpression) {
            ConstructorCallExpression cce = (ConstructorCallExpression) target
            String tn = cce.type?.nameWithoutPackage
            if (tn != null && (tn ==~ /Tuple\d+/)) {
                return new FactoryContainer(kind: 'list', args: ctorArgList(cce))
            }
        }
        // Phase 82 — nested products: a constant-slot accessor `X.vN` / `X[k]` on a list-kind product whose
        // slot expression is *itself* a product yields that nested container (so `Tuple.tuple(p, q).v1.v2`
        // and `result.v1[0]` fold through to the leaf). Recurses on the strictly smaller inner expression.
        Object[] nestAcc = slotAccessor(target)
        if (nestAcc != null) {
            FactoryContainer outer = factoryContainerFor((Expression) nestAcc[0])
            if (outer != null && outer.kind == 'list' && outer.args != null) {
                int k = (int) nestAcc[1]
                if (k >= 0 && k < outer.args.size()) return factoryContainerFor(outer.args.get(k))
            }
        }
        if (target instanceof MethodCallExpression) {
            MethodCallExpression mce = (MethodCallExpression) target
            if (mce.methodAsString == 'of' && mce.objectExpression instanceof ClassExpression) {
                String tn = ((ClassExpression) mce.objectExpression).type?.name
                List<Expression> args = argList(mce)
                if (tn == 'java.util.List') return new FactoryContainer(kind: kindOverride ?: 'list', args: args)
                if (tn == 'java.util.Set') {
                    // Phase 38c — refuse to fold {@code Set.of(...)} when literal args collide.
                    // The runtime call throws {@code IllegalArgumentException} for duplicates and
                    // the actual set has the deduped size, so folding to {@code args.size()} would
                    // claim a size the runtime never produces. Non-literal arg pairs would need
                    // Z3 to prove distinctness — out of scope; the verifier honestly skips by
                    // continuing only when all literal pairs are distinct.
                    if (hasDuplicateLiteralArgs(args)) return null
                    return new FactoryContainer(kind: 'set', args: args)
                }
                if (tn == 'java.util.Map') {
                    if (args.size() % 2 != 0) return null
                    List<Expression> ks = new ArrayList<Expression>()
                    List<Expression> vs = new ArrayList<Expression>()
                    for (int i = 0; i < args.size(); i += 2) {
                        ks.add(args.get(i))
                        vs.add(args.get(i + 1))
                    }
                    return new FactoryContainer(kind: 'map', keys: ks, values: vs)
                }
            }
        }
        if (target instanceof ListExpression) {
            return new FactoryContainer(kind: kindOverride ?: 'list', args: ((ListExpression) target).expressions)
        }
        // `new int[]{a, b, …}` — an array literal with an initializer is the array dual of a list literal:
        // a fixed-arity positional container. Model it as a list-kind factory over its initializer
        // expressions so a returned/assigned array's `result[k]` / `result.length` / component-wise `==`
        // fold via the same Phase 78/81 machinery (each slot translates in its own sort). The *sized* form
        // `new int[n]` (no initializer, `sizeExpression != null`) is a fresh symbolic array, not a literal —
        // out of this slice, so it falls through to null (honest skip).
        if (target instanceof ArrayExpression) {
            ArrayExpression ae = (ArrayExpression) target
            if (ae.sizeExpression == null) {
                return new FactoryContainer(kind: kindOverride ?: 'list', args: ae.expressions)
            }
        }
        if (target instanceof MapExpression) {
            List<Expression> ks = new ArrayList<Expression>()
            List<Expression> vs = new ArrayList<Expression>()
            for (MapEntryExpression entry : ((MapExpression) target).mapEntryExpressions) {
                ks.add(entry.keyExpression)
                vs.add(entry.valueExpression)
            }
            return new FactoryContainer(kind: 'map', keys: ks, values: vs)
        }
        null
    }

    /**
     * Phase 38b — record a factory assignment on a local: if {@code rhs} is a recognised
     * immutable-container factory, stash it in {@link #localFactories} so subsequent receiver
     * lookups against {@code name} fold the same way the factory itself would. Returns true on
     * success so the caller short-circuits the int-SSA path (the local isn't an int and there's
     * nothing to bind via the size oracle — the factory's size is the literal entry count).
     */
    boolean tryRecordFactoryAssign(String name, Expression rhs) {
        FactoryContainer f = factoryContainerFor(rhs)
        if (f == null) return tryRecordSizedArrayAssign(name, rhs)
        localFactories.put(name, f)
        // Pin the oracles the surrounding machinery consults independently of the factory fold:
        //  (1) nullity — a factory result is non-null, so the implicit scalar-deref check on
        //      {@code xs.size()}/{@code m.get(k)}/etc. has its obligation immediately discharged.
        //  (2) size — for list/set kinds, fix {@code sizeOf(name)} to the literal entry count, so
        //      the implicit bounds check on {@code xs[i]} closes the same way (sound: this is
        //      what the factory's runtime size actually is, modulo Set dedup which is a known
        //      limit). Map factories don't need a size pin: {@code m.size()} folds via the
        //      factory fold, and the underlying map-vals/key-set handles aren't queried directly.
        session.assertExpr(session.not(nullityOf(name)))
        if (f.kind == 'list' || f.kind == 'set') {
            session.assertExpr(session.eq(sizeOf(name), session.intLit((long) f.entryCount())))
        }
        true
    }

    /**
     * A *sized* array allocation {@code new int[n]} — an {@link ArrayExpression} with a single
     * dimension size and no initializer (the dual of the fixed-arity {@code new int[]{…}} literal that
     * {@link #factoryContainerFor} records). There is no element list, so this is modelled through the
     * size/array oracles rather than a {@link FactoryContainer}: {@code sizeOf(name) == n}, non-null,
     * and — for an Int-element array — a const-0 content array (Java zero-fills a fresh array), so an
     * unwritten {@code name[i]} reads {@code 0} and a later {@code name[i] = v} store threads from there.
     * Returns true so the caller short-circuits the int-SSA path (the target is an array, not an int).
     *
     * <p>Single dimension only; a non-Int element sort keeps havoced contents (sound, just no zero
     * default). The {@code n < 0} {@code NegativeArraySizeException} is not modelled — a negative size
     * yields an unsatisfiable index range, so no out-of-bounds is mis-verified.
     */
    boolean tryRecordSizedArrayAssign(String name, Expression rhs) {
        Expression target = rhs
        if (target instanceof CastExpression) target = ((CastExpression) target).expression
        if (!(target instanceof ArrayExpression)) return false
        ArrayExpression ae = (ArrayExpression) target
        List<Expression> dims = ae.sizeExpression
        if (dims == null || dims.size() != 1) return false                       // single-dimension `new T[n]` only
        if (ae.expressions != null && !ae.expressions.isEmpty()) return false     // has an initializer → factory path
        try {
            Object sizeH = translate(dims.get(0))
            if (sizeH == null) return false
            localFactories.remove(name)                                          // drop any stale factory record
            bindSize(name, sizeH)
            session.assertExpr(session.not(nullityOf(name)))
            Object[] sorts = arraySortsFor(name)
            if (sorts[1] == session.intSort()) {
                bindArray(name, session.constIntArray(session.intLit(0L)))
            }
            return true
        } catch (Exception ignored) {
            return false                                                          // unmodelled size/sort → honest skip
        }
    }

    /**
     * Phase 38d — drop a factory record from {@link #localFactories}. Called by
     * {@code applyListMutation} after {@code xs.add(v)} / {@code xs.removeLast()} / {@code
     * xs.clear()} so subsequent {@code factoryContainerFor(xs)} lookups fall through to the
     * threaded {@code sizeOf}/{@code arrayFor} oracles (which Phase 40 keeps current across
     * the mutation) rather than the now-stale literal-arg list. Closes a soundness gap where
     * {@code xs = []; xs.add(v); xs.size()} folded to 0.
     */
    void clearFactoryRecord(String name) {
        localFactories.remove(name)
    }

    /** Disjunction of equalities — {@code x == a_0 ∨ x == a_1 ∨ …}; null if any element fails to translate. */
    private Object foldContainsDisjunction(Object xH, List<Expression> elems) {
        if (elems.isEmpty()) return session.boolLit(false)
        List<Object> disjuncts = new ArrayList<Object>()
        for (Expression el : elems) {
            Object elH = translate(el)
            if (elH == null) return null
            disjuncts.add(session.eq(xH, elH))
        }
        disjuncts.size() == 1 ? disjuncts.get(0) : session.or(disjuncts)
    }

    /**
     * Phase 38 — fold a method call on a recognised factory receiver. Returns null when the op
     * isn't one we recognise on this kind (caller falls through to honest skip).
     */
    private Object foldFactoryMethodCall(FactoryContainer f, String m, List<Expression> args) {
        if (m == 'size' && args.isEmpty()) return session.intLit(f.entryCount().longValue())
        if (m == 'isEmpty' && args.isEmpty()) return session.boolLit(f.entryCount() == 0)
        if (m == 'contains' && args.size() == 1 && (f.kind == 'list' || f.kind == 'set')) {
            Object xH = translate(args.get(0))
            if (xH == null) return null
            return foldContainsDisjunction(xH, f.args)
        }
        if (m == 'containsKey' && args.size() == 1 && f.kind == 'map') {
            Object xH = translate(args.get(0))
            if (xH == null) return null
            return foldContainsDisjunction(xH, f.keys)
        }
        if (m == 'containsValue' && args.size() == 1 && f.kind == 'map') {
            Object xH = translate(args.get(0))
            if (xH == null) return null
            return foldContainsDisjunction(xH, f.values)
        }
        if (m == 'get' && args.size() == 1) {
            if (f.kind == 'list') return foldFactoryListIndex(f.args, args.get(0))
            if (f.kind == 'map')  return foldFactoryMapLookup(f, args.get(0))
        }
        // Phase 39 — first/head/last on a list/set factory fold to the literal at position 0
        // or size-1. Both ops on an empty factory fold to null (the JDK throws at runtime); the
        // fold returns null too so the call surfaces as honest skip rather than picking a wrong
        // element.
        if ((m == 'first' || m == 'head') && args.isEmpty() && (f.kind == 'list' || f.kind == 'set')) {
            return f.args.isEmpty() ? null : translate(f.args.get(0))
        }
        if (m == 'last' && args.isEmpty() && (f.kind == 'list' || f.kind == 'set')) {
            return f.args.isEmpty() ? null : translate(f.args.get(f.args.size() - 1))
        }
        // Phase 79 — TupleN slot accessor methods: getV1()..getV16() and second() (first/head/last/get
        // are handled above). The slot value is the k-th constructed element, in its own sort.
        if (args.isEmpty() && f.kind == 'list' && f.args != null) {
            int si = tupleSlotIndex(m)
            if (si >= 0 && si < f.args.size()) return translate(f.args.get(si))
        }
        null
    }

    /**
     * {@code listFactory.get(i)} / {@code [a, b, c][i]} — direct lookup for a literal {@code i}
     * in range, otherwise an ite-chain {@code ite(i==0, a, ite(i==1, b, …, default))} where
     * {@code default} is a fresh unconstrained Int (Phase 38c).
     *
     * <p>Soundness for the symbolic-i case rests on the user constraining {@code i} to
     * {@code [0, size)} via {@code @Requires} — out-of-range {@code i} resolves to the
     * unconstrained default, so any @Ensures that asserts a specific element must refute
     * unless the constraint rules out the out-of-range case. (The verifier doesn't synthesise
     * a bounds-check obligation for a factory expression because the factory has no named
     * receiver to attach a size oracle to; the @Requires path is the contract.)
     */
    private Object foldFactoryListIndex(List<Expression> elems, Expression idxExpr) {
        Object idxH = translate(idxExpr)
        if (idxH == null) return null
        if (elems.isEmpty()) return null
        // Const-i fast path.
        if (idxExpr instanceof ConstantExpression) {
            Object v = ((ConstantExpression) idxExpr).value
            if (v instanceof Integer || v instanceof Long || v instanceof Short || v instanceof Byte) {
                int idx = ((Number) v).intValue()
                if (idx >= 0 && idx < elems.size()) return translate(elems.get(idx))
                // Out-of-range literal index — fall through to the ite-chain so the default
                // branch fires (and the @Ensures correctly refutes for the wrong literal).
            }
        }
        // Symbolic-i (or out-of-range literal): build the ite-chain from right to left.
        Object defaultV = session.intVar('factory$out$' + (quantCounter++))
        Object current = defaultV
        for (int i = elems.size() - 1; i >= 0; i--) {
            Object elH = translate(elems.get(i))
            if (elH == null) return null   // any element outside fragment → honest skip
            current = session.ite(session.eq(idxH, session.intLit((long) i)), elH, current)
        }
        current
    }

    /** {@code mapFactory.get(k)} / {@code mapFactory[k]} — ite-chain over the literal entries. */
    /** Map property names that are the JDK/Groovy API, not data keys — never folded to a key read. */
    private static final Set<String> MAP_RESERVED_PROPS = ['empty', 'class', 'metaClass'] as Set

    /**
     * Phase 84 — {@code m.key} (property form) on a map <em>parameter</em>: the value at the constant string
     * key, read through the map's value array (the dual of {@link #foldMapPropertyByName} for factories).
     * `m.sum` ≡ `m['sum']`. Null unless {@code obj} is a String-keyed map and {@code prop} isn't reserved.
     */
    private Object foldMapParamProperty(Expression obj, String prop) {
        if (MAP_RESERVED_PROPS.contains(prop)) return null
        String mlog = mapLogicalFor(obj)
        if (mlog == null) return null
        ClassNode[] pair = mapTypes.get(mlog)
        // Only an explicitly String-keyed map (`Map<String, V>`) supports `m.prop` as a named-key access.
        // A raw / non-String-keyed map skips — both because `m.prop` isn't a meaningful string key there and
        // to avoid a value-array key-domain mismatch (the value array is String-keyed). The try/catch is a
        // belt-and-suspenders against any residual sort mismatch — a clean skip, never a crash.
        if (pair == null || pair[0] == null || pair[0].name != 'java.lang.String') return null
        Object keyH = translateInSort(new ConstantExpression(prop), sortFor(pair[0]))
        if (keyH == null) return null
        try {
            return session.select(mapValsFor(mlog), keyH)
        } catch (Exception ignored) {
            return null
        }
    }

    /**
     * Phase 83 — the value at a constant string key {@code propName} in a map factory, by direct
     * compile-time key match (no SMT key equality), or null if {@code f} isn't a map or {@code propName}
     * isn't one of its (constant) keys. Backs the Groovy {@code m.key} map-as-named-tuple property access.
     */
    private Object foldMapPropertyByName(FactoryContainer f, String propName) {
        if (f == null || f.kind != 'map' || f.keys == null) return null
        for (int i = 0; i < f.keys.size(); i++) {
            Expression k = f.keys.get(i)
            if (k instanceof ConstantExpression && propName == String.valueOf(((ConstantExpression) k).value)) {
                return translate(f.values.get(i))
            }
        }
        null
    }

    private Object foldFactoryMapLookup(FactoryContainer f, Expression keyExpr) {
        Object kH = translate(keyExpr)
        if (kH == null) return null
        // If kH matches one of the entry keys symbolically, that's the value. For runtime mismatch
        // the JDK throws; we only fold the in-range case via an ite chain.
        // Build right-to-left: for entries [(k_0,v_0), …, (k_{n-1},v_{n-1})], emit
        //   ite(k == k_{n-1}, v_{n-1}, ite(k == k_{n-2}, v_{n-2}, … default))
        // The default is the last value — semantically wrong for true misses, but folds are only
        // exercised when the user asserts the key matches one of the entries (otherwise the result
        // is unconstrained, which Z3 will treat as a free unknown — sound for our refute discipline).
        if (f.keys.isEmpty()) return null
        Object current = translate(f.values.get(f.keys.size() - 1))
        if (current == null) return null
        for (int i = f.keys.size() - 2; i >= 0; i--) {
            Object kiH = translate(f.keys.get(i))
            Object viH = translate(f.values.get(i))
            if (kiH == null || viH == null) return null
            current = session.ite(session.eq(kH, kiH), viH, current)
        }
        current
    }

    private Object translateSetEquals(String sKey, Expression tExpr) {
        Object forward = translateContainsAll(sKey, tExpr)
        if (forward == null) return null
        String tKey = setKeyFor(tExpr)
        if (tKey == null) return null
        // Reverse direction: build a VariableExpression-shaped wrapper for the receiver's key so
        // translateContainsAll can resolve it back. The receiver name is the setKey itself for a
        // plain receiver; for an old-snapshot key, strip the old$ prefix.
        String sName = sKey.startsWith('old$') ? sKey.substring('old$'.length()) : sKey
        Expression sAsExpr = new VariableExpression(sName)
        Object backward = translateContainsAll(tKey, sAsExpr)
        if (backward == null) return null
        session.and([forward, backward])
    }

    /**
     * Phase 32a — lower {@code m.containsValue(v)} to the finite disjunction
     * {@code (m[c_1] == v) ∨ … ∨ (m[c_N] == v)} over an enum-keyed map's key constants.
     * The existential mirror of {@link #translateContainsAll}: instead of "every key implies
     * membership", "some key matches the value". Returns null for non-enum key sorts (no finite
     * domain to enumerate) — Int/String keys honestly skip.
     */
    private Object translateMapContainsValue(String mapLog, Expression vExpr) {
        ClassNode[] pair = mapTypes.get(mapLog)
        if (pair == null) return null
        ClassNode keyType = pair[0]
        if (keyType == null || !(keyType.isEnum() || isEnumLikeType(keyType))) return null
        Object vSort = sortFor(pair[1])
        Object vH = translateInSort(vExpr, vSort)
        if (vH == null) return null
        Object valsArr = mapValsFor(mapLog)
        Object keySort = session.declareSort(enumSortName(keyType))
        List<Object> disjuncts = new ArrayList<Object>()
        for (String constName : enumConstantNames(keyType)) {
            Object keyLit = session.litOfSort(keySort, constName)
            disjuncts.add(session.eq(session.select(valsArr, keyLit), vH))
        }
        disjuncts.isEmpty() ? session.boolLit(false) : session.or(disjuncts)
    }

    private Object translateContainsAll(String sKey, Expression tExpr) {
        String tKey = setKeyFor(tExpr)
        if (tKey == null) return null
        Object sElemSort = setKeySortForKey(sKey)
        Object tElemSort = setKeySortForKey(tKey)
        if (sElemSort != tElemSort) return null
        Object sH = setFor(sKey)
        Object tH = setFor(tKey)
        // Int case: needs a bound on t from a prior Sets.boundedBy(t, n) in the same session.
        if (sElemSort == session.intSort()) {
            Object nH = intSubsetBounds.get(tKey)
            if (nH == null) return null
            Object iv = session.boundIntVar('subset$i' + (quantCounter++))
            Object inRange = session.and([session.le(session.intLit(0L), iv), session.lt(iv, nH)])
            Object body = session.implies(member(tH, iv), member(sH, iv))
            Object matrix = session.implies(inRange, body)
            return session.forall([iv], matrix, [session.select(tH, iv), session.select(sH, iv)])
        }
        // Enum case: finite conjunction over the enum's constants.
        ClassNode elemType = elementTypeForSetKey(sKey)
        if (elemType != null && (elemType.isEnum() || isEnumLikeType(elemType))) {
            Object enumSort = session.declareSort(enumSortName(elemType))
            List<Object> conjuncts = new ArrayList<Object>()
            for (String constName : enumConstantNames(elemType)) {
                Object constLit = session.litOfSort(enumSort, constName)
                conjuncts.add(session.implies(member(tH, constLit), member(sH, constLit)))
            }
            return conjuncts.isEmpty() ? session.boolLit(true) : session.and(conjuncts)
        }
        null
    }

    /**
     * Phase 29 — finite-domain conjunction {@code c1 ∈ s ∧ c2 ∈ s ∧ ... ∧ cN ∈ s} over the
     * enum's constants. The encoder-side replacement for the Int-domain bounded universal
     * {@code ∀ i. 0<=i<n ⟹ i ∈ s}, used when {@code Sets.boundedBy}/{@code Sets.boundedCount} reach an
     * enum-element set with n matching the enum's domain size.
     */
    private Object finiteEnumCoverage(Object setH, ClassNode enumType) {
        Object sort = session.declareSort(enumSortName(enumType))
        List<Object> conjuncts = new ArrayList<Object>()
        for (String constName : enumConstantNames(enumType)) {
            Object constLit = session.litOfSort(sort, constName)
            conjuncts.add(member(setH, constLit))
        }
        conjuncts.isEmpty() ? session.boolLit(true) : session.and(conjuncts)
    }

    /** Re-bind a set name to a new handle — threads an add/remove as {@code s := (store s x 1|0)}. */
    void bindSet(String key, Object handle) { setEnv.put(key, handle) }

    /** Current set binding, or null — for save/restore around a call's framing. */
    Object peekSet(String key) { setEnv.get(key) }

    /** Set analogue of {@link #havocArray}: re-bind a set name's contents to a fresh, unconstrained set. */
    Object havocSet(String key) {
        Object v = session.setVar(key + '$havoc$' + (havocCounter++))
        setEnv.put(key, v)
        v
    }

    /** Map analogue of {@link #havocArray}: re-bind a map name's value array and key-set to fresh ones. */
    void havocMap(String name) {
        putMapVals(name, session.arrayVar(mapValsKey(name) + '$havoc$' + (havocCounter++)))
        putMapKeys(name, session.setVar(mapKeysKey(name) + '$havoc$' + (havocCounter++)))
    }

    /** Re-bind a receiver's size oracle to a fresh, unconstrained {@code >= 0} integer. */
    void havocSize(String name) {
        Object v = session.intVar(name + '.size$havoc$' + (havocCounter++))
        session.assertExpr(session.ge(v, session.intLit(0L)))
        sizeEnv.put(name + '.size', v)
    }

    /** Membership {@code x ∈ s}, over a characteristic-array set handle: {@code (select s x) == 1}. */
    Object member(Object setHandle, Object elem) {
        session.eq(session.select(setHandle, elem), session.intLit(1L))
    }

    /** Cardinality {@code |s|} of a set handle, asserting {@code >= 0} the first time each handle is seen. */
    Object cardOf(Object setHandle) {
        Object c = session.setCard(setHandle)
        if (cardConstrained.add(setHandle)) session.assertExpr(session.ge(c, session.intLit(0L)))
        c
    }

    /** Set handles for which a {@code bcount(s,k)} term has had its bound axiom asserted (mint-once). */
    private final Set<Object> countConstrained = new HashSet<Object>()

    /**
     * The bounded-sum cardinality {@code bcount(s, k)} of a set handle, asserting its sound bound axiom
     * the first time each term is seen: {@code 0 <= bcount}, {@code k >= 0 ⟹ bcount <= k}, and
     * {@code k <= 0 ⟹ bcount == 0}. All three are theorems of the intended meaning (count of members in
     * {@code [0,k)}), so asserting them keeps the uninterpreted symbol consistent with — and as strong as —
     * the count it models, without an inductive proof at the use site.
     */
    Object setCountOf(Object setHandle, Object kH) {
        Object c = session.setCount(setHandle, kH)
        if (countConstrained.add(c)) {
            Object zero = session.intLit(0L)
            session.assertExpr(session.ge(c, zero))
            session.assertExpr(session.or([session.lt(kH, zero), session.le(c, kH)]))   // k >= 0 ⟹ c <= k
            session.assertExpr(session.or([session.gt(kH, zero), session.eq(c, zero)])) // k <= 0 ⟹ c == 0
            // Full-characterization (Phase 22): bcount(s,k) == k  ⟺  s covers [0,k). Both directions are
            // theorems of the count's meaning (k members in k slots ⟺ every slot a member), so asserting
            // the iff keeps the primitive as strong as the count — this is the converse of Phase 20's
            // "full ⟹ count = k", and the fact a cardinality-terminating DFS needs to prove coverage.
            session.assertExpr(session.eq(session.eq(c, kH), domainCoverageForall(setHandle, kH)))
        }
        c
    }

    /** Array handles whose sum base/step axioms have been asserted (mint-once, per array). */
    private final Set<Object> sumConstrained = new HashSet<Object>()

    /**
     * The bounded sum {@code sum(arr, lo, hi) = Σ_{lo<=i<hi} arr[i]}, asserting its two defining axioms
     * the first time each array handle is seen (quantified over all ranges, so once per array suffices):
     * <ul>
     *   <li>base — {@code ∀ l,h. h <= l ⟹ sum(arr,l,h) == 0}</li>
     *   <li>step — {@code ∀ l,h. l < h ⟹ sum(arr,l,h) == sum(arr,l,h-1) + arr[h-1]}</li>
     * </ul>
     * The step axiom is what makes a loop invariant {@code s == sum(arr,0,i)} provable: at {@code i+1}
     * it e-matches to {@code sum(arr,0,i+1) == sum(arr,0,i) + arr[i]}, exactly the body's update.
     */
    Object sumOf(Object arr, Object loH, Object hiH) {
        if (sumConstrained.add(arr)) {
            Object zero = session.intLit(0L)
            Object one = session.intLit(1L)
            // base
            Object bl = session.boundIntVar('sum$bl' + (quantCounter++))
            Object bh = session.boundIntVar('sum$bh' + (quantCounter++))
            Object bterm = session.sum(arr, bl, bh)
            session.assertExpr(session.forall([bl, bh],
                session.implies(session.le(bh, bl), session.eq(bterm, zero)), [bterm]))
            // step
            Object sl = session.boundIntVar('sum$sl' + (quantCounter++))
            Object sh = session.boundIntVar('sum$sh' + (quantCounter++))
            Object sterm = session.sum(arr, sl, sh)
            Object hm1 = session.minus(sh, one)
            Object rhs = session.plus(session.sum(arr, sl, hm1), session.select(arr, hm1))
            session.assertExpr(session.forall([sl, sh],
                session.implies(session.lt(sl, sh), session.eq(sterm, rhs)), [sterm]))
        }
        session.sum(arr, loH, hiH)
    }

    /** Array handles whose Real-sum base/step axioms have been asserted (mint-once, per array). */
    private final Set<Object> sumRealConstrained = new HashSet<Object>()

    /**
     * Phase 70 — the Real-element analogue of {@link #sumOf}: the bounded sum over an {@code Array Int
     * Real} (a {@code List<BigDecimal>}'s contents), with base ({@code h <= l ⟹ sumReal == 0.0}) and
     * step ({@code l < h ⟹ sumReal(l,h) == sumReal(l,h-1) + arr[h-1]}) axioms over Z3's Real sort.
     */
    Object sumRealOf(Object arr, Object loH, Object hiH) {
        if (sumRealConstrained.add(arr)) {
            Object zero = session.realLit('0')
            Object one = session.intLit(1L)
            Object bl = session.boundIntVar('sumR$bl' + (quantCounter++))
            Object bh = session.boundIntVar('sumR$bh' + (quantCounter++))
            Object bterm = session.sumReal(arr, bl, bh)
            session.assertExpr(session.forall([bl, bh],
                session.implies(session.le(bh, bl), session.eq(bterm, zero)), [bterm]))
            Object sl = session.boundIntVar('sumR$sl' + (quantCounter++))
            Object sh = session.boundIntVar('sumR$sh' + (quantCounter++))
            Object sterm = session.sumReal(arr, sl, sh)
            Object hm1 = session.minus(sh, one)
            Object rhs = session.plus(session.sumReal(arr, sl, hm1), session.select(arr, hm1))
            session.assertExpr(session.forall([sl, sh],
                session.implies(session.lt(sl, sh), session.eq(sterm, rhs)), [sterm]))
        }
        session.sumReal(arr, loH, hiH)
    }

    /** Array handles whose product base/step axioms have been asserted (mint-once, per array). */
    private final Set<Object> prodConstrained = new HashSet<Object>()

    /**
     * The bounded product {@code prod(arr, lo, hi) = Π_{lo<=i<hi} arr[i]}, the multiplicative sibling
     * of {@link #sumOf}. Axioms asserted mint-once per array: base {@code ∀ l,h. h <= l ⟹ prod == 1}
     * (the empty product), step {@code ∀ l,h. l < h ⟹ prod(arr,l,h) == prod(arr,l,h-1) * arr[h-1]}.
     * A loop invariant {@code p == prod(arr,0,i)} is preserved by {@code p = p * arr[i]} (the step at
     * {@code i+1} gives {@code prod(arr,0,i+1) == prod(arr,0,i) * arr[i]} — a congruence, not NIA).
     */
    Object prodOf(Object arr, Object loH, Object hiH) {
        if (prodConstrained.add(arr)) {
            Object one = session.intLit(1L)
            // base — empty product is 1
            Object bl = session.boundIntVar('prod$bl' + (quantCounter++))
            Object bh = session.boundIntVar('prod$bh' + (quantCounter++))
            Object bterm = session.prod(arr, bl, bh)
            session.assertExpr(session.forall([bl, bh],
                session.implies(session.le(bh, bl), session.eq(bterm, one)), [bterm]))
            // step
            Object sl = session.boundIntVar('prod$sl' + (quantCounter++))
            Object sh = session.boundIntVar('prod$sh' + (quantCounter++))
            Object sterm = session.prod(arr, sl, sh)
            Object hm1 = session.minus(sh, one)
            Object rhs = session.times(session.prod(arr, sl, hm1), session.select(arr, hm1))
            session.assertExpr(session.forall([sl, sh],
                session.implies(session.lt(sl, sh), session.eq(sterm, rhs)), [sterm]))
        }
        session.prod(arr, loH, hiH)
    }

    /**
     * Resolve a list-aggregation receiver to {@code [listName, arrayHandle, loH, hiH]}, or null.
     * Handles the whole-list {@code xs} (range {@code [0, size)}) and the sublist {@code xs[lo..<hi]};
     * an inclusive {@code ..} range normalises to half-open. The element type is *not* gated here — the
     * caller decides (Int → `sum$`/`prod$`, String → `strConcat$`, other → skip) from {@code listName}.
     */
    private Object[] listAggHandles(Expression recv) {
        if (recv instanceof BinaryExpression &&
            ((BinaryExpression) recv).operation.type == Types.LEFT_SQUARE_BRACKET &&
            ((BinaryExpression) recv).leftExpression instanceof VariableExpression &&
            ((BinaryExpression) recv).rightExpression instanceof RangeExpression) {
            BinaryExpression sub = (BinaryExpression) recv
            String xs = ((VariableExpression) sub.leftExpression).name
            RangeExpression re = (RangeExpression) sub.rightExpression
            Object lo = translate(re.from)
            Object hi = translate(re.to)
            if (lo == null || hi == null) return null
            if (re.inclusive) hi = session.plus(hi, session.intLit(1L))
            return [xs, arrayFor(xs), lo, hi] as Object[]
        }
        if (recv instanceof VariableExpression) {
            String xs = ((VariableExpression) recv).name
            return [xs, arrayFor(xs), session.intLit(0L), sizeOf(xs)] as Object[]
        }
        // Phase 69 — old.xs.sum(): the entry-snapshot array over the same [0, size) range, so a
        // postcondition can compare the final total to the entry total (`xs.sum() == old.xs.sum()`).
        if (recv instanceof PropertyExpression && isOldReceiver(((PropertyExpression) recv).objectExpression)) {
            String prop = ((PropertyExpression) recv).propertyAsString
            return ['old$' + prop, arrayFor('old$' + prop), session.intLit(0L), sizeOf(prop)] as Object[]
        }
        null
    }

    /** Cache of minted {@code max()}/{@code min()} extremum constants, keyed by receiver-text + op. */
    private final Map<String, Object> extremumCache = new HashMap<String, Object>()

    /**
     * Model {@code xs.max()} / {@code xs.min()} over the {@code elemSort}-typed contents of {@code arr} on
     * the half-open range {@code [loH, hiH)} as a fresh constant {@code r} carrying the two facts that
     * define an extremum (Phase 60; sort-generic since Phase 76): {@code r} bounds every element
     * ({@code ∀i. lo<=i<hi ⟹ a[i] <= r}, or {@code >=} for min, triggered on {@code a[i]}) and {@code r}
     * is *achieved* by some element ({@code ∃j. lo<=j<hi ∧ a[j] == r}). Only the extremum constant is
     * sort-specific; the order comparisons ({@code le}/{@code ge}) and {@code eq} are arithmetic-polymorphic
     * over Int and Real in Z3, so they're unchanged. The achieved-fact is guarded by non-emptiness
     * ({@code lo < hi ⟹ …}) so an empty range — Groovy's {@code [].max()} is undefined — cannot make
     * the context vacuously unsatisfiable and "prove" anything. Mint-once per receiver so repeated
     * {@code xs.max()} occurrences are the same term.
     */
    Object maxMinOf(String key, Object arr, Object loH, Object hiH, boolean isMax, Object elemSort, boolean fpElem) {
        Object cached = extremumCache.get(key)
        if (cached != null) return cached
        Object r = varOfSort('extremum$' + (quantCounter++), elemSort)
        extremumCache.put(key, r)
        Object iv = session.boundIntVar('ext$b' + (quantCounter++))
        Object seli = session.select(arr, iv)
        Object rangei = session.and([session.le(loH, iv), session.lt(iv, hiH)])
        Object jv = session.boundIntVar('ext$a' + (quantCounter++))
        Object selj = session.select(arr, jv)
        Object rangej = session.and([session.le(loH, jv), session.lt(jv, hiH)])
        if (fpElem) {
            // FP is *not* totally ordered: Groovy's max/min returns NaN when any element is NaN, and NaN is
            // not fpLeq-comparable nor fpEq to anything. So the bound/achieved facts hold only under
            // all-non-NaN — asserted conditionally on that guard so an array that *might* contain NaN can't
            // make the context vacuous (the guard is just false then). A developer proves an FP-extremum
            // property under a `!Double.isNaN` precondition, which discharges the guard.
            Object nv = session.boundIntVar('ext$n' + (quantCounter++))
            Object seln = session.select(arr, nv)
            Object rangen = session.and([session.le(loH, nv), session.lt(nv, hiH)])
            Object allNonNaN = session.forall([nv],
                session.implies(rangen, session.not(session.fpIsNaN(seln))), [seln])
            Object bound = isMax ? session.fpLeq(seli, r) : session.fpGeq(seli, r)
            session.assertExpr(session.implies(allNonNaN,
                session.forall([iv], session.implies(rangei, bound), [seli])))
            Object ach = session.exists([jv], session.and([rangej, session.fpEq(selj, r)]), [selj])
            session.assertExpr(session.implies(allNonNaN, session.implies(session.lt(loH, hiH), ach)))
            return r
        }
        // Int / Real — totally ordered, so le/ge/eq (arithmetic-polymorphic in Z3) and no NaN guard.
        // bound: ∀i. lo <= i < hi ⟹ (isMax ? a[i] <= r : a[i] >= r)
        Object bound = isMax ? session.le(seli, r) : session.ge(seli, r)
        session.assertExpr(session.forall([iv], session.implies(rangei, bound), [seli]))
        // achieved (guarded non-empty): lo < hi ⟹ ∃j. lo <= j < hi ∧ a[j] == r
        Object ach = session.exists([jv], session.and([rangej, session.eq(selj, r)]), [selj])
        session.assertExpr(session.implies(session.lt(loH, hiH), ach))
        return r
    }

    /** A fresh scalar variable in {@code sort} — Int, Real, or IEEE-754 (double/float). */
    private Object varOfSort(String name, Object sort) {
        if (sort == session.realSort()) return session.realVar(name)
        if (sort == session.fpSort(true)) return session.fpVar(name, true)
        if (sort == session.fpSort(false)) return session.fpVar(name, false)
        return session.intVar(name)
    }

    /** Array handles whose String-concat base/step axioms have been asserted (mint-once, per array). */
    private final Set<Object> strConcatConstrained = new HashSet<Object>()

    /**
     * The bounded string concatenation {@code concat(arr, lo, hi)} over a {@code (Int -> String)} array
     * — the String-monoid analogue of {@link #sumOf}, for Groovy's {@code ['a','b'].sum() == 'ab'}.
     * Axioms asserted mint-once per array: base {@code ∀ l,h. h <= l ⟹ concat == ""}, step
     * {@code ∀ l,h. l < h ⟹ concat(arr,l,h) == concat(arr,l,h-1) ++ arr[h-1]} (via Z3 seq {@code str.++}).
     */
    Object strConcatOf(Object arr, Object loH, Object hiH) {
        if (strConcatConstrained.add(arr)) {
            Object strSort = session.declareSort('String')
            Object empty = session.litOfSort(strSort, '')
            Object one = session.intLit(1L)
            // base — empty concatenation is ""
            Object bl = session.boundIntVar('cat$bl' + (quantCounter++))
            Object bh = session.boundIntVar('cat$bh' + (quantCounter++))
            Object bterm = session.strConcatRange(arr, bl, bh)
            session.assertExpr(session.forall([bl, bh],
                session.implies(session.le(bh, bl), session.eq(bterm, empty)), [bterm]))
            // step
            Object sl = session.boundIntVar('cat$sl' + (quantCounter++))
            Object sh = session.boundIntVar('cat$sh' + (quantCounter++))
            Object sterm = session.strConcatRange(arr, sl, sh)
            Object hm1 = session.minus(sh, one)
            Object rhs = session.stringConcat(session.strConcatRange(arr, sl, hm1), session.select(arr, hm1))
            session.assertExpr(session.forall([sl, sh],
                session.implies(session.lt(sl, sh), session.eq(sterm, rhs)), [sterm]))
        }
        session.strConcatRange(arr, loH, hiH)
    }

    /** True if {@code t} is the {@code String} element type. */
    private static boolean isStringElementType(ClassNode t) { t != null && t.name == 'java.lang.String' }

    /** Phase 70 — true if {@code t} is a decimal element type (BigDecimal/Double/Float), modelled as Real. */
    private static boolean isDecimalElementType(ClassNode t) {
        if (t == null) return false
        String n = t.name
        n == 'java.math.BigDecimal'   // Phase 72 — only BigDecimal is exact; double/float are IEEE-754
    }

    /** Whether {@code t} is an IEEE-754 element type — {@code double}/{@code float} (Phase 77 FP arrays). */
    private static boolean isFpElementType(ClassNode t) {
        String n = t?.name
        n == 'double' || n == 'java.lang.Double' || n == 'float' || n == 'java.lang.Float'
    }

    /** Double precision (Float64) vs single (Float32) for an FP element type. */
    private static boolean isFpDoubleType(ClassNode t) {
        String n = t?.name
        n == 'double' || n == 'java.lang.Double'
    }

    /** Whether fib's defining axioms have been asserted (mint-once — fib is one global function). */
    private boolean fibConstrained = false

    /**
     * The Fibonacci function {@code fib(k)}, asserting its defining axioms the first time it is seen:
     * base {@code fib(0)==0} / {@code fib(1)==1}, step {@code ∀k. k>=2 ⟹ fib(k)==fib(k-1)+fib(k-2)}.
     * The step (triggered on {@code fib(k)}) is what preserves a generation invariant {@code b ==
     * Fib.of(i+1)} across {@code b = a + b}: at {@code i+2} it e-matches to {@code fib(i+2) ==
     * fib(i+1) + fib(i)}, exactly the body's update (a congruence, not a fresh nonlinearity).
     */
    Object fibOf(Object kH) {
        if (!fibConstrained) {
            fibConstrained = true
            Object zero = session.intLit(0L), one = session.intLit(1L), two = session.intLit(2L)
            session.assertExpr(session.eq(session.fib(zero), zero))
            session.assertExpr(session.eq(session.fib(one), one))
            Object k = session.boundIntVar('fib$k' + (quantCounter++))
            Object term = session.fib(k)
            Object rhs = session.plus(session.fib(session.minus(k, one)), session.fib(session.minus(k, two)))
            session.assertExpr(session.forall([k], session.implies(session.ge(k, two), session.eq(term, rhs)), [term]))
        }
        session.fib(kH)
    }

    /** Whether trib's defining axioms have been asserted (mint-once — trib is one global function). */
    private boolean tribConstrained = false
    private boolean gcdConstrained = false
    private boolean lcmConstrained = false

    /**
     * The tribonacci function {@code trib(k)} (HumanEval 063 {@code fibfib}), asserting its defining axioms
     * the first time it is seen: base {@code trib(0)==0} / {@code trib(1)==0} / {@code trib(2)==1}, step
     * {@code ∀k. k>=3 ⟹ trib(k)==trib(k-1)+trib(k-2)+trib(k-3)}. The three-term sibling of {@link #fibOf}:
     * the step (triggered on {@code trib(k)}) preserves a generation invariant {@code c == Trib.of(i+2)}
     * across {@code c = a + b + c} by e-matching to {@code trib(i+3) == trib(i+2)+trib(i+1)+trib(i)}.
     */
    Object tribOf(Object kH) {
        if (!tribConstrained) {
            tribConstrained = true
            Object zero = session.intLit(0L), one = session.intLit(1L)
            Object two = session.intLit(2L), three = session.intLit(3L)
            session.assertExpr(session.eq(session.trib(zero), zero))
            session.assertExpr(session.eq(session.trib(one), zero))
            session.assertExpr(session.eq(session.trib(two), one))
            Object k = session.boundIntVar('trib$k' + (quantCounter++))
            Object term = session.trib(k)
            Object rhs = session.plus(session.plus(session.trib(session.minus(k, one)),
                                                   session.trib(session.minus(k, two))),
                                      session.trib(session.minus(k, three)))
            session.assertExpr(session.forall([k], session.implies(session.ge(k, three), session.eq(term, rhs)), [term]))
        }
        session.trib(kH)
    }

    private boolean tetraConstrained = false
    /**
     * The fib4 / tetranacci function {@code tetra(k)} (HumanEval 046 {@code fib4}), asserting its defining axioms
     * the first time it is seen: base {@code tetra(0)==0} / {@code tetra(1)==0} / {@code tetra(2)==2} /
     * {@code tetra(3)==0}, step {@code ∀k. k>=4 ⟹ tetra(k)==tetra(k-1)+tetra(k-2)+tetra(k-3)+tetra(k-4)}. The
     * four-term sibling of {@link #tribOf}: the step (triggered on {@code tetra(k)}) preserves a generation
     * invariant {@code d == Tetra.of(i+3)} across {@code e = a+b+c+d} by e-matching to
     * {@code tetra(i+4) == tetra(i+3)+tetra(i+2)+tetra(i+1)+tetra(i)}.
     */
    Object tetraOf(Object kH) {
        if (!tetraConstrained) {
            tetraConstrained = true
            Object zero = session.intLit(0L), one = session.intLit(1L), two = session.intLit(2L)
            Object three = session.intLit(3L), four = session.intLit(4L)
            session.assertExpr(session.eq(session.tetra(zero), zero))
            session.assertExpr(session.eq(session.tetra(one), zero))
            session.assertExpr(session.eq(session.tetra(two), two))
            session.assertExpr(session.eq(session.tetra(three), zero))
            Object k = session.boundIntVar('tetra$k' + (quantCounter++))
            Object term = session.tetra(k)
            Object rhs = session.plus(session.plus(session.plus(session.tetra(session.minus(k, one)),
                                                                session.tetra(session.minus(k, two))),
                                                   session.tetra(session.minus(k, three))),
                                      session.tetra(session.minus(k, four)))
            session.assertExpr(session.forall([k], session.implies(session.ge(k, four), session.eq(term, rhs)), [term]))
        }
        session.tetra(kH)
    }

    /**
     * The greatest-common-divisor function {@code gcd(a, b)} (HumanEval 013), asserting Euclid's defining
     * axioms the first time it is seen: base {@code ∀x. gcd(x, 0) == x} and step
     * {@code ∀x,y. y != 0 ⟹ gcd(x, y) == gcd(y, x % y)}. The two-argument sibling of {@link #fibOf}: the step
     * (triggered on {@code gcd(x, y)}) preserves a Euclid loop's invariant {@code Gcd.of(x, y) == Gcd.of(a, b)}
     * across {@code t = x % y; x = y; y = t} by e-matching {@code gcd(x, y) == gcd(y, x % y)}, and at exit
     * ({@code y == 0}) the base axiom collapses {@code gcd(x, 0)} to {@code x}.
     */
    Object gcdOf(Object aH, Object bH) {
        ensureGcdAxioms()
        session.gcd(aH, bH)
    }

    /** Assert Euclid's gcd axioms once (base + step) — shared by {@link #gcdOf} and {@link #lcmOf}. */
    private void ensureGcdAxioms() {
        if (gcdConstrained) return
        gcdConstrained = true
        Object zero = session.intLit(0L)
        // base: ∀x. gcd(x, 0) == x
        Object x = session.boundIntVar('gcd$x' + (quantCounter++))
        Object baseTerm = session.gcd(x, zero)
        session.assertExpr(session.forall([x], session.eq(baseTerm, x), [baseTerm]))
        // step: ∀x,y. y != 0 ⟹ gcd(x, y) == gcd(y, x % y)
        Object sx = session.boundIntVar('gcd$x' + (quantCounter++))
        Object sy = session.boundIntVar('gcd$y' + (quantCounter++))
        Object stepTerm = session.gcd(sx, sy)
        Object rhs = session.gcd(sy, session.intRem(sx, sy))
        session.assertExpr(session.forall([sx, sy],
            session.implies(session.ne(sy, zero), session.eq(stepTerm, rhs)), [stepTerm]))
        // non-zero: ∀x,y. (x != 0 ∨ y != 0) ⟹ gcd(x, y) != 0. A theorem of the recurrence (Euclid never
        // returns 0 unless both args are 0) that finite e-matching can't reach for symbolic args; asserted
        // directly so dividing by a gcd — `a.intdiv(Gcd.of(a, b))`, the lcm idiom — discharges its
        // divisor-non-zero obligation. Sound: it's a true fact about `Gcd.of`.
        Object nx = session.boundIntVar('gcd$x' + (quantCounter++))
        Object ny = session.boundIntVar('gcd$y' + (quantCounter++))
        Object nzTerm = session.gcd(nx, ny)
        session.assertExpr(session.forall([nx, ny],
            session.implies(session.or([session.ne(nx, zero), session.ne(ny, zero)]), session.ne(nzTerm, zero)),
            [nzTerm]))
    }

    /**
     * The least-common-multiple function {@code lcm(a, b)} — the multiplicative sibling of {@link #gcdOf}.
     * Asserts the gcd axioms plus lcm's base ({@code ∀a. lcm(a,0)==0}, {@code ∀b. lcm(0,b)==0}) and the
     * <em>fundamental identity</em> {@code ∀a,b. lcm(a,b) * gcd(a,b) == a * b} (triggered on {@code lcm(a, b)}).
     * So a concrete {@code Lcm.of(4, 6)} unfolds {@code gcd(4,6)==2} via Euclid, then NIA solves
     * {@code lcm * 2 == 24} ⟹ {@code 12}; and the identity {@code Lcm.of(a,b) * Gcd.of(a,b) == a*b} proves
     * symbolically (it <em>is</em> the axiom). The identity is sound for the runtime helper, whose
     * {@code (a / gcd) * b} satisfies it by construction since {@code gcd(a, b)} divides {@code a}.
     */
    Object lcmOf(Object aH, Object bH) {
        ensureGcdAxioms()
        if (!lcmConstrained) {
            lcmConstrained = true
            Object zero = session.intLit(0L)
            // base: ∀a. lcm(a, 0) == 0 ; ∀b. lcm(0, b) == 0
            Object la = session.boundIntVar('lcm$a' + (quantCounter++))
            Object lz = session.lcm(la, zero)
            session.assertExpr(session.forall([la], session.eq(lz, zero), [lz]))
            Object lb = session.boundIntVar('lcm$b' + (quantCounter++))
            Object zl = session.lcm(zero, lb)
            session.assertExpr(session.forall([lb], session.eq(zl, zero), [zl]))
            // identity: ∀a,b. lcm(a, b) * gcd(a, b) == a * b
            Object pa = session.boundIntVar('lcm$a' + (quantCounter++))
            Object pb = session.boundIntVar('lcm$b' + (quantCounter++))
            Object lterm = session.lcm(pa, pb)
            session.assertExpr(session.forall([pa, pb],
                session.eq(session.times(lterm, session.gcd(pa, pb)), session.times(pa, pb)), [lterm]))
        }
        session.lcm(aH, bH)
    }

    /** Whether pow's defining axioms have been asserted (mint-once — {@code pow$} is one global function). */
    private boolean powConstrained = false

    /**
     * The exponentiation function {@code pow(b, k)} backing {@code **}, asserting its defining axioms the
     * first time it is seen: base {@code ∀b. pow(b, 0) == 1}, step {@code ∀b,k. k >= 1 ⟹ pow(b, k) == b *
     * pow(b, k-1)}. The step (triggered on {@code pow(b, k)}) unfolds a literal exponent to a value
     * ({@code 2 ** 3} e-matches down to {@code 2*2*2*1 == 8}) and proves the doubling recurrence
     * {@code 2 ** (n + 1) == 2 * (2 ** n)} by e-matching on {@code pow(2, n+1)} — exactly the {@code << }
     * idiom's essence, expressed in {@code **}. The two-argument sibling of {@link #fibOf}: symbolic-exponent
     * <em>value</em> facts (e.g. {@code 2 ** n >= 1}) need induction the finite e-matching can't reach, so
     * they stay "could not decide" — honest. Negative exponents are left unconstrained (the axioms guard
     * {@code k >= 0}); a fractional {@code b ** -k} isn't an int anyway. For a symbolic base the step's
     * {@code b * pow(...)} is nonlinear (NIA, timeout-gated); for the common literal base it stays linear.
     */
    Object powOf(Object baseH, Object expH) {
        if (!powConstrained) {
            powConstrained = true
            Object zero = session.intLit(0L), one = session.intLit(1L)
            // base: ∀b. pow(b, 0) == 1
            Object b0 = session.boundIntVar('pow$b' + (quantCounter++))
            Object baseTerm = session.pow(b0, zero)
            session.assertExpr(session.forall([b0], session.eq(baseTerm, one), [baseTerm]))
            // step: ∀b,k. k >= 1 ⟹ pow(b, k) == b * pow(b, k-1)
            Object sb = session.boundIntVar('pow$b' + (quantCounter++))
            Object sk = session.boundIntVar('pow$k' + (quantCounter++))
            Object stepTerm = session.pow(sb, sk)
            Object rhs = session.times(sb, session.pow(sb, session.minus(sk, one)))
            session.assertExpr(session.forall([sb, sk],
                session.implies(session.ge(sk, one), session.eq(stepTerm, rhs)), [stepTerm]))
        }
        session.pow(baseH, expH)
    }

    /**
     * For a two-parameter fold closure {@code { a, x -> a OP x }} whose operands are exactly the two
     * parameters (either order), return the operator text when {@code OP} is {@code *} (product) or
     * {@code +} (sum); null otherwise. Recognises {@code inject(init){ a, x -> a * x }} as a product.
     */
    private String foldClosureOp(ClosureExpression clo) {
        Parameter[] ps = clo.parameters
        if (ps == null || ps.length != 2) return null
        Expression body = singleExprOf(clo.code)
        if (!(body instanceof BinaryExpression)) return null
        BinaryExpression be = (BinaryExpression) body
        String op = be.operation.text
        if (op != '*' && op != '+') return null
        if (!(be.leftExpression instanceof VariableExpression) ||
            !(be.rightExpression instanceof VariableExpression)) return null
        Set<String> got = [((VariableExpression) be.leftExpression).name,
                           ((VariableExpression) be.rightExpression).name] as Set
        Set<String> want = [ps[0].name, ps[1].name] as Set
        got == want ? op : null
    }

    /** The bounded universal {@code ∀ i. 0 <= i < k ⟹ i ∈ s}, with {@code (select s i)} as its trigger. */
    private Object domainCoverageForall(Object setHandle, Object kH) {
        Object iv = session.boundIntVar('cov$q' + (quantCounter++))
        Object sel = session.select(setHandle, iv)
        Object mem = session.eq(sel, session.intLit(1L))
        Object range = session.and([session.le(session.intLit(0L), iv), session.lt(iv, kH)])
        session.forall([iv], session.implies(range, mem), [sel])
    }

    /**
     * The set-env key for a receiver that names a set: a plain set-typed variable {@code s}, or the
     * entry snapshot {@code old.s} (keyed {@code old$s}). Null when the receiver is not a known set.
     */
    private String setKeyFor(Expression recv) {
        if (recv instanceof VariableExpression) {
            String n = ((VariableExpression) recv).name
            return setElementTypes.containsKey(n) ? n : null
        }
        if (recv instanceof PropertyExpression && isOldReceiver(((PropertyExpression) recv).objectExpression)) {
            String n = ((PropertyExpression) recv).propertyAsString
            return setElementTypes.containsKey(n) ? ('old$' + n) : null
        }
        null
    }

    // ---- Maps: a value array (contents) + a key-set (a characteristic array), keyed by a logical
    // name ({@code m} or {@code old$m}). The key-set reuses the set machinery, so map size and the
    // cardinality law come straight from {@link #cardOf}/{@link #member}.
    private static String mapValsKey(String logical) { 'map$vals$' + logical }
    private static String mapKeysKey(String logical) { 'map$keys$' + logical }

    /** The value-array handle ({@code m[k]} reads) for a map's logical name. */
    Object mapValsFor(String logical) { arrayFor(mapValsKey(logical)) }
    /** The key-set handle ({@code containsKey}/{@code size}) for a map's logical name. */
    Object mapKeysFor(String logical) { setFor(mapKeysKey(logical)) }
    /** Re-bind a map's value array — threads {@code m[k] = v} / {@code m.put(k,v)} on the value side. */
    void putMapVals(String logical, Object handle) { bindArray(mapValsKey(logical), handle) }
    /** Re-bind a map's key-set — threads the key added by a put (with the cardinality law). */
    void putMapKeys(String logical, Object handle) { bindSet(mapKeysKey(logical), handle) }
    /** Current value-array / key-set bindings, or null — for save/restore around a call's framing. */
    Object peekMapVals(String logical) { peekArray(mapValsKey(logical)) }
    Object peekMapKeys(String logical) { peekSet(mapKeysKey(logical)) }

    /** The logical map name for a receiver that names a map ({@code m} or the snapshot {@code old.m}); null otherwise. */
    String mapLogicalFor(Expression recv) {
        if (recv instanceof VariableExpression) {
            String n = ((VariableExpression) recv).name
            return mapTypes.containsKey(n) ? n : null
        }
        if (recv instanceof PropertyExpression && isOldReceiver(((PropertyExpression) recv).objectExpression)) {
            String n = ((PropertyExpression) recv).propertyAsString
            return mapTypes.containsKey(n) ? ('old$' + n) : null
        }
        null
    }

    /** The nullity oracle: a boolean that is true exactly when {@code recv} is null. */
    Object nullityOf(String recv) {
        Object cached = nullEnv.get(recv)
        if (cached != null) return cached
        Object v = session.boolVar(recv + '?null')
        nullEnv.put(recv, v)
        v
    }

    /** Phase 131 — bind {@code name}'s nullity flag to {@code handle} (a Bool: true ⇒ null), so a later
     *  {@code name == null}/{@code name != null} reads it. The value-flow analogue of {@link #bind} for nullity. */
    void bindNullity(String name, Object handle) { if (handle != null) nullEnv.put(name, handle) }

    /**
     * Phase 131 — the nullity flag implied by the *value* of {@code e}, or null when its nullity is unknown
     * (the caller then leaves the oracle free, the pre-Phase-131 behaviour). This is what lets a method *prove*
     * it returns/holds a non-null value — `null`/non-null literals, a freshly constructed object, a collection or
     * GString literal, and string concatenation all have statically-known nullity; a bare variable ties to its
     * own oracle (so a `@Requires`-known-non-null param flows through `return x`).
     */
    Object nullityOfExpr(Expression e) {
        if (e == null) return null
        if (e instanceof ConstantExpression) return session.boolLit(((ConstantExpression) e).value == null)
        if (e instanceof VariableExpression) {
            String n = ((VariableExpression) e).name
            if (n == 'null') return session.boolLit(true)
            return nullityOf(n)
        }
        if (e instanceof ConstructorCallExpression || e instanceof ListExpression ||
            e instanceof MapExpression || e instanceof GStringExpression) return session.boolLit(false)
        if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.PLUS &&
            isStringReceiver(e)) return session.boolLit(false)   // String concatenation is never null
        null
    }

    /**
     * Phase 37 — get-or-mint the per-element nullity array for a list/array container. The handle
     * is an {@code Array<Int, Int>} where {@code select(arr, i) == 1} means element {@code i} is
     * null, {@code 0} means non-null. The shape matches the existing set machinery (also 1/0 over
     * an Int-Int characteristic array), so Z3's array theory carries through cleanly: a contract
     * {@code @Requires({ xs[i] != null })} adds a path fact that {@code select(xs$nullElem, i) == 0},
     * which discharges the implicit per-element NPE obligation at a later {@code xs[i].method()}.
     */
    Object elementNullityFor(String name) { arrayFor(name + '$nullElem') }

    /**
     * Translate a Groovy expression to an SMT handle. Returns null
     * if anything in the subtree is outside the fragment.
     */
    /** The released value of an explicit declassification {@code Declassify.to('Level', value)} → {@code value};
     *  otherwise null. Value-level identity (§III-E only releases the label, never alters the value). */
    private static Expression declassifyValue(Expression e) {
        String m = null
        Expression recv = null, args = null
        if (e instanceof MethodCallExpression) {
            m = ((MethodCallExpression) e).methodAsString; recv = ((MethodCallExpression) e).objectExpression
            args = ((MethodCallExpression) e).arguments
        } else if (e instanceof StaticMethodCallExpression) {
            m = ((StaticMethodCallExpression) e).method; recv = null
            args = ((StaticMethodCallExpression) e).arguments
            if (((StaticMethodCallExpression) e).ownerType?.nameWithoutPackage != 'Declassify') return null
        } else {
            return null
        }
        if (m != 'to') return null
        if (e instanceof MethodCallExpression) {
            String rn = (recv instanceof VariableExpression) ? ((VariableExpression) recv).name :
                        (recv instanceof ClassExpression) ? recv.type?.nameWithoutPackage : null
            if (rn != 'Declassify') return null
        }
        if (args instanceof ArgumentListExpression) {
            List<Expression> as = ((ArgumentListExpression) args).expressions
            if (as.size() == 2) return as.get(1)
        }
        null
    }

    Object translate(Expression expr) {
        if (expr == null) return null

        // §III-E declassification is a value-level identity: `Declassify.to('Low', e)` carries the value of `e`
        // unchanged (only its security label is released). Unwrap so the value-flow fragment sees through it.
        Expression declassified = declassifyValue(expr)
        if (declassified != null) return translate(declassified)

        if (expr instanceof ConstantExpression) {
            Object v = ((ConstantExpression) expr).value
            if (v instanceof Integer || v instanceof Long || v instanceof Short || v instanceof Byte) {
                return session.intLit(((Number) v).longValue())
            }
            // BigInteger is Z3's unbounded Int sort exactly (Groovy's arbitrary-precision integer), so a literal
            // folds straight to an Int constant — within long range. A wider literal is left to skip loudly; the
            // unbounded *arithmetic* on BigInteger values is modelled regardless (they default to the Int sort).
            if (v instanceof BigInteger) {
                BigInteger bi = (BigInteger) v
                return bi.bitLength() < 63 ? session.intLit(bi.longValue()) : null
            }
            if (v instanceof Boolean) {
                return session.boolLit((Boolean) v)
            }
            if (v instanceof String) {
                // Phase 27 — a bare String literal in expression position translates to a
                // constant of the default String!Sort. Cross-comparisons like
                // {@code m["k"] == "v"} (where m is Map<String,String>) and
                // {@code xs[i] == "abc"} (where xs is List<String>) then connect through this
                // same sort. Interning by the literal text means two references to "v" in the
                // same session resolve to the same Z3 constant; the lazy pairwise-distinct
                // cascade keeps distinct literals distinct.
                return session.litOfSort(session.declareSort('String'), (String) v)
            }
            return null  // floats, null — outside fragment (null handled at comparison level)
        }

        if (expr instanceof VariableExpression) {
            String name = ((VariableExpression) expr).name
            // Boolean literal as variable name shouldn't really happen at this
            // point post-parse, but defensive:
            if (name == "true")  return session.boolLit(true)
            if (name == "false") return session.boolLit(false)
            if (fpNames.containsKey(name)) return session.fpVar(name, fpNames.get(name))   // Phase 73 — IEEE-754
            return varFor(name)
        }

        if (expr instanceof UnaryMinusExpression) {
            if (isDecimalExpr(expr)) return asReal(expr)   // Phase 67 — decimal negation in the Real sort
            Object inner = translate(((UnaryMinusExpression) expr).expression)
            return inner == null ? null : session.neg(inner)
        }

        if (expr instanceof UnaryPlusExpression) {
            return translate(((UnaryPlusExpression) expr).expression)
        }

        if (expr instanceof BitwiseNegationExpression) {
            // `~x` is the two's-complement complement = -x - 1, an exact Int identity (no bit-vector needed, and
            // not refute-hostile). (`~"regex"` is `Pattern.compile`, not bitwise — its non-Int operand makes the
            // arithmetic throw, so it skips loudly rather than mis-modelling.)
            Object inner = translate(((BitwiseNegationExpression) expr).expression)
            if (inner == null) return null
            try { return session.minus(session.neg(inner), session.intLit(1L)) }
            catch (Exception ignored) { return null }
        }

        if (expr instanceof NotExpression) {
            Expression ie = ((NotExpression) expr).expression
            Object inner = truthy(ie, translate(ie))   // the negated operand may be non-Boolean (Groovy truth)
            return inner == null ? null : session.not(inner)
        }

        if (expr instanceof BooleanExpression) {
            // Groovy wraps if/while conditions in BooleanExpression
            return translate(((BooleanExpression) expr).expression)
        }

        // Phase 46e — {@code (int) "hello".charAt(0)} bridges Groovy's char-vs-int distinction
        // at the return path: charAt returns char, the method may return int, so the user adds
        // a numeric cast. The verifier treats the cast as transparent — the inner term's sort
        // is already Int — and translates through.
        if (expr instanceof CastExpression) {
            CastExpression ce = (CastExpression) expr
            // {@code (int)(a / b)} (and {@code (a / b) as int}) is Groovy's other truncate-toward-zero
            // integer-division idiom: BigDecimal division then narrow-to-int. Model it as the same
            // truncating division as {@code a.intdiv(b)}, rather than skipping the inner `/`.
            if (isIntegralCastType(ce.type) && ce.expression instanceof BinaryExpression) {
                BinaryExpression inner = (BinaryExpression) ce.expression
                if (inner.operation.text == '/' || inner.operation.text == '\\') {
                    Object a = translate(inner.leftExpression)
                    Object b = translate(inner.rightExpression)
                    return (a == null || b == null) ? null : truncDiv(a, b)
                }
            }
            // Phase 105 — Groovy has no primitive char literal, so `('a' as char)` / `(char)'a'` (and the
            // numeric `(int)'a'`) is the idiomatic way to write a code point. Fold a char/integral cast of a
            // single-char String (or Character) literal to its int code, so `s.charAt(i) >= ('a' as char)`
            // compares code points rather than mixing an int term with the Seq term `'a'` translates to.
            if (isCharCastType(ce.type) || isIntegralCastType(ce.type)) {
                Integer code = singleCharCode(ce.expression)
                if (code != null) return session.intLit((long) code.intValue())
            }
            return translate(ce.expression)
        }

        // Phase 47h — GString interpolation. {@code "hello $name"} parses as a
        // {@link GStringExpression} with parallel lists of static strings and interpolated
        // values; translate to chained {@code stringConcat} via Z3's seq theory. Each value
        // is converted to its String representation via {@link #translateValueAsString} —
        // String values flow directly, integers go through {@code intToString}, others skip.
        if (expr instanceof GStringExpression) {
            return translateGString((GStringExpression) expr)
        }

        // Phase 98 — Elvis `a ?: b` is `groovyTruth(a) ? a : b`. Its condition is *Groovy truth on the first
        // operand* (re-used as the then-branch), NOT a boolean — so it must be handled before the general
        // TernaryExpression case below, which would feed `a` straight in as the `ite` condition and crash
        // (an Int term cast to Bool). {@link #groovyTruth} models the truth per operand type; an unmodelled
        // type returns null → a loud "outside fragment" skip, never a crash.
        if (expr instanceof ElvisOperatorExpression) {
            ElvisOperatorExpression el = (ElvisOperatorExpression) expr
            Expression operand = el.trueExpression        // the `a` in `a ?: b`
            Object aTerm = translate(operand)
            Object bTerm = translate(el.falseExpression)
            if (aTerm == null || bTerm == null) return null
            Object cond = groovyTruth(operand, aTerm)
            if (cond == null) return null
            return session.ite(cond, aTerm, bTerm)
        }

        if (expr instanceof TernaryExpression) {
            // cond ? a : b  ->  (ite cond a b). Also the shape an unfolded pure
            // function takes (e.g. pow2's `n == 0 ? 1 : ...`), see translateCall.
            TernaryExpression te = (TernaryExpression) expr
            Object c = translate(te.booleanExpression)
            Object t = translate(te.trueExpression)
            Object f = translate(te.falseExpression)
            if (c == null || t == null || f == null) return null
            return session.ite(c, t, f)
        }

        // Phase B — `new Res(a)` on a recognised wrapper carrier: the datatype constructor (unit/of). The
        // contract-side type is unresolved (re-parsed), so the resolved carrier is recovered by simple name.
        if (expr instanceof ConstructorCallExpression) {
            ConstructorCallExpression cce = (ConstructorCallExpression) expr
            ClassNode carrier = cce.type != null ? carrierByName(cce.type.nameWithoutPackage) : null
            if (carrier != null) {
                FieldNode cf = wrapperContentField(carrier)
                List<Expression> cargs = (cce.arguments instanceof ArgumentListExpression) ?
                    ((ArgumentListExpression) cce.arguments).expressions : Collections.<Expression>emptyList()
                if (cf != null && cargs.size() == 1) {
                    Object cSort = contentSortFor(cf)
                    Object val = translateInSort(cargs.get(0), cSort)
                    if (val != null) return session.wrapperUnit(carrier.nameWithoutPackage, cSort, val)
                }
                List<FieldNode> rc = recordComponents(carrier)   // Phase 142 — `new R(a, b, …)` → N-field datatype ctor
                if (rc != null && cargs.size() == rc.size()) {
                    sortFor(carrier)                              // ensure the datatype is declared
                    List<Object> vals = new ArrayList<Object>()
                    for (int i = 0; i < rc.size(); i++) {
                        Object v = translateInSort(cargs.get(i), sortFor(rc.get(i).type))
                        if (v == null) { vals = null; break }
                        vals.add(v)
                    }
                    if (vals != null) return session.datatypeConstruct(carrier.nameWithoutPackage, carrier.nameWithoutPackage, vals)
                }
            }
        }

        if (expr instanceof PropertyExpression) {
            PropertyExpression pe = (PropertyExpression) expr
            String prop = pe.propertyAsString
            Expression obj = pe.objectExpression
            // Phase B/M-C — `<carrier>.content`: the datatype selector. The receiver may be a carrier-typed
            // variable, a freshly-constructed carrier (`new Res(x).v`), or a factory call (`some(x).value`).
            ClassNode mt = carrierTypeOf(obj)
            if (mt != null) {
                FieldNode cf = wrapperContentField(mt)
                if (cf != null && cf.name == prop) {
                    Object carrier = translate(obj)
                    if (carrier != null) return session.wrapperContent(mt.nameWithoutPackage, contentSortFor(cf), carrier)
                }
                Object[] mc = multiCaseInfo(mt)
                if (mc != null && ((FieldNode) mc[2]).name == prop) {
                    sortFor(mt)
                    Object carrier = translate(obj)
                    if (carrier != null) return session.datatypeSelect(mt.nameWithoutPackage, 'Some', prop, carrier)
                }
                List<FieldNode> rc = recordComponents(mt)   // Phase 142 — `r.field` → N-field datatype selector
                if (rc != null && rc.any { it.name == prop }) {
                    sortFor(mt)
                    Object carrier = translate(obj)
                    if (carrier != null) return session.datatypeSelect(mt.nameWithoutPackage, mt.nameWithoutPackage, prop, carrier)
                }
            }
            // Phase 148 (experimental DSL) — `X.value` (the property form of getValue()) on a JSR 385 quantity:
            // its SI magnitude read in X's current unit. After the carrier branches, so a bespoke record's own
            // `.value` field still wins. Gated on a Quantity-typed receiver.
            if (prop == 'value' && isQuantityTyped(obj)) {
                Object v = quantityValueTerm(obj)
                if (v != null) return v
            }
            // Phase 44 polish — JDK boxed-numeric range constants fold to their literal values, so a
            // user can write {@code @Requires({ n < Integer.MAX_VALUE })} (or the {@code Long}
            // equivalents) and the verifier sees the same literal a tighter explicit bound would
            // give. Matched by simple-name on the receiver and property string; Long values exceed
            // 32-bit range but our int model is mathematical so a 64-bit literal is fine to assert.
            Object jdkConst = tryFoldJdkRangeConstant(obj, prop)
            if (jdkConst != null) return jdkConst
            // old.field -> the field's *entry* snapshot variable (groovy-contracts' `old` map). The
            // snapshot is pinned to the entry value before the body's writes (see VerifyChecker).
            if (isOldReceiver(obj)) {
                return varFor('old$' + prop)
            }
            // this.field -> the field's state variable (instance-field support). The bare-name form
            // `field` is already a VariableExpression -> varFor(field), so both spellings unify.
            if (isThisReceiver(obj)) {
                return varFor(prop)
            }
            // Phase 45 — b.field for a class-typed parameter b: resolves to {@code b$field}, a
            // receiver-qualified SMT entity distinct from any same-named field on the declaring
            // class. The field must exist on b's declared type; otherwise fall through (avoids
            // misinterpreting a property name as a field).
            if (obj instanceof VariableExpression) {
                String recvName = ((VariableExpression) obj).name
                if (objectParams.containsKey(recvName)) {
                    Set<String> fields = fieldsOfObjectParam(recvName)
                    if (fields.contains(prop)) {
                        // Phase 89 — an alias-modelled receiver reads its Int field through the
                        // identity-keyed heap map, so `a.f` / `b.f` coincide iff `id(a) == id(b)`.
                        ClassNode ft = fieldTypeOfObjectParam(recvName, prop)
                        if (isAliasModeled(recvName) && ft != null && isIntLikeType(ft)) {
                            return session.select(fieldMap(objectParams.get(recvName).name, prop), objId(recvName))
                        }
                        return varForRaw(recvName + '$' + prop)
                    }
                }
            }
            // Native idiom: `a.sorted` — the boolean-getter property form of `a.isSorted()` (Groovy 6
            // GDK on List/object-arrays and the native int[]/long[] overloads). Ascending with ties,
            // the same axiom as `Sorted.ascending(a)`. Only fires for a recognised array/list receiver
            // (translateSorted returns null otherwise), so a genuine field/property named `sorted` is
            // unaffected; placed after the field/object-param handling so those keep precedence.
            if (prop == 'sorted' && obj instanceof VariableExpression) {
                Object q = translateSorted('ascending', obj)
                if (q != null) return q
            }
            // Phase 79 — a tuple/list factory's named slot accessor (property form): t.v1 / t.vN /
            // t.first / t.second fold to the k-th constructed element. Covers `result.v1` on a returned
            // tuple (result is recorded as a factory by Phase 78) and `Tuple.tuple(a, b).first`.
            int slot = tupleSlotIndex(prop)
            if (slot >= 0) {
                FactoryContainer tf = factoryContainerFor(obj)
                if (tf != null && tf.kind == 'list' && tf.args != null && slot < tf.args.size()) {
                    Object h = translate(tf.args.get(slot))
                    if (h != null) return h   // leaf scalar; a nested-tuple slot is null here, resolved via the chain
                }
                // Phase 80/82 — slot of a (possibly nested) tuple *parameter* → typed entity t$vN / t$v1$v2.
                Object te = tupleParamSlot(obj, slot)
                if (te != null) return te
            }
            // Phase 83 — Groovy map-as-named-tuple: `m.key` (property form) on a map factory folds to the
            // value at that key — only when `prop` actually names an entry, so `m.size` etc. still reach
            // their own handling below. Covers `result.sum` on a returned `[sum: s, product: p]`.
            Object mapVal = foldMapPropertyByName(factoryContainerFor(obj), prop)
            if (mapVal != null) return mapVal
            // Phase 80 — t.size on a tuple parameter folds to its arity (a literal).
            if (prop == 'size' && obj instanceof VariableExpression) {
                int ar = tupleArity(tupleParams.get(((VariableExpression) obj).name))
                if (ar >= 0) return session.intLit((long) ar)
            }
            // s.size / m.size (property form) on a known set/map -> cardinality, ahead of the size oracle.
            if (prop == 'size') {
                String setKey = setKeyFor(obj)
                if (setKey != null) return cardOf(setFor(setKey))
                String mapLog = mapLogicalFor(obj)
                if (mapLog != null) return cardOf(mapKeysFor(mapLog))
            }
            // xs.length / xs.size  ->  size oracle
            if ((prop == 'length' || prop == 'size') && obj instanceof VariableExpression) {
                return sizeOf(((VariableExpression) obj).name)
            }
            // Phase 84 — `m.key` on a map *parameter* (after .size etc.): the value at key `prop`,
            // routed to the map's value array — `m.sum` ≡ `m['sum']`. The dual of Phase 83's map factories.
            Object mapParamVal = foldMapParamProperty(obj, prop)
            if (mapParamVal != null) return mapParamVal
            // Phase 28 — `Color.values().length` folds to the literal enum-constant count, so a
            // contract like `Sets.boundedBy(s, Color.values().length)` or a body returning the count
            // becomes ground.
            if (prop == 'length') {
                Integer cnt = enumValuesCountFor(obj)
                if (cnt != null) return session.intLit(cnt.longValue())
            }
            // Phase 27 — enum literal in a non-expected-sort position (e.g. the RHS of
            // `xs[k] == Color.RED` where the encoder doesn't push down an expected sort). Two
            // shapes: PropertyExpression(ClassExpression(Color), RED) when the type has been
            // resolved (typed method body), and PropertyExpression(VariableExpression(Color), RED)
            // when the contract closure has been re-parsed from text. Both mint a literal of the
            // enum's sort, keyed by the property name — the same key shape translateInSort uses,
            // so a body's `xs[k] = Color.RED` and a contract's `xs[k] == Color.RED` agree.
            if (obj instanceof ClassExpression) {
                ClassNode t = ((ClassExpression) obj).type
                if (t != null && (t.isEnum() || isEnumLikeType(t))) {
                    return session.litOfSort(session.declareSort(enumSortName(t)), prop)
                }
            }
            if (obj instanceof VariableExpression) {
                String recvName = ((VariableExpression) obj).name
                if (isKnownEnumName(recvName)) {
                    return session.litOfSort(session.declareSort(recvName), prop)
                }
            }
            return null
        }

        if (expr instanceof MethodCallExpression) {
            Object aw = tryTranslateAwait(expr)             // Phase 153 — await x → the safe async body's value
            if (aw != null) return aw
            Object r = translateMethodCall((MethodCallExpression) expr)
            return r != null ? r : translateCall(expr)
        }

        // Phase 8a — a resolved static call (e.g. `C.pow2(n)`) only reaches the verifier
        // already in this form; try the pure-function paths (closed eval / unfolding).
        if (expr instanceof StaticMethodCallExpression) {
            Object aw = tryTranslateAwait(expr)             // Phase 153 — STC-resolved AsyncSupport.await(x)
            if (aw != null) return aw
            return translateCall(expr)
        }

        if (expr instanceof BinaryExpression) {
            return translateBinary((BinaryExpression) expr)
        }

        // Anything else: outside fragment.
        return null
    }

    /**
     * Attempt to reduce a closed (constant) expression to an SMT literal via Groovy's own
     * constant folder ({@link ExpressionUtils#transformInlineConstants}), so the integer
     * arithmetic matches Groovy's semantics. Returns null if it doesn't fold to an integral
     * or boolean constant (the same value shapes {@link #translate} accepts as literals).
     */
    /**
     * Phase 44 polish — recognise the JDK boxed-numeric range constants
     * ({@code Integer.MAX_VALUE}/{@code MIN_VALUE}, {@code Long.MAX_VALUE}/{@code MIN_VALUE},
     * {@code Short}/{@code Byte}/{@code Character} variants) and fold each to its literal value.
     * Returns null when the property doesn't match — the caller falls through to the existing
     * PropertyExpression dispatch. The receiver match is by simple class-name on a
     * {@link ClassExpression} so the contract can be written {@code Integer.MAX_VALUE}
     * unqualified (the imported boxed-name) or fully qualified.
     */
    private Object tryFoldJdkRangeConstant(Expression obj, String prop) {
        if (obj == null || prop == null) return null
        String typeName = null
        if (obj instanceof ClassExpression) {
            typeName = ((ClassExpression) obj).type?.nameWithoutPackage
        } else if (obj instanceof VariableExpression) {
            // {@code Integer.MAX_VALUE} sometimes parses as VariableExpression('Integer') before
            // type resolution; accept the bare class-name spelling too.
            typeName = ((VariableExpression) obj).name
        }
        if (typeName == null) return null
        if (typeName == 'Integer') {
            if (prop == 'MAX_VALUE') return session.intLit(2147483647L)
            if (prop == 'MIN_VALUE') return session.intLit(-2147483648L)
        } else if (typeName == 'Long') {
            if (prop == 'MAX_VALUE') return session.intLit(Long.MAX_VALUE)
            if (prop == 'MIN_VALUE') return session.intLit(Long.MIN_VALUE)
        } else if (typeName == 'Short') {
            if (prop == 'MAX_VALUE') return session.intLit(32767L)
            if (prop == 'MIN_VALUE') return session.intLit(-32768L)
        } else if (typeName == 'Byte') {
            if (prop == 'MAX_VALUE') return session.intLit(127L)
            if (prop == 'MIN_VALUE') return session.intLit(-128L)
        } else if (typeName == 'Character') {
            if (prop == 'MAX_VALUE') return session.intLit(65535L)
            if (prop == 'MIN_VALUE') return session.intLit(0L)
        }
        null
    }

    private Object tryFoldConstant(Expression e) {
        Expression folded = ExpressionUtils.transformInlineConstants(e, ClassHelper.int_TYPE)
        if (folded instanceof ConstantExpression) {
            Object v = ((ConstantExpression) folded).value
            if (v instanceof Integer || v instanceof Long || v instanceof Short || v instanceof Byte) {
                return session.intLit(((Number) v).longValue())
            }
            if (v instanceof Boolean) {
                return session.boolLit((Boolean) v)
            }
        }
        return null
    }

    /** Phase 61 — cache of minted Real constants for decimal-typed names (one per source name). */
    private final Map<String, Object> realVars = new HashMap<String, Object>()

    private Object realVarFor(String name) {
        Object v = realVars.get(name)
        if (v == null) { v = session.realVar(name); realVars.put(name, v) }
        v
    }

    /** Phase 61 — true if {@code name} is a decimal-typed (BigDecimal/Double/Float) name. */
    boolean isDecimalName(String name) { decimalNames.contains(name) }

    /** Phase 61 — true if {@code e} produces a decimal value (a `/`, a decimal literal/name, or
     *  decimal arithmetic). Exposed so binding sites can refuse to put a Real handle into an
     *  Int-typed slot (which would crash Z3 on a sort mismatch) and skip loudly instead. */
    boolean isDecimalValued(Expression e) { isDecimalExpr(e) }

    /** Phase 67 — translate {@code e} into the Real sort (for a decimal-valued binding); null = skip. */
    Object asRealValue(Expression e) { asReal(e) }

    // ── Phase 73 — IEEE-754 floating point (double/float via Z3's FP theory) ──────────────────────
    /** True if {@code e} produces a {@code double}/{@code float} value (an FP name, literal, or +,-,*,/). */
    boolean isFpValued(Expression e) {
        if (e instanceof ConstantExpression) {
            Object v = ((ConstantExpression) e).value
            return v instanceof Double || v instanceof Float
        }
        if (e instanceof VariableExpression) return fpNames.containsKey(((VariableExpression) e).name)
        if (e instanceof UnaryMinusExpression) return isFpValued(((UnaryMinusExpression) e).expression)
        if (e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e
            // Phase 77 — an FP-element list/array read `xs[i]` is FP-valued (the select inherits the
            // array's element sort), so a comparison/arithmetic on it routes to the FP theory.
            if (be.operation.type == Types.LEFT_SQUARE_BRACKET && be.leftExpression instanceof VariableExpression) {
                return isFpElementType(listElementTypes.get(((VariableExpression) be.leftExpression).name))
            }
            String t = be.operation.text
            if (t == '+' || t == '-' || t == '*' || t == '/') {
                return isFpValued(be.leftExpression) || isFpValued(be.rightExpression)
            }
        }
        // Phase 77 — `xs.max()` / `xs.min()` over an FP-element list is FP-valued (the witnessed extremum r).
        if (e instanceof MethodCallExpression) {
            MethodCallExpression mc = (MethodCallExpression) e
            String m = mc.methodAsString
            if ((m == 'max' || m == 'min') && argList(mc).isEmpty() &&
                mc.objectExpression instanceof VariableExpression) {
                return isFpElementType(listElementTypes.get(((VariableExpression) mc.objectExpression).name))
            }
        }
        if (isFpMathCall(e) != null) return true   // Math.sqrt(fp) / Math.abs(fp)
        false
    }

    /** {@code Math.sqrt}/{@code Math.abs} over an FP argument → ['sqrt'|'abs', argExpr]; null otherwise. */
    private Object[] isFpMathCall(Expression e) {
        if (!(e instanceof MethodCallExpression)) return null
        MethodCallExpression mce = (MethodCallExpression) e
        String mm = mce.methodAsString
        if ((mm != 'sqrt' && mm != 'abs') || !isMathReceiver(mce.objectExpression)) return null
        List<Expression> a = argList(mce)
        if (a.size() != 1 || !isFpValued(a.get(0))) return null
        [mm, a.get(0)] as Object[]
    }

    /** Precision of an FP expression — {@code true} = double/Float64, from its first FP leaf; null if none. */
    private Boolean fpDoubleOf(Expression e) {
        Object[] math = isFpMathCall(e)
        if (math != null) return math[0] == 'sqrt' ? Boolean.TRUE : fpDoubleOf((Expression) math[1])
        if (e instanceof ConstantExpression) {
            Object v = ((ConstantExpression) e).value
            if (v instanceof Double) return Boolean.TRUE
            if (v instanceof Float) return Boolean.FALSE
            return null
        }
        if (e instanceof VariableExpression) return fpNames.get(((VariableExpression) e).name)
        if (e instanceof UnaryMinusExpression) return fpDoubleOf(((UnaryMinusExpression) e).expression)
        if (e instanceof BinaryExpression) {
            Boolean l = fpDoubleOf(((BinaryExpression) e).leftExpression)
            return l != null ? l : fpDoubleOf(((BinaryExpression) e).rightExpression)
        }
        null
    }

    /** Translate {@code e} into the FP sort. Pure FP only (FP names/literals + `+ - * /`, unary minus);
     *  an int operand or anything else returns null → loud skip (no silent int↔fp coercion). */
    Object asFp(Expression e) {
        if (e instanceof ConstantExpression) {
            Object v = ((ConstantExpression) e).value
            if (v instanceof Double) return session.fpLit(((Double) v).doubleValue(), true)
            if (v instanceof Float)  return session.fpLit(((Float) v).doubleValue(), false)
            return null
        }
        if (e instanceof VariableExpression && fpNames.containsKey(((VariableExpression) e).name)) {
            String n = ((VariableExpression) e).name
            Object bound = env.get(n)            // e.g. result bound to its FP return handle
            return bound != null ? bound : session.fpVar(n, fpNames.get(n))
        }
        if (e instanceof UnaryMinusExpression) {
            Object o = asFp(((UnaryMinusExpression) e).expression)
            return o == null ? null : session.fpNeg(o)
        }
        if (e instanceof BinaryExpression) {
            String t = ((BinaryExpression) e).operation.text
            if (t == '+' || t == '-' || t == '*' || t == '/') {
                Object L = asFp(((BinaryExpression) e).leftExpression)
                Object R = asFp(((BinaryExpression) e).rightExpression)
                if (L == null || R == null) return null
                if (t == '+') return session.fpAdd(L, R)
                if (t == '-') return session.fpSub(L, R)
                if (t == '*') return session.fpMul(L, R)
                return session.fpDiv(L, R)
            }
        }
        Object[] math = isFpMathCall(e)
        if (math != null) {
            // Math.sqrt always returns double; a float arg widens in Java, which fp.sqrt over Float32
            // wouldn't model — so only model double-precision sqrt. abs preserves precision (sound for both).
            if (math[0] == 'sqrt' && fpDoubleOf((Expression) math[1]) != Boolean.TRUE) return null
            Object x = asFp((Expression) math[1])
            if (x == null) return null
            return math[0] == 'sqrt' ? session.fpSqrt(x) : session.fpAbs(x)
        }
        // Phase 77 — fallback for any expression that already translates to an FP-sorted term: an
        // FP-element array read `xs[i]` (the select inherits the element sort), a quantifier element
        // bound to such a select, or `xs.max()`/`xs.min()` over an FP list. Accept it iff it's FP-sorted.
        Object h = translate(e)
        return (h != null && session.isFp(h)) ? h : null
    }

    /** True if {@code recv} is the {@code Math} class (for {@code Math.sqrt(x)} / {@code Math.abs(x)}). */
    private static boolean isMathReceiver(Expression recv) {
        String n = null
        if (recv instanceof VariableExpression) n = ((VariableExpression) recv).name
        else if (recv instanceof PropertyExpression) n = ((PropertyExpression) recv).propertyAsString
        else if (recv instanceof ClassExpression) n = ((ClassExpression) recv).type?.nameWithoutPackage
        n == 'Math'
    }

    /** True if {@code recv} is the {@code Double}/{@code Float} class (for {@code Double.isNaN(x)} etc.). */
    private static boolean isFpClassReceiver(Expression recv) {
        String n = null
        if (recv instanceof VariableExpression) n = ((VariableExpression) recv).name
        else if (recv instanceof PropertyExpression) n = ((PropertyExpression) recv).propertyAsString
        else if (recv instanceof ClassExpression) n = ((ClassExpression) recv).type?.nameWithoutPackage
        n == 'Double' || n == 'Float'
    }

    /** True if {@code e} denotes a decimal (BigDecimal/Double/Float) value in Groovy's semantics. */
    /**
     * Phase 143 — true if dividing ANY finite-decimal value by {@code e} terminates *exactly* in Groovy (so
     * `BigDecimal /` returns the exact quotient rather than rounding) — i.e. {@code e} is a non-zero literal whose
     * unscaled integer has only the prime factors 2 and 5 (a power of ten, or any product of 2s and 5s: `/1000`,
     * `/8`, `/0.25`, …). Division by such a constant is sound to model as exact Real division; any other divisor
     * (a 3, a 7, a symbolic value) makes Groovy round to its `MathContext`, so the Real model would be unsound
     * and the division must skip.
     */
    static boolean isTerminatingDivisor(Expression e) {
        Expression c = (e instanceof UnaryMinusExpression) ? ((UnaryMinusExpression) e).expression : e
        if (!(c instanceof ConstantExpression)) return false
        Object v = ((ConstantExpression) c).value
        if (!(v instanceof Number) || v instanceof Double || v instanceof Float) return false
        BigDecimal bd
        try { bd = new BigDecimal(v.toString()) } catch (Exception ignored) { return false }
        if (bd.signum() == 0) return false
        BigInteger u = bd.unscaledValue().abs()
        BigInteger two = BigInteger.valueOf(2), five = BigInteger.valueOf(5)
        while (u.mod(two).signum() == 0) u = u.divide(two)
        while (u.mod(five).signum() == 0) u = u.divide(five)
        u.equals(BigInteger.ONE)
    }

    private boolean isDecimalExpr(Expression e) {
        if (e instanceof ConstantExpression) {
            return ((ConstantExpression) e).value instanceof BigDecimal   // not Double/Float (IEEE-754)
        }
        if (e instanceof VariableExpression) {
            return decimalNames.contains(((VariableExpression) e).name)
        }
        if (e instanceof UnaryMinusExpression) return isDecimalExpr(((UnaryMinusExpression) e).expression)
        if (e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e
            String t = be.operation.text
            // Phase 152 — a JSR 385 `quantity * / + - quantity` is NOT a BigDecimal scalar: it dispatches to
            // Quantity.multiply/divide/add/subtract, and is modelled by the dimension/magnitude reader, not the Real
            // path. Without this guard a `1.m / 1.s` return is mis-flagged "BigDecimal but return type is not decimal".
            if (isQuantityExpr(be)) return false
            if (t == '/') {
                // Groovy `/` on int/BigDecimal operands is BigDecimal (Real) division. But `double`/`float`
                // operands make it IEEE-754 FP division — defer to the FP branch, not the Real path.
                return !(isFpValued(be.leftExpression) || isFpValued(be.rightExpression))
            }
            if (t == '+' || t == '-' || t == '*') {
                return isDecimalExpr(be.leftExpression) || isDecimalExpr(be.rightExpression)
            }
        }
        false
    }

    /** Translate {@code e} into the Real sort, coercing Int subexpressions via int→real. Null = skip. */
    private Object asReal(Expression e) {
        if (e instanceof ConstantExpression) {
            Object v = ((ConstantExpression) e).value
            if (v instanceof BigDecimal) return session.realLit(rationalOf(v))
            if (v instanceof Integer || v instanceof Long || v instanceof Short || v instanceof Byte) {
                return session.intToReal(session.intLit(((Number) v).longValue()))
            }
            return null   // Double/Float etc. are IEEE-754, not exact Real — skip
        }
        if (e instanceof VariableExpression && decimalNames.contains(((VariableExpression) e).name)) {
            // A threaded binding (e.g. `result` bound to its Real return handle, or a decimal local
            // assigned in the body) is already Real — reuse it; otherwise mint the param's constant.
            String n = ((VariableExpression) e).name
            Object bound = env.get(n)
            return bound != null ? bound : realVarFor(n)
        }
        if (e instanceof UnaryMinusExpression) {
            Object o = asReal(((UnaryMinusExpression) e).expression)
            return o == null ? null : session.neg(o)
        }
        if (e instanceof BinaryExpression) {
            String t = ((BinaryExpression) e).operation.text
            if (t == '/' || t == '+' || t == '-' || t == '*') {
                Object L = asReal(((BinaryExpression) e).leftExpression)
                Object R = asReal(((BinaryExpression) e).rightExpression)
                if (L == null || R == null) return null
                if (t == '/') {
                    if (!isTerminatingDivisor(((BinaryExpression) e).rightExpression)) return null   // Phase 143 — sound exact-div only
                    return session.realDiv(L, R)
                }
                if (t == '+') return session.plus(L, R)
                if (t == '-') return session.minus(L, R)
                return session.times(L, R)
            }
        }
        // Any other expression (a named int var, a[i], a method call). Translate it; coerce to Real
        // only if it isn't already Real — a decimal-element read `xs[i]` (Phase 70) is Real already, and
        // intToReal would be a sort error.
        Object h = translate(e)
        if (h == null) return null
        return session.isReal(h) ? h : session.intToReal(h)
    }

    // ==================== Phase 132 — JSR 385 value/scale (C₁: SI-normalized magnitudes) ====================

    /** SI base units → their scale (always 1 for a base unit; a non-coherent base like GRAM carries its factor). */
    private static final Map<String, BigDecimal> BASE_UNIT_SCALE = [
        'METRE': 1.0G, 'METER': 1.0G, 'SECOND': 1.0G, 'KILOGRAM': 1.0G, 'GRAM': 0.001G,
        'KELVIN': 1.0G, 'AMPERE': 1.0G, 'MOLE': 1.0G, 'CANDELA': 1.0G,
        // Non-SI length units (scale to metres). The international mile is exactly 1609.344 m — pinned against
        // the JSR 385 RI by UnitScaleTest, since these scales are trusted constants, not computed.
        'MILE': 1609.344G, 'YARD': 0.9144G, 'FOOT': 0.3048G, 'INCH': 0.0254G,
    ]

    /** Metric prefixes → their multiplier, so {@code KILO(METRE)} resolves to scale 1000. */
    private static final Map<String, BigDecimal> PREFIX_SCALE = [
        'GIGA': 1000000000.0G, 'MEGA': 1000000.0G, 'KILO': 1000.0G, 'HECTO': 100.0G, 'DECA': 10.0G, 'DEKA': 10.0G,
        'DECI': 0.1G, 'CENTI': 0.01G, 'MILLI': 0.001G, 'MICRO': 0.000001G, 'NANO': 0.000000001G,
    ]

    /**
     * Phase 148 — EXPERIMENTAL units DSL: a curated unit-suffix property (`1.km`, `1.mile`) → its scale-to-SI,
     * the same trusted-constant posture as {@link #BASE_UNIT_SCALE} but for the Groovy extension-method sugar a
     * consumer registers (`getKm(Number)` etc.). The verifier never compiles against the extension module — it
     * recognises the sugar *by property name* and gated on a {@code javax.measure.Quantity}-typed receiver. A
     * deliberately tiny, fixed vocabulary; anything outside it skips. See {@code examples-dsl}.
     */
    private static final Map<String, BigDecimal> DSL_SUFFIX_SCALE = [
        'm': 1.0G, 'km': 1000.0G, 'mile': 1609.344G, 'kg': 1.0G, 's': 1.0G,
        // `mps` is the *coherent SI derived unit* metre-per-second — a Speed literal whose SI magnitude IS its value.
        'mps': 1.0G,
    ]

    /**
     * Phase 151 — the *dimension* twin of {@link #BASE_UNIT_SCALE}: a base unit's exponent vector over the
     * {@code [Length, Mass, Time]} base (the same base as the Phase 131 cast-checker's {@code QUANTITY_KIND}).
     * The scale layer alone can't compare quantities (`1.m` and `1.kg` both have SI magnitude 1), so a
     * quantity-to-quantity {@code ==} consults this vector first: differing dimensions are never equal. Units
     * outside {@code [L,M,T]} (KELVIN/AMPERE/MOLE/CANDELA) are intentionally absent → unknown dimension → skip.
     */
    private static final Map<String, int[]> BASE_UNIT_DIM = [
        'METRE': [1, 0, 0] as int[], 'METER': [1, 0, 0] as int[],
        'MILE': [1, 0, 0] as int[], 'YARD': [1, 0, 0] as int[], 'FOOT': [1, 0, 0] as int[], 'INCH': [1, 0, 0] as int[],
        'KILOGRAM': [0, 1, 0] as int[], 'GRAM': [0, 1, 0] as int[],
        'SECOND': [0, 0, 1] as int[],
    ]

    /** Phase 151 — the dimension twin of {@link #DSL_SUFFIX_SCALE} for the experimental unit-suffix sugar. */
    private static final Map<String, int[]> DSL_SUFFIX_DIM = [
        'm': [1, 0, 0] as int[], 'km': [1, 0, 0] as int[], 'mile': [1, 0, 0] as int[], 'kg': [0, 1, 0] as int[],
        's': [0, 0, 1] as int[], 'mps': [1, 0, -1] as int[],     // Speed = Length·Time⁻¹
    ]

    /** Phase 151 — alias a (result/local) name to the JSR 385 Quantity expression it holds, so the magnitude /
     *  dimension readers can resolve it. See {@link #quantitySource}. */
    void registerQuantitySource(String name, Expression e) { if (name != null && e != null) quantitySource.put(name, e) }

    // ──────────────────────────── Phase 153 — Groovy 6 async/await ────────────────────────────
    // `async`/`await` lower (at parse time) to AsyncSupport.async(closure) / AsyncSupport.await(arg). By the time
    // the verifier runs, STC has resolved those static calls to StaticMethodCallExpression (the Phase 8a form), so
    // the recognisers below accept *either* a MethodCallExpression (class-receiver) or a StaticMethodCallExpression.

    private static final String ASYNC_SUPPORT_FQN = 'org.apache.groovy.runtime.async.AsyncSupport'

    /** The args of an AsyncSupport call, whichever AST form it took. */
    private static List<Expression> asyncCallArgs(Expression e) {
        if (e instanceof MethodCallExpression) return argList((MethodCallExpression) e)
        if (e instanceof StaticMethodCallExpression) {
            Expression a = ((StaticMethodCallExpression) e).arguments
            if (a instanceof org.codehaus.groovy.ast.expr.TupleExpression) return ((org.codehaus.groovy.ast.expr.TupleExpression) a).expressions
        }
        Collections.emptyList()
    }

    /** True when {@code e} is {@code AsyncSupport.<method>(…)} (either the class-receiver method call or the
     *  STC-resolved static-call form). */
    private static boolean isAsyncSupportCall(Expression e, String method) {
        if (e instanceof StaticMethodCallExpression) {
            StaticMethodCallExpression mc = (StaticMethodCallExpression) e
            return mc.method == method && mc.ownerType?.name == ASYNC_SUPPORT_FQN
        }
        if (e instanceof MethodCallExpression) {
            MethodCallExpression mc = (MethodCallExpression) e
            if (mc.methodAsString != method) return false
            Expression obj = mc.objectExpression
            if (obj instanceof ClassExpression) return ((ClassExpression) obj).type?.name == ASYNC_SUPPORT_FQN
            return obj != null && String.valueOf(obj.text).endsWith('AsyncSupport')
        }
        false
    }

    /** True when {@code e} is the lowered form of `async { … }` — {@code AsyncSupport.async(closure)}. */
    static boolean isAsyncCall(Expression e) {
        List<Expression> a = asyncCallArgs(e)
        return isAsyncSupportCall(e, 'async') && a.size() == 1 && a.get(0) instanceof ClosureExpression
    }

    /** The single value-expression of an `async { e }` closure (its sole expression / return), else null. A
     *  multi-statement or side-effecting body falls outside this slice and skips. */
    static Expression asyncBodyExpr(Expression e) {
        if (!isAsyncCall(e)) return null
        Statement code = ((ClosureExpression) asyncCallArgs(e).get(0)).code
        if (code instanceof BlockStatement) {
            List<Statement> ss = ((BlockStatement) code).statements
            if (ss.size() != 1) return null
            code = ss.get(0)
        }
        if (code instanceof ExpressionStatement) return ((ExpressionStatement) code).expression
        if (code instanceof ReturnStatement) return ((ReturnStatement) code).expression
        null
    }

    /** The value-expression an `await(arg)` reads out: the body of a direct `async { e }`, or the registered body
     *  of a local bound to one (`def fa = async { e }; await fa`). Null when the awaited source isn't a modellable
     *  safe async closure (a parameter Awaitable, a CompletableFuture from elsewhere, a racing combinator). */
    private Expression awaitedBody(Expression arg) {
        Expression a = arg
        while (a instanceof CastExpression) a = ((CastExpression) a).expression    // STC inserts (Object) casts
        // Phase 153 — a timeout wrapper is transparent under the *completion* assumption (the deadline is the
        // structural half we assume away, like mutual exclusion for locks): `await(task.orTimeoutMillis(ms))` /
        // `await(Awaitable.orTimeoutMillis(task, ms))` reads out the same value as `await(task)`. (The fallback
        // form `completeOnTimeoutMillis` is *not* unwrapped — value-or-fallback is genuinely nondeterministic.)
        Expression untimed = unwrapTimeout(a)
        if (untimed != null) return awaitedBody(untimed)
        if (isAsyncCall(a)) return asyncBodyExpr(a)
        if (a instanceof VariableExpression) return asyncSource.get(((VariableExpression) a).name)
        null
    }

    /** Peel a `…orTimeoutMillis(ms)` / `…orTimeout(ms, unit)` deadline wrapper to the task it guards (instance or
     *  static {@code Awaitable.orTimeout*} form), else null. */
    private static Expression unwrapTimeout(Expression e) {
        // static: Awaitable.orTimeoutMillis(task, ms) / Awaitable.orTimeout(task, ms, unit) — the task is the FIRST ARG.
        if (isAwaitableCall(e, 'orTimeoutMillis') || isAwaitableCall(e, 'orTimeout')) {
            List<Expression> a = asyncCallArgs(e)
            if (!a.isEmpty()) return a.get(0)
        }
        // instance: task.orTimeoutMillis(ms) / task.orTimeout(ms, unit) — the task is the RECEIVER (not the class,
        // which the static branch above already handled).
        if (e instanceof MethodCallExpression) {
            MethodCallExpression mc = (MethodCallExpression) e
            if ((mc.methodAsString == 'orTimeoutMillis' || mc.methodAsString == 'orTimeout') &&
                !(mc.objectExpression instanceof ClassExpression)) {
                return mc.objectExpression
            }
        }
        null
    }

    /** True when {@code e} is `await Awaitable.delay(ms)` — a non-blocking pause with no value and no state effect,
     *  a no-op for a logic proof (timing isn't modelled). */
    static boolean isAwaitDelayCall(Expression e) {
        if (!isAsyncSupportCall(e, 'await')) return false
        List<Expression> aw = asyncCallArgs(e)
        if (aw.size() != 1) return false
        Expression arg = aw.get(0)
        while (arg instanceof CastExpression) arg = ((CastExpression) arg).expression
        return isAwaitableCall(arg, 'delay')
    }

    /** If {@code e} is {@code AsyncSupport.await(arg)} over a safe async source, the read-out value (its body,
     *  translated); else null (skip). Called from both the method-call and static-call dispatch paths. */
    private Object tryTranslateAwait(Expression e) {
        if (!isAsyncSupportCall(e, 'await')) return null
        List<Expression> a = asyncCallArgs(e)
        if (a.size() != 1) return null
        Expression body = awaitedBody(a.get(0))
        return body != null ? translate(body) : null
    }

    /** Alias a local to the value-expression of the `async { e }` it holds (called from the body replay when an
     *  assignment's RHS {@link #isAsyncCall}). A later `await` on the local resolves through {@link #awaitedBody}. */
    void registerAsyncSource(String name, Expression e) { if (name != null && e != null) asyncSource.put(name, e) }

    /** True when {@code e} is {@code Awaitable.all(...)} — the gather-all combinator (multi-arg `await(a,b,c)`
     *  lowers to {@code AsyncSupport.await(Awaitable.all(a,b,c))}). The racing {@code any}/{@code first}
     *  combinators are deliberately NOT recognised — their result is scheduler-dependent, not a determinate value. */
    private static boolean isAwaitableCall(Expression e, String method) {
        if (e instanceof StaticMethodCallExpression) {
            StaticMethodCallExpression mc = (StaticMethodCallExpression) e
            return mc.method == method && mc.ownerType?.name == 'groovy.concurrent.Awaitable'
        }
        if (e instanceof MethodCallExpression) {
            MethodCallExpression mc = (MethodCallExpression) e
            if (mc.methodAsString != method) return false
            Expression obj = mc.objectExpression
            if (obj instanceof ClassExpression) return ((ClassExpression) obj).type?.name == 'groovy.concurrent.Awaitable'
            return obj != null && String.valueOf(obj.text).endsWith('Awaitable')
        }
        false
    }
    private static boolean isAwaitableAllCall(Expression e) { isAwaitableCall(e, 'all') }

    /** For {@code await(Awaitable.all(t1, t2, …))} over *safe* async tasks, the value LIST {@code [body1, …]} as a
     *  synthesised {@link ListExpression} — sound because {@code all} waits for every task, so the gathered list is
     *  order-independent. Null when the await arg isn't {@code Awaitable.all} over resolvable safe async sources
     *  (a racing {@code any}/{@code first}, or a task whose body the verifier can't see) → the caller skips loudly. */
    private Expression awaitAllList(Expression rhs) {
        if (!isAsyncSupportCall(rhs, 'await')) return null
        List<Expression> aw = asyncCallArgs(rhs)
        if (aw.size() != 1) return null
        Expression arg = aw.get(0)
        while (arg instanceof CastExpression) arg = ((CastExpression) arg).expression
        if (!isAwaitableAllCall(arg)) return null
        List<Expression> bodies = new ArrayList<Expression>()
        for (Expression el : asyncCallArgs(arg)) {
            Expression b = awaitedBody(el)
            if (b == null) return null      // a non-safe element → the whole gather is out of fragment
            bodies.add(b)
        }
        return new ListExpression(bodies)
    }

    /** `r = await(t1, t2, …)`: register {@code r} as the value-list factory {@code [body1, body2, …]} so
     *  {@code r[i]} / {@code r.size()} fold (riding the Phase 38 list-factory machinery). False → loud skip. */
    boolean tryRecordAwaitAll(String name, Expression rhs) {
        Expression list = awaitAllList(rhs)
        return list != null && tryRecordFactoryAssign(name, list)
    }

    /** True when {@code e} is a JSR 385 Quantity expression the readers can model both the dimension AND the
     *  magnitude of — the gate {@code checkPath} uses before aliasing a Quantity-typed {@code result}. */
    boolean isModellableQuantity(Expression e) { dimensionOf(e) != null && siMagnitude(e) != null }

    /** The Quantity source expression a variable aliases (see {@link #quantitySource}), else null. Guards against
     *  a self-alias so the readers' recursion terminates. */
    private Expression quantitySourceOf(Expression e) {
        if (!(e instanceof VariableExpression)) return null
        Expression src = quantitySource.get(((VariableExpression) e).name)
        return (src != null && !src.is(e)) ? src : null
    }

    private static int[] vadd(int[] a, int[] b) {
        if (a == null || b == null) return null
        int[] r = new int[a.length]; for (int i = 0; i < a.length; i++) r[i] = a[i] + b[i]; r
    }
    private static int[] vsub(int[] a, int[] b) {
        if (a == null || b == null) return null
        int[] r = new int[a.length]; for (int i = 0; i < a.length; i++) r[i] = a[i] - b[i]; r
    }

    /** The dimension vector of a unit expression — a base-unit constant or a (nested) prefix application (a
     *  metric prefix is dimension-neutral). Mirrors {@link #scaleOf}; null = outside the curated base → skip. */
    private int[] dimVecOf(Expression u) {
        if (u instanceof PropertyExpression) return BASE_UNIT_DIM.get(((PropertyExpression) u).propertyAsString)
        if (u instanceof VariableExpression) return BASE_UNIT_DIM.get(((VariableExpression) u).name)
        if (u instanceof MethodCallExpression) {
            MethodCallExpression mc = (MethodCallExpression) u
            List<Expression> a = argList(mc)
            if (PREFIX_SCALE.containsKey(mc.methodAsString) && a.size() == 1) return dimVecOf(a.get(0))
        }
        if (u instanceof StaticMethodCallExpression) {
            StaticMethodCallExpression mc = (StaticMethodCallExpression) u
            List<Expression> a = (mc.arguments instanceof org.codehaus.groovy.ast.expr.ArgumentListExpression) ?
                ((org.codehaus.groovy.ast.expr.ArgumentListExpression) mc.arguments).expressions : []
            if (PREFIX_SCALE.containsKey(mc.method) && a.size() == 1) return dimVecOf(a.get(0))
        }
        null
    }

    /**
     * Phase 151 — the SI *dimension* (exponent vector over {@code [L,M,T]}) of a Quantity-valued expression,
     * recovered structurally exactly as {@link #siMagnitude} recovers the magnitude: {@code getQuantity(v,U)} is
     * {@code dim(U)}; {@code to}/{@code add}/{@code subtract} keep it; {@code multiply} adds vectors and
     * {@code divide} subtracts; the DSL suffix/`+`/`-`/`*` mirror those. A scalar factor is dimension-neutral.
     * null = unknown (a parameter quantity, an uncurated unit) → the {@code ==} caller skips, never guesses.
     */
    private int[] dimensionOf(Expression e) {
        Expression src = quantitySourceOf(e)
        if (src != null) return dimensionOf(src)
        if (isGetQuantityCall(e)) {
            List<Expression> a = callArgs(e)
            return a.size() == 2 ? dimVecOf(a.get(1)) : null
        }
        if (e instanceof MethodCallExpression) {
            MethodCallExpression mc = (MethodCallExpression) e
            String m = mc.methodAsString
            List<Expression> a = argList(mc)
            if (m == 'to' && a.size() == 1) return dimensionOf(mc.objectExpression)        // unit relabel: dimension invariant
            if (m in ['add', 'subtract'] && a.size() == 1) return dimensionOf(mc.objectExpression)
            if (m in ['multiply', 'divide'] && a.size() == 1) {
                int[] dRecv = dimensionOf(mc.objectExpression)
                if (dRecv == null) return null
                Expression arg = a.get(0)
                if (isNumericScalar(arg)) return dRecv                                       // scalar ×/÷ keeps dimension
                int[] dArg = dimensionOf(arg)
                return m == 'multiply' ? vadd(dRecv, dArg) : vsub(dRecv, dArg)
            }
        }
        if (e instanceof PropertyExpression) {
            PropertyExpression pe = (PropertyExpression) e
            int[] d = DSL_SUFFIX_DIM.get(pe.propertyAsString)
            if (d != null && isQuantityExpr(pe)) return d
        }
        if (e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e
            String op = be.operation.text
            if (!isQuantityExpr(e)) return null
            if (op == '+' || op == '-') return dimensionOf(be.leftExpression)               // same-dimension (STC-enforced)
            if (op == '*' || op == '/') {
                int[] l = isNumericScalar(be.leftExpression) ? ([0, 0, 0] as int[]) : dimensionOf(be.leftExpression)
                int[] r = isNumericScalar(be.rightExpression) ? ([0, 0, 0] as int[]) : dimensionOf(be.rightExpression)
                return op == '*' ? vadd(l, r) : vsub(l, r)                                   // Length/Time = Speed [1,0,-1]
            }
        }
        null
    }

    /** The scale-to-SI of a unit expression — a base-unit constant or a (nested) prefix application — or null. */
    private BigDecimal scaleOf(Expression u) {
        if (u instanceof PropertyExpression) return BASE_UNIT_SCALE.get(((PropertyExpression) u).propertyAsString)
        if (u instanceof VariableExpression) return BASE_UNIT_SCALE.get(((VariableExpression) u).name)
        if (u instanceof MethodCallExpression) {
            MethodCallExpression mc = (MethodCallExpression) u
            BigDecimal p = PREFIX_SCALE.get(mc.methodAsString)
            List<Expression> a = argList(mc)
            if (p != null && a.size() == 1) { BigDecimal inner = scaleOf(a.get(0)); return inner == null ? null : p * inner }
        }
        if (u instanceof StaticMethodCallExpression) {
            StaticMethodCallExpression mc = (StaticMethodCallExpression) u
            BigDecimal p = PREFIX_SCALE.get(mc.method)
            List<Expression> a = (mc.arguments instanceof org.codehaus.groovy.ast.expr.ArgumentListExpression) ?
                ((org.codehaus.groovy.ast.expr.ArgumentListExpression) mc.arguments).expressions : []
            if (p != null && a.size() == 1) { BigDecimal inner = scaleOf(a.get(0)); return inner == null ? null : p * inner }
        }
        null
    }

    /** True for a {@code tech.units.indriya.quantity.Quantities.getQuantity(value, unit)} construction. */
    private static boolean isGetQuantityCall(Expression e) {
        if (e instanceof MethodCallExpression) {
            MethodCallExpression mc = (MethodCallExpression) e
            return mc.methodAsString == 'getQuantity' && String.valueOf(mc.objectExpression?.text).endsWith('Quantities')
        }
        if (e instanceof StaticMethodCallExpression) {
            StaticMethodCallExpression mc = (StaticMethodCallExpression) e
            return mc.method == 'getQuantity' && String.valueOf(mc.ownerType?.name).endsWith('Quantities')
        }
        false
    }

    /** A scalar (dimensionless number) factor for {@code multiply}/{@code divide} — a numeric literal or a
     *  numeric-typed expression, never a Quantity. */
    private static boolean isNumericScalar(Expression e) {
        if (e instanceof ConstantExpression) return ((ConstantExpression) e).value instanceof Number
        ClassNode t = null
        try { t = e?.getType() } catch (ignored) {}
        if (t == null || t.name == null) return false
        String n = t.name
        n in ['int', 'long', 'short', 'byte', 'double', 'float',
              'java.lang.Integer', 'java.lang.Long', 'java.lang.Short', 'java.lang.Byte',
              'java.lang.Double', 'java.lang.Float', 'java.math.BigDecimal', 'java.math.BigInteger', 'java.lang.Number']
    }

    /**
     * The SI magnitude (a Real term) of a Quantity-valued expression, recovered from its construction:
     * {@code getQuantity(v, U)} is {@code v·scale(U)}, {@code to(U)} is magnitude-invariant, {@code add}/{@code
     * subtract} combine same-dimension magnitudes (the dimension match is what STC already enforces on these),
     * and {@code multiply}/{@code divide} take a Quantity or a scalar. A Quantity whose construction isn't
     * visible (a parameter) → null, i.e. out of scope.
     */
    private Object siMagnitude(Expression e) {
        Expression src = quantitySourceOf(e)
        if (src != null) return siMagnitude(src)
        if (isGetQuantityCall(e)) {
            List<Expression> a = callArgs(e)
            if (a.size() != 2) return null
            BigDecimal s = scaleOf(a.get(1))
            Object vR = asReal(a.get(0))
            if (s == null || vR == null) return null
            return (s.compareTo(BigDecimal.ONE) == 0) ? vR : session.times(vR, session.realLit(rationalOf(s)))
        }
        if (e instanceof MethodCallExpression) {
            MethodCallExpression mc = (MethodCallExpression) e
            String m = mc.methodAsString
            List<Expression> a = argList(mc)
            if (m == 'to' && a.size() == 1) return siMagnitude(mc.objectExpression)         // unit relabel: magnitude invariant
            if (m in ['add', 'subtract', 'multiply', 'divide'] && a.size() == 1) {
                Object recvM = siMagnitude(mc.objectExpression)
                if (recvM == null) return null
                Expression arg = a.get(0)
                Object other
                if (m == 'add' || m == 'subtract') {
                    other = siMagnitude(arg)                  // add/subtract take a same-dimension Quantity (STC-enforced)
                } else {
                    Object q = siMagnitude(arg)               // multiply/divide: a Quantity if we can model it,
                    other = q != null ? q : (isNumericScalar(arg) ? asReal(arg) : null)   // else a numeric scalar
                }
                if (other == null) return null
                if (m == 'add')      return session.plus(recvM, other)
                if (m == 'subtract') return session.minus(recvM, other)
                if (m == 'multiply') return session.times(recvM, other)
                return session.realDiv(recvM, other)                                          // divide
            }
        }
        // Phase 148 (experimental DSL) — a curated unit-suffix property `v.km` is `v · scale`, and the DSL `+`/`-`
        // (the registered `plus`/`minus` extension operators) combine same-dimension magnitudes. Gated on a
        // javax.measure.Quantity-typed expression so a stray `.m` on a non-quantity can't be misread as a unit.
        if (e instanceof PropertyExpression) {
            PropertyExpression pe = (PropertyExpression) e
            BigDecimal sc = DSL_SUFFIX_SCALE.get(pe.propertyAsString)
            if (sc != null && isQuantityExpr(pe)) {
                Object vR = asReal(pe.objectExpression)
                if (vR == null) return null
                return (sc.compareTo(BigDecimal.ONE) == 0) ? vR : session.times(vR, session.realLit(rationalOf(sc)))
            }
        }
        if (e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e
            String op = be.operation.text
            if ((op == '+' || op == '-') && isQuantityExpr(e)) {
                Object l = siMagnitude(be.leftExpression)
                Object r = siMagnitude(be.rightExpression)
                if (l == null || r == null) return null
                return op == '+' ? session.plus(l, r) : session.minus(l, r)
            }
            // Phase 150/152 — the DSL `*` (Quantity.multiply) and `/` (Quantity.divide): magnitudes multiply/divide.
            // `1.km * 1.km` is an *area* whose SI magnitude is 1000·1000 = 1e6 (m²); `1.m / 1.s` is a *speed* whose SI
            // magnitude is 1 (m/s). A scalar factor multiplies/divides the magnitude. (The dimension the operator
            // produces is invisible to the magnitude alone — the dimension reader / the .value read-out make it
            // observable to the verifier.)
            if ((op == '*' || op == '/') && isQuantityExpr(e)) {
                Object l = siMagnitude(be.leftExpression)
                if (l == null && isNumericScalar(be.leftExpression)) l = asReal(be.leftExpression)
                Object r = siMagnitude(be.rightExpression)
                if (r == null && isNumericScalar(be.rightExpression)) r = asReal(be.rightExpression)
                if (l == null || r == null) return null
                if (op == '*') return session.times(l, r)
                // Phase 143 posture: exact Real division is sound only for a terminating divisor (Groovy rounds the
                // rest, e.g. `/3`). The divisor here is a *quantity's magnitude*, not a syntactic literal, so guard on
                // the right operand's scale being a terminating decimal — a unit scale (1, 1000, 1609.344) always is.
                if (!isTerminatingQuantityDivisor(be.rightExpression)) return null
                return session.realDiv(l, r)
            }
        }
        null
    }

    /** Phase 152 — true when the divisor {@code e}'s SI magnitude is a *closed terminating decimal*, so exact Real
     *  division is sound (Groovy/indriya round a non-terminating quotient, which the exact Real model would not — and
     *  a later multiply-back could then "verify" a runtime-false contract, the Phase 143 hazard). We compute the full
     *  magnitude (value·scale, including the unit scale — so {@code 1.mile} = 1609.344, which has a factor of 3, is
     *  correctly rejected) and test it has only the prime factors 2 and 5; a symbolic divisor (a parameter) → false. */
    private boolean isTerminatingQuantityDivisor(Expression e) {
        BigDecimal m = closedQuantityMagnitude(e)
        return m != null && isTerminatingDecimal(m)
    }

    /** The SI magnitude of a Quantity (or scalar) expression as a literal {@link BigDecimal}, when it's fully closed
     *  over numeric literals and curated units; null if anything is symbolic (a name, a parameter). The BigDecimal
     *  twin of {@link #siMagnitude}, used only by the division soundness guard. */
    private BigDecimal closedQuantityMagnitude(Expression e) {
        if (e == null) return null
        Expression src = quantitySourceOf(e)
        if (src != null) return closedQuantityMagnitude(src)        // a quantity local resolves to its RHS
        if (e instanceof UnaryMinusExpression) {
            BigDecimal inner = closedQuantityMagnitude(((UnaryMinusExpression) e).expression)
            return inner == null ? null : inner.negate()
        }
        if (e instanceof ConstantExpression) {
            Object v = ((ConstantExpression) e).value
            if (!(v instanceof Number) || v instanceof Double || v instanceof Float) return null
            try { return new BigDecimal(v.toString()) } catch (Exception ignored) { return null }
        }
        if (e instanceof PropertyExpression) {
            PropertyExpression pe = (PropertyExpression) e
            BigDecimal sc = DSL_SUFFIX_SCALE.get(pe.propertyAsString)
            if (sc == null) return null
            BigDecimal v = closedQuantityMagnitude(pe.objectExpression)
            return v == null ? null : v.multiply(sc)
        }
        if (e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e
            String op = be.operation.text
            BigDecimal l = closedQuantityMagnitude(be.leftExpression)
            BigDecimal r = closedQuantityMagnitude(be.rightExpression)
            if (l == null || r == null) return null
            switch (op) {
                case '+': return l.add(r)
                case '-': return l.subtract(r)
                case '*': return l.multiply(r)
                case '/': return (r.signum() == 0 || !isTerminatingDecimal(r)) ? null : l.divide(r)
            }
        }
        null
    }

    /** A BigDecimal whose unscaled integer has only the prime factors 2 and 5 — i.e. a *terminating* decimal, safe
     *  as an exact Real divisor (the value-level twin of {@link #isTerminatingDivisor}'s expression test). */
    private static boolean isTerminatingDecimal(BigDecimal bd) {
        if (bd == null || bd.signum() == 0) return false
        BigInteger u = bd.unscaledValue().abs()
        BigInteger two = BigInteger.valueOf(2), five = BigInteger.valueOf(5)
        while (u.mod(two).signum() == 0) u = u.divide(two)
        while (u.mod(five).signum() == 0) u = u.divide(five)
        u.equals(BigInteger.ONE)
    }

    /** Phase 148 — true when {@code e}'s (STC-inferred) type is {@code javax.measure.Quantity} — the gate that
     *  keeps the experimental DSL recognisers off non-quantity property reads / operators. The kind comes from
     *  STC's {@code INFERRED_TYPE} node metadata (a `+`/property's syntactic {@code getType()} is just Object). */
    private static boolean isQuantityTyped(Expression e) {
        if (e == null) return false
        ClassNode t = (ClassNode) e.getNodeMetaData(org.codehaus.groovy.transform.stc.StaticTypesMarker.INFERRED_TYPE)
        if (t == null) { try { t = e.getType() } catch (ignored) {} }
        t != null && t.name == 'javax.measure.Quantity'
    }

    /**
     * Phase 151 — is {@code e} a JSR 385 Quantity expression, for the DSL readers' gate? Prefers STC's
     * {@code INFERRED_TYPE} ({@link #isQuantityTyped}), but falls back to a *structural* recognition of the
     * curated DSL shapes when that metadata is absent. The metadata IS absent inside an {@code @Ensures}
     * closure — captured at CONVERSION, before type-checking — so `result == 1.km` needs this to see the `1.km`.
     * The fallback is tight: a curated unit suffix on a numeric receiver ({@code 1.km}), or a {@code +}/{@code -}/
     * {@code *} of such — never a bare `.m` on an arbitrary object.
     */
    static boolean isQuantityExpr(Expression e) {
        if (e == null) return false
        if (isQuantityTyped(e)) return true
        if (e instanceof PropertyExpression) {
            PropertyExpression pe = (PropertyExpression) e
            return DSL_SUFFIX_SCALE.containsKey(pe.propertyAsString) && isNumericReceiver(pe.objectExpression)
        }
        if (e instanceof BinaryExpression) {
            String op = ((BinaryExpression) e).operation.text
            if (op == '+' || op == '-' || op == '*' || op == '/') {
                return isQuantityExpr(((BinaryExpression) e).leftExpression) ||
                       isQuantityExpr(((BinaryExpression) e).rightExpression)
            }
        }
        false
    }

    /** A numeric receiver for a DSL unit suffix — a numeric literal ({@code 1.km}) or numeric-typed expression. */
    private static boolean isNumericReceiver(Expression r) {
        if (r instanceof ConstantExpression) return ((ConstantExpression) r).value instanceof Number
        return isNumericScalar(r)
    }

    /** Phase 148 — the scale of an expression's *current* unit, for a getValue read-out: a unit-suffix property's
     *  scale, a {@code to(U)} / {@code getQuantity(_, U)}'s unit, or (for the DSL `+`/`-` and `add`/`subtract`) the
     *  receiver's unit, which those keep. {@code value-in-unit = siMagnitude / currentUnitScale}. */
    private BigDecimal currentUnitScale(Expression e) {
        Expression src = quantitySourceOf(e)
        if (src != null) return currentUnitScale(src)
        if (e instanceof PropertyExpression) {
            BigDecimal sc = DSL_SUFFIX_SCALE.get(((PropertyExpression) e).propertyAsString)
            if (sc != null) return sc
        }
        if (e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e
            String op = be.operation.text
            if (op == '+' || op == '-') return currentUnitScale(be.leftExpression)
            // Phase 150/152 — a product/quotient's current unit is the product/quotient of the operands' units
            // (km · km = km², scale 1e6; m / s = m·s⁻¹, scale 1), so `(1.km * 1.km).value` reads back 1e6/1e6 = 1 and
            // `(1.m / 1.s).value` reads back 1. A scalar factor carries unit-scale 1.
            if (op == '*' || op == '/') {
                BigDecimal l = currentUnitScale(be.leftExpression)
                if (l == null && isNumericScalar(be.leftExpression)) l = 1.0G
                BigDecimal r = currentUnitScale(be.rightExpression)
                if (r == null && isNumericScalar(be.rightExpression)) r = 1.0G
                if (l == null || r == null) return null
                if (op == '*') return l * r
                return (r.signum() == 0 || !isTerminatingDecimal(r)) ? null : l.divide(r)
            }
        }
        if (e instanceof MethodCallExpression) {
            MethodCallExpression mc = (MethodCallExpression) e
            List<Expression> a = argList(mc)
            if (mc.methodAsString == 'to' && a.size() == 1) return scaleOf(a.get(0))
            if (mc.methodAsString in ['add', 'subtract'] && a.size() == 1) return currentUnitScale(mc.objectExpression)
        }
        if (isGetQuantityCall(e)) {
            List<Expression> a = callArgs(e)
            if (a.size() == 2) return scaleOf(a.get(1))
        }
        null
    }

    /** {@code X.getValue()} (or the property `X.value`) as a Real — the SI magnitude read back in X's *current*
     *  unit, i.e. {@code siMagnitude(X) / currentUnitScale(X)}. Modelled only when both are syntactically known
     *  (a {@code to(U)} / {@code getQuantity(_, U)} top, or the experimental DSL forms); else null (skips). */
    private Object quantityValueTerm(Expression recv) {
        Object mag = siMagnitude(recv)
        BigDecimal s = currentUnitScale(recv)
        if (mag == null || s == null) return null
        return (s.compareTo(BigDecimal.ONE) == 0) ? mag : session.realDiv(mag, session.realLit(rationalOf(s)))
    }

    /** A BigDecimal/Double/Float as a Z3 rational numeral string ("25/10" for 2.5G). */
    private static String rationalOf(Object value) {
        BigDecimal bd = (value instanceof BigDecimal) ? (BigDecimal) value : new BigDecimal(value.toString())
        bd = bd.stripTrailingZeros()
        int scale = bd.scale()
        if (scale <= 0) {
            return bd.unscaledValue().multiply(BigInteger.TEN.pow(-scale)).toString()
        }
        return bd.unscaledValue().toString() + '/' + BigInteger.TEN.pow(scale).toString()
    }

    private Object translateBinary(BinaryExpression be) {
        // Phase 8a — normalise-then-SMT: fold a closed numeric subexpression to a
        // literal before encoding. This dissolves the NIA opt-out for *constant*
        // products (e.g. `(2 + 2) * (2 + 2)`), which would otherwise be skipped.
        // Reuses Groovy's own constant folder, so the arithmetic semantics match.
        Object folded = tryFoldConstant(be)
        if (folded != null) return folded

        int op = be.operation.type

        // Phase 89 — reference identity `a === b` / `a !== b` between object references → identity
        // equality on their object ids (not a value comparison). Falls through if either side isn't
        // an object parameter (so `===` outside this fragment still skips loudly).
        if (be.operation.text == '===' || be.operation.text == '!==') {
            Object idEq = refIdentityEq(be.leftExpression, be.rightExpression)
            if (idEq != null) return be.operation.text == '===' ? idEq : session.not(idEq)
        }

        // Phase 81 — component-wise tuple/list equality: `t1 == t2` (or `==` a tuple/list literal) folds to
        // the conjunction of pairwise component equalities (same arity); `!=` is its negation. Preempts the
        // scalar paths below, which would skip on a tuple operand. Only fires when both sides are products.
        if (op == Types.COMPARE_EQUAL || op == Types.COMPARE_NOT_EQUAL) {
            Object te = translateTupleEquality(be, op == Types.COMPARE_EQUAL)
            if (te != null) return te
        }

        // Phase 133 — an arithmetic operator on a carrier (record / wrapper) operand has no numeric meaning
        // in the encoder (Groovy dispatches `a + b` to `a.plus(b)`, etc.). Skip gracefully rather than feed a
        // datatype term into the numeric path below, which would cast it to an arithmetic term and crash.
        // (Routing the operator to its carrier method — so `a + b` verifies via the method's contract — is a
        // future slice; for now an operator-on-carrier is an honest out-of-fragment skip.)
        if ((op == Types.PLUS || op == Types.MINUS || op == Types.MULTIPLY || op == Types.DIVIDE) &&
            (carrierTypeOf(be.leftExpression) != null || carrierTypeOf(be.rightExpression) != null)) {
            return null
        }

        // Array subscript a[i] -> (select a i). The element value, modelled under
        // Z3's array theory (Phase 6). Recorded as a trigger when inside a quantifier.
        // The base is a named array a, or old.a (the entry-snapshot array, keyed old$a).
        if (op == Types.LEFT_SQUARE_BRACKET) {
            // Phase 38 — `[a, b, c][i]` / `Map.of(k, v)[k']` / `[k:v][k']`: factory receiver
            // peephole-folds to the i-th element (for constant i) or an ite-chain over entries.
            // For an EMPTY list factory ({@code positive = []}) with a symbolic index — common
            // in invariants over a list local that's being filled — the fold returns null and we
            // fall through to the regular array-handle path below, which gets the right element
            // sort from {@code listElementTypes} (so {@code result[k].startsWith(p)} works for
            // a {@code List<String> result = []}).
            FactoryContainer factoryL = factoryContainerFor(be.leftExpression)
            if (factoryL != null) {
                if (factoryL.kind == 'list') {
                    Object foldedList = foldFactoryListIndex(factoryL.args, be.rightExpression)
                    if (foldedList != null) return foldedList
                    // fall through to arrayHandleFor for the empty-factory case.
                } else if (factoryL.kind == 'map') {
                    return foldFactoryMapLookup(factoryL, be.rightExpression)
                }
            }
            // Phase 80/82 — t[k] (constant k) on a (possibly nested) tuple parameter → the slot's typed entity.
            if (be.rightExpression instanceof ConstantExpression &&
                ((ConstantExpression) be.rightExpression).value instanceof Integer) {
                Object te = tupleParamSlot(be.leftExpression,
                                           (Integer) ((ConstantExpression) be.rightExpression).value)
                if (te != null) return te
            }
            // m[k] over a map reads its value array (key in map's key sort); a[i] over an array
            // or list reads its contents (index in Int). Phase 27: route map keys through the
            // declared key sort so a Map<String, Integer> can do m["admin"] cleanly.
            // Phase 38c — unwrap a transparent immutability wrapper on the receiver so
            // {@code Collections.unmodifiableList(xs)[i]} resolves to {@code xs[i]}.
            Expression bracketRecv = unwrapImmutableWrap(be.leftExpression)
            String mlog = mapLogicalFor(bracketRecv)
            Object arr = mlog != null ? mapValsFor(mlog) : arrayHandleFor(bracketRecv)
            if (arr == null) return null
            Object idx
            if (mlog != null) {
                ClassNode[] pair = mapTypes.get(mlog)
                Object kSort = sortFor(pair != null ? pair[0] : null)
                idx = translateInSort(be.rightExpression, kSort)
            } else {
                idx = translate(be.rightExpression)
            }
            if (idx == null) return null
            Object sel = session.select(arr, idx)
            if (triggerSink != null) triggerSink.add(sel)
            return sel
        }

        // Set membership: `x in s` / `x !in s` over a known set-typed receiver. Lowers to the
        // characteristic-array query (select s x) == 1, riding Z3's array theory — so an add
        // (a store) is related to a later membership read for free. The element is translated in
        // the receiver's element sort (Phase 27 — Int by default, String/Enum when typed).
        String sym = be.operation.text
        if (sym == 'in' || sym == '!in') {
            // `x in s` (set membership) or `k in m` (map key membership — same as m.containsKey(k)).
            // Phase 38c — unwrap a transparent immutability wrapper on the receiver so
            // {@code x in Collections.unmodifiableList(xs)} resolves to {@code x in xs}.
            Expression inRecv = unwrapImmutableWrap(be.rightExpression)
            String setKey = setKeyFor(inRecv)
            String mapLog = setKey == null ? mapLogicalFor(inRecv) : null
            if (setKey != null || mapLog != null) {
                Object elemSort = setKey != null ? setKeySortForKey(setKey) :
                                  sortFor(mapTypes.get(mapLog) != null ? mapTypes.get(mapLog)[0] : null)
                Object elem = translateInSort(be.leftExpression, elemSort)
                if (elem == null) return null
                Object setH = setKey != null ? setFor(setKey) : mapKeysFor(mapLog)
                Object mem = member(setH, elem)
                return sym == 'in' ? mem : session.not(mem)
            }
            // Phase 33 — `x in (a + b)` / `x !in (a + b)` / `x in a.intersect(b)`: the lazy
            // union/intersection lowering applied to the membership operator. Mirror of the
            // (s + t).contains(x) path in translateMethodCall.
            SetBinop binop = setBinopFor(inRecv)
            if (binop != null) {
                Object elem = translateInSort(be.leftExpression, binop.elemSort)
                if (elem == null) return null
                Object lMem = member(setFor(binop.leftKey), elem)
                Object rMem = member(setFor(binop.rightKey), elem)
                Object mem = setCombineMembership(binop.kind, lMem, rMem)
                return sym == 'in' ? mem : session.not(mem)
            }
            // Phase 36 — `x in m[k]` over a known Map<K, Set<V>>: lower to membership in the inner
            // set (an SMT array term, never minted as a named handle).
            NestedSetReceiver nr = nestedSetReceiverFor(inRecv)
            if (nr != null) {
                Object elem = translateInSort(be.leftExpression, nr.innerElemSort)
                if (elem == null) return null
                Object mem = member(nr.innerSet, elem)
                return sym == 'in' ? mem : session.not(mem)
            }
            // Phase 38 — `x in [a, b, c]` / `x in List.of(…)` / `x in [k: v]`: peephole disjunction
            // over the recognised factory's elements (or keys, for map factories — matching the
            // Groovy `in` semantics: `k in m` tests key membership, mirror of containsKey).
            FactoryContainer factoryR = factoryContainerFor(inRecv)
            if (factoryR != null) {
                Object xH = translate(be.leftExpression)
                if (xH == null) return null
                List<Expression> probe = (factoryR.kind == 'map') ? factoryR.keys : factoryR.args
                Object disj = foldContainsDisjunction(xH, probe)
                if (disj == null) return null
                return sym == 'in' ? disj : session.not(disj)
            }
            // Phase 99 — `i in lo..hi` (integer range → bounds) / `s in 'A'..'Z'` (char range → regex class).
            Object rangeMem = translateIntRangeContains(inRecv, be.leftExpression)
            if (rangeMem == null) rangeMem = translateStringRangeContains(inRecv, be.leftExpression)
            if (rangeMem != null) return sym == 'in' ? rangeMem : session.not(rangeMem)
        }

        // Nullity: x == null / x != null, before we try to translate `null`.
        if (op == Types.COMPARE_EQUAL || op == Types.COMPARE_NOT_EQUAL) {
            VariableExpression ref = nullComparisonTarget(be)
            if (ref != null) {
                Object isNull = nullityOf(ref.name)
                return op == Types.COMPARE_EQUAL ? isNull : session.not(isNull)
            }
            // Phase 37 — xs[i] == null / xs.get(i) == null and their `!=` mirrors: lower to the
            // per-element nullity oracle. Lets a @Requires({ xs[i] != null }) constrain the same
            // flag the implicit deref obligation later asserts the negation of.
            IndexedNullTarget ind = indexedNullComparisonTarget(be)
            if (ind != null) {
                Object idxH = translate(ind.indexExpr)
                if (idxH != null) {
                    Object flag = session.select(elementNullityFor(ind.containerName), idxH)
                    Object isNull = session.eq(flag, session.intLit(1L))
                    return op == Types.COMPARE_EQUAL ? isNull : session.not(isNull)
                }
            }
        }

        // Phase 151 — quantity-to-quantity equality `a == b` (and `!=`) between two JSR 385 Quantity values.
        // Sound only by consulting BOTH layers: the dimension (compile-time exponent vector) decides whether the
        // comparison can be true at all, and only when dimensions agree does the SI magnitude (Z3 Real) settle the
        // value. Different dimensions are NEVER equal — `1.m == 1.kg` THROWS UnconvertibleException at runtime (so
        // `==` can't be true → refute; `!=` can't be proved true → skip). Equal dimensions fall to magnitude
        // equality (`1.km == 1000.m` → true). A dimension or magnitude unknown (a parameter quantity) → skip loudly.
        if (op == Types.COMPARE_EQUAL || op == Types.COMPARE_NOT_EQUAL) {
            int[] dL = dimensionOf(be.leftExpression)
            int[] dR = dimensionOf(be.rightExpression)
            if (dL != null && dR != null) {                           // both sides modellable Quantity expressions
                if (!java.util.Arrays.equals(dL, dR)) {
                    // Different dimension: at runtime the comparison THROWS UnconvertibleException — it is neither
                    // true nor false (empirically pinned). So `==` can never hold → model `false` (it refutes,
                    // which is sound: we never prove it true). But `!=` must NOT be proved *true* — the method would
                    // throw at its own contract check, so a "verified" there would be unsound. Skip `!=` loudly.
                    return op == Types.COMPARE_EQUAL ? session.boolLit(false) : null
                }
                Object mL = siMagnitude(be.leftExpression)
                Object mR = siMagnitude(be.rightExpression)
                if (mL == null || mR == null) return null             // dimension known but magnitude isn't → skip
                Object eq = session.eq(mL, mR)                        // same dimension: magnitude settles it (runtime compareTo)
                return op == Types.COMPARE_EQUAL ? eq : session.not(eq)
            }
            // a side's dimension is unknown (a parameter quantity) → out of fragment; fall through to a loud skip.
        }

        // Phase 47 — String concatenation via the {@code +} operator. When both operands are
        // String-typed, translate each in the String sort and dispatch to {@code stringConcat}
        // rather than the integer {@code plus}. The {@link #isStringReceiver} helper recognises
        // String literals, String parameters, and {@code xs[i]} on a {@code List<String>}.
        if (op == Types.PLUS && isStringReceiver(be.leftExpression) && isStringReceiver(be.rightExpression)) {
            Object strSort = session.declareSort('String')
            Object lH = translateInSort(be.leftExpression, strSort)
            Object rH = translateInSort(be.rightExpression, strSort)
            if (lH != null && rH != null) return session.stringConcat(lH, rH)
        }

        // Phase 47j — Groovy's match operator `s ==~ regex` is a whole-string match, semantically exactly
        // `s.matches(regex)`. Route it to the same `str.in_re` lowering: a String left and a regex literal
        // the inline parser handles. (`=~`, the *find* operator, returns a Matcher and stays out.)
        if (op == Types.MATCH_REGEX) {
            Object strSort = session.declareSort('String')
            Object lH = translateInSort(be.leftExpression, strSort)
            Object re = parseRegexLiteral(be.rightExpression)
            return (lH != null && re != null) ? session.stringInRegex(lH, re) : null
        }

        // Phase 61 — BigDecimal arithmetic & comparison via Z3's exact Real sort. Fires when an
        // operand is a decimal (literal or BigDecimal-typed name) or the operator is `/` (Groovy's
        // `/` on integers is BigDecimal division: 5 / 2 == 2.5). Int operands are coerced via
        // int→real; the `b != 0` divide obligation is still collected as a DivideSite. Anything that
        // can't be lowered to Real returns null (loud skip) rather than the integer path.
        boolean cmpOp = (op == Types.COMPARE_EQUAL || op == Types.COMPARE_NOT_EQUAL ||
                         op == Types.COMPARE_LESS_THAN || op == Types.COMPARE_LESS_THAN_EQUAL ||
                         op == Types.COMPARE_GREATER_THAN || op == Types.COMPARE_GREATER_THAN_EQUAL)
        boolean decimalCmp = cmpOp && (isDecimalExpr(be.leftExpression) || isDecimalExpr(be.rightExpression))
        if (isDecimalExpr(be) || decimalCmp) {
            Object dl = asReal(be.leftExpression)
            Object dr = asReal(be.rightExpression)
            if (dl == null || dr == null) return null
            if (decimalCmp) {
                switch (op) {
                    case Types.COMPARE_EQUAL:              return session.eq(dl, dr)
                    case Types.COMPARE_NOT_EQUAL:          return session.not(session.eq(dl, dr))
                    case Types.COMPARE_LESS_THAN:          return session.lt(dl, dr)
                    case Types.COMPARE_LESS_THAN_EQUAL:    return session.le(dl, dr)
                    case Types.COMPARE_GREATER_THAN:       return session.gt(dl, dr)
                    case Types.COMPARE_GREATER_THAN_EQUAL: return session.ge(dl, dr)
                }
            }
            switch (be.operation.text) {
                case '/':
                    // Phase 143 — exact Real division is sound only for a terminating divisor; Groovy rounds the
                    // rest (`/3`, `/7`, a symbolic divisor), so skip those rather than prove a runtime-false fact.
                    if (!isTerminatingDivisor(be.rightExpression)) return null
                    return session.realDiv(dl, dr)
                case '+': return session.plus(dl, dr)
                case '-': return session.minus(dl, dr)
                case '*': return session.times(dl, dr)
            }
            return null
        }
        // Phase 67 — a decimal operand on an operator the Real path doesn't model (notably `%`, whose
        // BigDecimal remainder Z3's real theory has no clean primitive for): skip loudly rather than
        // fall through to the integer path below, which would translate the decimals as meaningless
        // int shadows (a spurious divide-by-zero / wrong remainder).
        if (isDecimalExpr(be.leftExpression) || isDecimalExpr(be.rightExpression)) return null

        // Phase 73 — IEEE-754 floating point: double/float arithmetic and comparison via Z3's FP theory.
        // Fires when an operand is FP (a double/float name or a Double/Float literal). Comparisons use
        // IEEE semantics (`==` is fp.eq, so NaN != NaN); arithmetic rounds RNE. Anything not purely FP
        // (e.g. an int operand) returns null → loud skip.
        boolean fpCmp = cmpOp && (isFpValued(be.leftExpression) || isFpValued(be.rightExpression))
        if (isFpValued(be) || fpCmp) {
            if (fpCmp) {
                Object fl = asFp(be.leftExpression), fr = asFp(be.rightExpression)
                if (fl == null || fr == null) return null
                switch (op) {
                    case Types.COMPARE_EQUAL:              return session.fpEq(fl, fr)
                    case Types.COMPARE_NOT_EQUAL:          return session.not(session.fpEq(fl, fr))
                    case Types.COMPARE_LESS_THAN:          return session.fpLt(fl, fr)
                    case Types.COMPARE_LESS_THAN_EQUAL:    return session.fpLeq(fl, fr)
                    case Types.COMPARE_GREATER_THAN:       return session.fpGt(fl, fr)
                    case Types.COMPARE_GREATER_THAN_EQUAL: return session.fpGeq(fl, fr)
                }
            }
            return asFp(be)   // arithmetic (or null → skip)
        }

        Object L = translate(be.leftExpression)
        Object R = translate(be.rightExpression)
        if (L == null || R == null) return null
        // Phase 129 — a String/sequence operand reached the arithmetic/comparison dispatch, which is typed for
        // the Int sort and would throw (an {@code ArithExpr} cast in {@code plus}, or a sort-mismatch in
        // {@code mkEq}). The static {@link #isStringReceiver} route above only fires when both operand
        // *expressions* are statically recognisable as String, so two shapes slip past it: a combiner's
        // `a + b` inlined at a fold site (formals bound to seq handles, their types invisible here), and a
        // String-returning call whose result was modelled as a generic Int handle then compared to a String.
        // Decide by the translated operand *sort* instead: `+` on two sequences is concatenation (the genuine
        // string concat the inline intended); a lone sequence operand against a non-sequence has no fragment
        // meaning — skip loudly rather than crash. Two sequences under `==`/`!=` fall through to the
        // sort-polymorphic {@code eq}/{@code ne} in the switch below (this is how the string-law examples run).
        if (op == Types.PLUS && session.isSeq(L) && session.isSeq(R)) return session.stringConcat(L, R)
        if (session.isSeq(L) != session.isSeq(R)) return null
        // Phase 48 — operator-text dispatch for {@code /} and {@code %}: Groovy's parser
        // assigns {@code %} a token outside {@code Types.MOD} (same caveat ObligationCollector
        // notes), so {@code op.text} is the robust key. Used for both div and mod for parity
        // with the existing divide-site collection logic.
        String opText = be.operation.text
        if (opText == '/' || opText == '\\') {
            // Groovy's `/` on integers is *BigDecimal* division (5 / 2 == 2.5G), not integer
            // division — outside the integer fragment, so skip loudly. Genuine integer division is
            // `a.intdiv(b)` (translateMethodCall) or `(int)(a / b)` (the CastExpression handler).
            // The `b != 0` safety obligation is still collected as a DivideSite.
            return null
        }
        if (opText == '%') {
            // Groovy's `%` operator is the truncated, sign-of-dividend remainder (-5 % 2 == -1),
            // i.e. `a.remainder(b)` — NOT the non-negative `a.mod(b)`.
            return session.intRem(L, R)
        }
        if (opText == '==>') {
            // Groovy 5's logical-implication operator (a BinaryExpression with the IMPLIES token):
            // `a ==> b` ≡ `!a || b`. The boolean-method form `a.implies(b)` is handled in
            // translateMethodCall; both reuse the backend's existing `implies` primitive.
            return session.implies(L, R)
        }
        Object bw = translateBitwise(op, be, L, R)
        if (bw != null) return bw
        switch (op) {
            case Types.PLUS:                return session.plus(L, R)
            case Types.MINUS:               return session.minus(L, R)
            case Types.MULTIPLY:
                // Phase 48 — NIA: any-operand multiplication translates directly through to
                // Z3's NIA solver. Previously (Phase 8a) this opted out when both operands
                // were non-literal, conservatively staying in QF_LIA. Z3's per-VC 2s timeout
                // now protects against the NIA-hang case (an "UNKNOWN" returns "could not
                // decide" — honest, never silent), and the suite-wide tryFoldConstant in
                // Phase 8a still folds closed numeric subexpressions before reaching here.
                return session.times(L, R)
            case Types.POWER:
                // Phase 93 — `base ** exp` exponentiation, backed by the `pow$(base, exp)` function. Z3 has
                // no variable-exponent power primitive, so the value comes from pow's defining axioms (base
                // `pow(b,0)==1`, step `pow(b,k)==b*pow(b,k-1)` for k>=1; Phase 93b, minted once by `powOf`).
                // Those unfold a literal exponent to a value (`2 ** 3` → 8) and prove the doubling recurrence
                // `2 ** (n+1) == 2 * (2 ** n)`; symbolic-exponent value facts stay "could not decide" — they
                // need induction the finite e-matching can't reach. Groovy's `**` returns Number, so the int
                // surface is `(base ** exp).intValue()` (translateMethodCall's intValue handler).
                return powOf(L, R)
            case Types.COMPARE_EQUAL:       return session.eq(L, R)
            case Types.COMPARE_NOT_EQUAL:   return session.ne(L, R)
            case Types.COMPARE_LESS_THAN:           return session.lt(L, R)
            case Types.COMPARE_LESS_THAN_EQUAL:     return session.le(L, R)
            case Types.COMPARE_GREATER_THAN:        return session.gt(L, R)
            case Types.COMPARE_GREATER_THAN_EQUAL:  return session.ge(L, R)
            case Types.COMPARE_TO:
                // Groovy's spaceship `a <=> b` (compareTo): the three-way sign. For Int operands it is
                // exactly -1 / 0 / 1 (Integer.compareTo), modelled as nested `ite`. A non-Int receiver
                // (e.g. String, whose `<=>` is lexicographic and arbitrary-valued) would need Z3 string
                // ordering, so it skips honestly rather than mis-applying int comparison.
                if (isStringReceiver(be.leftExpression) || isStringReceiver(be.rightExpression)) return null
                return session.ite(session.lt(L, R), session.intLit(-1L),
                           session.ite(session.eq(L, R), session.intLit(0L), session.intLit(1L)))
            case Types.LOGICAL_AND: {       // operands may be non-Boolean (Groovy truth): `xs && i > 0`
                Object lb = truthy(be.leftExpression, L), rb = truthy(be.rightExpression, R)
                return (lb == null || rb == null) ? null : session.and([lb, rb])
            }
            case Types.LOGICAL_OR: {
                Object lb = truthy(be.leftExpression, L), rb = truthy(be.rightExpression, R)
                return (lb == null || rb == null) ? null : session.or([lb, rb])
            }
            default:                        return null
        }
    }

    /**
     * Groovy's truncate-toward-zero integer division ({@code a.intdiv(b)} / {@code (int)(a / b)}).
     * Derived from the (sign-of-dividend) remainder: {@code (a - rem) / b} divides exactly, so the
     * Euclidean {@code intDiv} and truncation agree on it — and the identity
     * {@code intdiv(a,b)*b + a.remainder(b) == a} holds by construction.
     */
    private Object truncDiv(Object a, Object b) {
        session.intDiv(session.minus(a, session.intRem(a, b)), b)
    }

    /**
     * Bitwise / shift operators on Int operands: {@code & | ^ << >>}. Returns the handle, or null if
     * {@code op} isn't a bitwise op or the operands aren't Int (e.g. a set {@code a & b} reaching here —
     * the term-build throws on the sort mismatch and we skip loudly).
     *
     * <p><b>Shifts by a non-negative literal</b> stay in unbounded Int arithmetic — {@code x << k} is
     * {@code x * 2^k} and {@code x >> k} is {@code ⌊x / 2^k⌋} (Z3's flooring {@code intDiv}, so an
     * arithmetic right shift is faithful for negatives too). This matches how {@code *} / {@code intdiv}
     * are modelled (unbounded Int by default) and keeps the common power-of-two idioms quantifier-free.
     * <b>Bitwise {@code & | ^} and variable shifts</b> have no such arithmetic form, so they go through
     * Z3's <b>bit-vector theory at Java's 32-bit width</b> ({@link SmtBackend#bvAnd} et al.) — faithful
     * two's-complement semantics, bit-blasted (and so timeout-gated like the FP fragment).
     */
    private Object translateBitwise(int op, BinaryExpression be, Object L, Object R) {
        boolean shl = (op == Types.LEFT_SHIFT)
        boolean shr = (op == Types.RIGHT_SHIFT)
        boolean ushr = (op == Types.RIGHT_SHIFT_UNSIGNED)
        if (op != Types.BITWISE_AND && op != Types.BITWISE_OR && op != Types.BITWISE_XOR && !shl && !shr && !ushr) {
            return null
        }
        try {
            // `>>>` is the logical (zero-fill) shift: its result depends on the full 32-bit sign pattern, so unlike
            // `<<`/`>>` it has no unbounded-Int form even for a literal count — it always goes through the bit-vector.
            if (ushr) return session.bvLShr(L, R)
            if (shl || shr) {
                Long k = nonNegIntLiteral(be.rightExpression)
                if (k != null && k <= 31) {
                    Object pow = session.intLit(1L << k)
                    return shl ? session.times(L, pow) : session.intDiv(L, pow)
                }
                return shl ? session.bvShl(L, R) : session.bvShr(L, R)
            }
            if (op == Types.BITWISE_AND) {
                // Phase 103 — a low-bit mask `x & (2^k - 1)` keeps exactly the low k bits, which *is* the
                // Euclidean mod `x mod 2^k` for every x (two's-complement, negative, even unbounded — since
                // 2^k | 2^32). Model it arithmetically rather than as a bit-vector so it stays in LIA and
                // bridges to `%` / `+` / divisibility: the OpenJML round-up `n + ((-n) & 0x0f)` then proves
                // `result % 16 == 0` (a bit-vector `&` times out there). The non-mask operand is `x`; a
                // non-low-bit-mask `&` (e.g. `x & 0x0a`) keeps the faithful bit-vector path.
                Long maskR = nonNegIntLiteral(be.rightExpression)
                if (maskR != null && isLowBitMask(maskR)) return session.intMod(L, session.intLit(maskR + 1L))
                Long maskL = nonNegIntLiteral(be.leftExpression)
                if (maskL != null && isLowBitMask(maskL)) return session.intMod(R, session.intLit(maskL + 1L))
                return session.bvAnd(L, R)
            }
            switch (op) {
                case Types.BITWISE_OR:  return session.bvOr(L, R)
                case Types.BITWISE_XOR: return session.bvXor(L, R)
            }
            return null
        } catch (Exception ignored) {
            return null   // non-Int operands → loud skip
        }
    }

    /** Phase 103 — true if {@code m} is a low-bit mask {@code 2^k - 1} ({@code m+1} is a power of two), so
     *  {@code x & m} keeps the low k bits — exactly {@code x mod (m+1)}. ({@code m == 0} ⇒ {@code mod 1 == 0}.) */
    private static boolean isLowBitMask(long m) {
        m >= 0 && (m & (m + 1L)) == 0
    }

    /** The value of {@code e} if it is a non-negative integer literal, else null. */
    private static Long nonNegIntLiteral(Expression e) {
        if (!(e instanceof ConstantExpression)) return null
        Object v = ((ConstantExpression) e).value
        if (v instanceof Integer || v instanceof Long) {
            long n = ((Number) v).longValue()
            return n >= 0 ? (Long) n : null
        }
        return null
    }

    /** True if {@code t} is an integral (int/long/short/byte or their wrappers) cast target. */
    private static boolean isIntegralCastType(ClassNode t) {
        if (t == null) return false
        switch (t.nameWithoutPackage) {
            case 'int': case 'Integer':
            case 'long': case 'Long':
            case 'short': case 'Short':
            case 'byte': case 'Byte':
                return true
            default: return false
        }
    }

    private static boolean isCharCastType(ClassNode t) {
        t != null && (t.nameWithoutPackage == 'char' || t.nameWithoutPackage == 'Character')
    }

    /** Phase 102 — the single {@code SwitchStatement} forming a no-parameter closure's whole body, i.e. the
     *  switch-expression desugaring {@code { -> switch(...){...} }.call()}; else null. */
    private static SwitchStatement soleSwitchOf(ClosureExpression cl) {
        if (cl.parameters != null && cl.parameters.length > 0) return null
        if (!(cl.code instanceof BlockStatement)) return null
        List<Statement> stmts = ((BlockStatement) cl.code).statements
        (stmts.size() == 1 && stmts.get(0) instanceof SwitchStatement) ? (SwitchStatement) stmts.get(0) : null
    }

    /** The yielded value expression of a switch case/default body — a lone {@code return e} / {@code e}
     *  (possibly block-wrapped), else null (a multi-statement / complex body is out of fragment). */
    private static Expression caseValueExpr(Statement code) {
        Statement st = code
        if (st instanceof BlockStatement) {
            List<Statement> ss = ((BlockStatement) st).statements
            if (ss.size() != 1) return null
            st = ss.get(0)
        }
        if (st instanceof ReturnStatement) return ((ReturnStatement) st).expression
        if (st instanceof ExpressionStatement) return ((ExpressionStatement) st).expression
        null
    }

    /**
     * Phase 102 — lower a switch EXPRESSION with *simple literal* case labels to an ite-chain
     * {@code ite(subj==l1, v1, ite(subj==l2, v2, … ite(subj==lN, vN, UNMATCHED)))}. The subject compares in its
     * own sort (int or String); the branch values share a result sort (int or String). UNMATCHED is the
     * {@code default ->} value, or — with no default — a fresh unconstrained term of the result sort: Groovy
     * yields {@code null} on no-match, so requiring it to satisfy a non-trivial postcondition is a sound
     * conservative refute, while a precondition that covers every case makes the branch dead and lets the proof
     * through. Skips (null) on a non-literal label, a complex case body, or a sort it can't model.
     */
    private Object translateSwitchExpr(SwitchStatement sw) {
        List<CaseStatement> cases = sw.caseStatements
        if (cases == null || cases.isEmpty()) return null
        Object subjH = translate(sw.expression)
        if (subjH == null) return null
        boolean stringSubj = isStringReceiver(sw.expression)
        if (!stringSubj && session.isReal(subjH)) return null     // decimal subject not modelled
        Object strSort = session.declareSort('String')
        Expression firstVal = caseValueExpr(cases.get(0).code)
        if (firstVal == null) return null
        boolean stringResult = isStringReceiver(firstVal)
        Expression defExpr = (sw.defaultStatement == null || sw.defaultStatement instanceof EmptyStatement)
                             ? null : caseValueExpr(sw.defaultStatement)
        try {
            Object acc
            if (defExpr != null) {
                acc = translate(defExpr); if (acc == null) return null
            } else {
                acc = stringResult ? session.varOfSort('switch$def' + (quantCounter++), strSort)
                                   : session.intVar('switch$def' + (quantCounter++))
            }
            for (int k = cases.size() - 1; k >= 0; k--) {
                CaseStatement c = cases.get(k)
                if (!(c.expression instanceof ConstantExpression)) return null
                Expression val = caseValueExpr(c.code)
                if (val == null) return null
                Object cond = stringSubj
                    ? session.eq(translateInSort(sw.expression, strSort), translateInSort(c.expression, strSort))
                    : session.eq(subjH, translate(c.expression))
                Object valH = translate(val)
                if (cond == null || valH == null) return null
                acc = session.ite(cond, valH, acc)
            }
            return acc
        } catch (Exception ignored) {
            return null     // sort mismatch among branches, etc. → loud skip
        }
    }

    /** Phase 116 — if {@code name(args)} is a registered equational combiner, translate {@code E[formals:=args]}
     *  (the {@code @Ensures} right-hand side with formals bound to the actual argument terms); else null. */
    private Object inlineCombiner(String name, List<Expression> args) {
        Object[] c = combiners.get(name + '/' + args.size())
        if (c == null) return null
        List<String> formals = (List<String>) c[0]
        Expression ensuresExpr = (Expression) c[1]
        Map<String, Object> bindings = new LinkedHashMap<String, Object>()
        for (int i = 0; i < formals.size(); i++) {
            Object h = translate(args.get(i))
            if (h == null) return null
            bindings.put(formals.get(i), h)
        }
        translateWith(ensuresExpr, bindings)
    }

    private Object translateMethodCall(MethodCallExpression mce) {
        String m = mce.methodAsString
        if (m == null) return null
        // Phase 102 — a switch EXPRESSION desugars to `{ -> <SwitchStatement> }.call()` (an IIFE closure).
        // Recognise that shape and lower the switch to an ite-chain, before the closure receiver is otherwise
        // translated. (Switch expressions only; switch statements stay an unsupported-statement skip.)
        if (m == 'call' && argList(mce).isEmpty() && mce.objectExpression instanceof ClosureExpression) {
            SwitchStatement sw = soleSwitchOf((ClosureExpression) mce.objectExpression)
            if (sw != null) {
                Object q = translateSwitchExpr(sw)
                if (q != null) return q
            }
        }
        // Phase 38c — strip a transparent immutability wrapper on the receiver so subsequent
        // dispatch sees the inner expression directly. Idempotent for non-wrapper receivers.
        Expression recv = unwrapImmutableWrap(mce.objectExpression)
        List<Expression> args = argList(mce)

        // Phase 132 — JSR 385 value/scale (C₁): a Quantity's `getValue()` read *in a named unit* is its
        // SI magnitude divided by that unit's scale. The magnitude is recovered structurally from the
        // construction (`getQuantity`/`to`/`add`/…), so only quantities *built in scope from known units* are
        // modelled — a Quantity parameter's magnitude/unit is unknown and skips. Exact LRA over rational scales.
        if (m == 'getValue' && args.isEmpty()) {
            Object v = quantityValueTerm(recv)
            if (v != null) return v
        }

        // Phase M-C — `some(v)` / `none()` factory call of a two-case carrier → the datatype constructor.
        Object[] fac = carrierFactoryMatch(m, args.size())
        if (fac != null) {
            ClassNode cn = (ClassNode) fac[0]
            String ctor = (String) fac[1]
            sortFor(cn)   // ensure the datatype is declared
            if (ctor == 'None') return session.datatypeConstruct(cn.nameWithoutPackage, 'None', [])
            Object val = translateInSort(args.get(0), contentSortFor((FieldNode) fac[2]))
            if (val != null) return session.datatypeConstruct(cn.nameWithoutPackage, 'Some', [val])
        }

        // Phase A (higher-order) — `f.apply(x)` on a stable named reference (a parameter/field/local `f`):
        // model `f` as an uninterpreted function over an uninterpreted value sort. We know nothing about what
        // `f` computes, only that it is a function (equal arguments → equal results), which is exactly an
        // uninterpreted-function symbol. This is the foundation for higher-order contract reasoning — notably
        // the @Monadic monad laws, which quantify over arbitrary `Function`s. Restricted to a VariableExpression
        // receiver so the UF key (`apply$<name>`) denotes a stable function; a computed receiver stays unmodelled.
        if (m == 'apply' && args.size() == 1 && recv instanceof VariableExpression) {
            Object vSort = session.declareSort('Object')
            String rn = ((VariableExpression) recv).name
            Object range = functionRange(rn, vSort)              // Phase C — a bind function returns the carrier
            Object arg = translateInSort(args.get(0), vSort)
            if (arg != null) return session.applyUF('apply$' + rn, [arg], range)
        }

        // Phase C — `m.bind(f)` / `m.map(p)` on a recognised wrapper carrier whose bind/map *bodies* are the
        // Identity-wrapper shape (verified, not assumed): model them by their definitions, so the monad/functor
        // laws compose with f.apply (Phase A) and the carrier datatype (Phase B).
        //   bind:  m.bind(f) == f.apply(content(m))            (f: value → carrier)
        //   map:   m.map(p)  == unit(p.apply(content(m)))      (p: value → value)
        if (args.size() == 1) {
            ClassNode ct = carrierTypeOf(recv)
            FieldNode cf = ct != null ? wrapperContentField(ct) : null
            if (cf != null) {
                Object cSort = contentSortFor(cf)
                Object recvH = (m == bindMethodName(ct) || m == mapMethodName(ct)) ? translate(recv) : null
                if (recvH != null && m == bindMethodName(ct) && isIdentityBind(ct, m, cf)) {
                    // m.bind(f) == f.apply(content(m)) ; f returns the carrier.
                    Object content = session.wrapperContent(ct.nameWithoutPackage, cSort, recvH)
                    Object r = applyFunction(args.get(0), content, sortFor(ct))
                    if (r != null) return r
                }
                if (recvH != null && m == mapMethodName(ct) && isIdentityMap(ct, m, cf)) {
                    // m.map(p) == unit(p.apply(content(m))) ; p returns a value.
                    Object content = session.wrapperContent(ct.nameWithoutPackage, cSort, recvH)
                    Object mapped = applyFunction(args.get(0), content, cSort)
                    if (mapped != null) return session.wrapperUnit(ct.nameWithoutPackage, cSort, mapped)
                }
            }
            // Phase M-D — a two-case carrier's case-split bind/map: `ite(is$Some(m), someCase, m)`. bind is the
            // same for any lawful Maybe; map's some-case is the discriminator — Vavr wraps in Some, Optional
            // collapses a null result to None (which is where its functor law breaks).
            Object[] mc = ct != null ? multiCaseInfo(ct) : null
            if (mc != null && isCanonicalWiring(ct, mc) && (m == bindMethodName(ct) || m == mapMethodName(ct))) {
                Object recvH = translate(recv)
                if (recvH != null) {
                    String tn = ct.nameWithoutPackage
                    FieldNode cfld = (FieldNode) mc[2]
                    Object cSort = contentSortFor(cfld)
                    sortFor(ct)   // ensure datatype declared
                    Object isSome = session.datatypeRecognize(tn, 'Some', recvH)
                    Object content = session.datatypeSelect(tn, 'Some', cfld.name, recvH)
                    if (m == bindMethodName(ct) && isMultiCaseBind(ct, m, mc)) {
                        Object someCase = applyFunction(args.get(0), content, sortFor(ct))   // f.apply(content): carrier
                        if (someCase != null) return session.ite(isSome, someCase, recvH)
                    }
                    if (m == mapMethodName(ct)) {
                        String kind = multiCaseMapKind(ct, m, mc)
                        Object mapped = kind != null ? applyFunction(args.get(0), content, cSort) : null   // g.apply(content): value
                        if (mapped != null) {
                            Object someV = session.datatypeConstruct(tn, 'Some', [mapped])
                            Object someCase = (kind == 'vavr') ? someV :
                                session.ite(session.eq(mapped, session.nullValue(cSort)),
                                            session.datatypeConstruct(tn, 'None', []), someV)
                            return session.ite(isSome, someCase, recvH)
                        }
                    }
                }
            }
        }

        // Phase 116 — equational combiner inlining: a call to a registered combiner `f(args)` (no `@Requires`,
        // `@Ensures({ result == E })`) is translated as `E[formals := args]`, so a reduction `acc = f(acc, x)`
        // matches the inline aggregation/extremum patterns instead of havocking `acc`. Sound — see {@link #combiners}.
        Object combined = inlineCombiner(m, args)
        if (combined != null) return combined

        // Phase 93 — `.intValue()` / `.longValue()` on an integral value is identity in the math-int model.
        // The motivating case is exponentiation: Groovy's `**` returns Number, so `(base ** exp).intValue()`
        // is how a power reaches an int context; translating the receiver yields the `pow$` term directly.
        // (Phase 95 attempt: modelling the 32-bit *wrap* here — `(2**31).intValue() == Integer.MIN_VALUE` —
        // is unsound to do at the leaf alone. The surrounding int arithmetic stays math-int, so a wrapped
        // leaf inside `2 * (2 ** n).intValue()` is inconsistent: the runtime wraps the `2 *` too, but the
        // model doesn't, breaking a runtime-true equality. Faithful narrowing needs a fully width-aware
        // arithmetic model, not a leaf truncation — tracked as a non-goal of this slice.)
        if ((m == 'intValue' || m == 'longValue') && args.isEmpty()) {
            Object r = translate(recv)
            if (r != null) return r
        }

        // Phase 89 — `a.is(b)` reference identity (the method form of `a === b`): identity equality
        // when both receiver and argument are object-parameter references.
        if (m == 'is' && args.size() == 1) {
            Object idEq = refIdentityEq(recv, args.get(0))
            if (idEq != null) return idEq
        }

        // Phase 80 — t.size() / t.getVN() / t.second() on a tuple parameter. `.size()` → arity (a literal);
        // the slot accessors mint the k-th slot's typed entity. (Constructed/returned tuples fold via the
        // factory container instead — that path is checked downstream.)
        if (recv instanceof VariableExpression && tupleParams.containsKey(((VariableExpression) recv).name)) {
            String tn = ((VariableExpression) recv).name
            if (m == 'size' && args.isEmpty()) return session.intLit((long) tupleArity(tupleParams.get(tn)))
            if (args.isEmpty()) {
                Object te = tupleSlotEntity(tn, tupleSlotIndex(m))
                if (te != null) return te
            }
        }

        // Phase 73 — Double.isNaN(x) / isInfinite(x) / isFinite(x) over an FP argument → IEEE predicates.
        if ((m == 'isNaN' || m == 'isInfinite' || m == 'isFinite') && args.size() == 1 &&
            isFpClassReceiver(recv) && isFpValued(args.get(0))) {
            Object x = asFp(args.get(0))
            if (x == null) return null
            if (m == 'isNaN') return session.fpIsNaN(x)
            if (m == 'isInfinite') return session.fpIsInfinite(x)
            return session.and([session.not(session.fpIsNaN(x)), session.not(session.fpIsInfinite(x))])  // isFinite
        }

        // Forall.range(lo, hi, { i -> body }) -> bounded universal quantifier.
        // Accept both the imported `Forall` (a VariableExpression) and the
        // fully-qualified `verification.Forall` (a PropertyExpression) — the
        // latter is needed inside @Invariant, where groovy-contracts' loop
        // transform doesn't carry the import.
        boolean isForall = (recv instanceof VariableExpression && ((VariableExpression) recv).name == 'Forall') ||
                           (recv instanceof PropertyExpression && ((PropertyExpression) recv).propertyAsString == 'Forall')
        if (m == 'range' && isForall &&
            args.size() == 3 && args.get(2) instanceof ClosureExpression) {
            return translateForallRange(args.get(0), args.get(1), (ClosureExpression) args.get(2))
        }

        // Sorted.ascending(a) / descending / strictlyAscending / strictlyDescending — the canonical
        // sortedness precondition, emitted as a FLAT 2-D axiom ∀ j,k. 0<=j<k<n ⟹ a[j] R a[k] with an
        // explicit multi-pattern trigger {a[j], a[k]} (see Sorted / forallMultiPattern). Reaches us the
        // three usual ways (bare import, FQN in a re-parsed @Invariant, resolved ClassExpression in a body).
        boolean isSortedClass = (recv instanceof VariableExpression && ((VariableExpression) recv).name == 'Sorted') ||
                                (recv instanceof PropertyExpression && ((PropertyExpression) recv).propertyAsString == 'Sorted') ||
                                (recv instanceof ClassExpression && ((ClassExpression) recv).type?.nameWithoutPackage == 'Sorted')
        if (isSortedClass && args.size() == 1) {
            Object q = translateSorted(m, args.get(0))
            if (q != null) return q
        }
        // Native idiom: `a.isSorted()` (Groovy 6 GDK on List/object-arrays plus the native int[]/long[]
        // overloads) — the receiver IS the array, ascending with ties (GDK semantics). The
        // property form `a.sorted` (the boolean getter) is handled in translate(PropertyExpression).
        if (m == 'isSorted' && args.isEmpty()) {
            Object q = translateSorted('ascending', recv)
            if (q != null) return q
        }

        // Phase 74 — Range.containsWithinBounds(v): Groovy's *bounds-only* range membership (it ignores
        // the step — that is exactly what separates it from `contains`). Lowers to the inclusive interval
        // predicate min(lo,hi) <= v <= max(lo,hi) in v's sort — exact, symbolic, no enumeration.
        // Recognises a `lo..hi` literal and a `new NumberRange(lo,hi,step)` / `new IntRange(lo,hi)`
        // constructor. Numeric bounds only; a character/String range skips loudly.
        if (m == 'containsWithinBounds' && args.size() == 1) {
            Object q = translateContainsWithinBounds(recv, args.get(0))
            if (q != null) return q
        }

        // Phase 99 — `(lo..hi).contains(i)` for an integer range: step-1 integer membership is exactly the
        // bounds (the `i in lo..hi` operator lowers identically, in translateBinary).
        if (m == 'contains' && args.size() == 1) {
            Object q = translateIntRangeContains(recv, args.get(0))
            if (q == null) q = translateStringRangeContains(recv, args.get(0))
            if (q != null) return q
        }

        // Sets.boundedBy(s, n) — the cardinality axiom (Phase 19): a set bounded by the domain [0, n).
        // Lowered to card(s) <= n ∧ (card(s) < n ∨ ∀ i ∈ [0,n)· i ∈ s), a faithful boolean definition.
        // `Sets` reaches us three ways: a bare import (VariableExpression) and FQN `verification.Sets`
        // (PropertyExpression) in re-parsed contracts, and a resolved ClassExpression when it appears in a
        // method *body* (e.g. a loop guard `Sets.boundedCount(...) < n`).
        // Phase 47e — static-class string/int conversions. Receiver reaches as one of three
        // shapes depending on whether the source is type-resolved: VariableExpression for
        // unresolved imports, PropertyExpression for FQN paths, ClassExpression after the
        // type checker has bound the class. Detect by simple name across all three.
        boolean isInteger = (recv instanceof VariableExpression && ((VariableExpression) recv).name == 'Integer') ||
                            (recv instanceof PropertyExpression && ((PropertyExpression) recv).propertyAsString == 'Integer') ||
                            (recv instanceof ClassExpression && ((ClassExpression) recv).type?.nameWithoutPackage == 'Integer')
        boolean isStringClass = (recv instanceof VariableExpression && ((VariableExpression) recv).name == 'String') ||
                                (recv instanceof PropertyExpression && ((PropertyExpression) recv).propertyAsString == 'String') ||
                                (recv instanceof ClassExpression && ((ClassExpression) recv).type?.nameWithoutPackage == 'String')
        if (isInteger && m == 'toString' && args.size() == 1) {
            Object n = translate(args.get(0))
            return n == null ? null : session.stringFromInt(n)
        }
        if (isInteger && m == 'parseInt' && args.size() == 1) {
            Object s = translateInSort(args.get(0), session.declareSort('String'))
            return s == null ? null : session.parseIntFromString(s)
        }
        if (isStringClass && m == 'valueOf' && args.size() == 1) {
            // Only the Int overload is modeled; String.valueOf on other types returns null
            // (honest skip — the caller's site is outside fragment).
            Object n = translate(args.get(0))
            return n == null ? null : session.stringFromInt(n)
        }
        // Phase 124 — instance form `x.toString()` on an integral value (the idiomatic Groovy default-branch
        // spelling). Mirrors `String.valueOf` / `Integer.toString`: convert the Int-sorted receiver via the
        // same Z3 intToString. Gated on the receiver being a String-free Int term so a non-int `.toString()`
        // stays an honest skip rather than a sort crash.
        if (m == 'toString' && args.isEmpty() && !isStringReceiver(recv)) {
            Object h = translate(recv)
            if (h != null && session.isInt(h)) return session.stringFromInt(h)
        }

        // Groovy's integer-division / modulo *method* forms (the `/` and `%` operators are handled in
        // translateBinary). Receiver and divisor are integer expressions; translate() yields a non-null
        // Int handle only for the integral types the fragment models (else honest skip).
        //   a.intdiv(b)    — integer division, truncate toward zero
        //   a.remainder(b) — remainder, sign of dividend (same as the `%` operator)
        //   a.mod(b)       — BigInteger.mod: non-negative result (the b > 0 obligation is added in
        //                    the ObligationCollector, matching Groovy's "modulus not positive" throw)
        if (args.size() == 1 && (m == 'intdiv' || m == 'remainder' || m == 'mod')) {
            Object a = translate(recv)
            Object b = translate(args.get(0))
            if (a == null || b == null) return null
            if (m == 'remainder') return session.intRem(a, b)
            if (m == 'mod')       return session.intMod(a, b)
            return truncDiv(a, b)   // intdiv
        }

        // Groovy's `a.implies(b)` (DGM `Boolean.implies` = `!a || b`) — the method twin of the `==>`
        // operator (translateBinary). Both reduce to the backend's `implies`.
        if (m == 'implies' && args.size() == 1) {
            Object a = translate(recv)
            Object b = translate(args.get(0))
            return (a == null || b == null) ? null : session.implies(a, b)
        }

        // Numeric sum/product aggregation over an *Int* list/array — the Groovy-idiomatic spellings:
        //   xs[lo..<hi].sum() / xs.sum() / xs.sum(init)        → init + sum$(arr,lo,hi)   (sum)
        //   xs.inject(1){ a,x -> a*x } / xs[lo..<hi].inject…   → init * prod$(arr,lo,hi)  (product fold)
        //   xs.inject(0){ a,x -> a+x }                         → init + sum$(arr,lo,hi)   (sum fold)
        // Lowered to the `sum$`/`prod$` primitives + their base/step axioms (see sumOf/prodOf).
        // Gated to Int-element lists: `sum()` is duck-typed (`['a','b'].sum() == 'ab'`) and the
        // primitives are Int-sorted, so a non-Int element list honestly skips (no Z3 sort mismatch).
        // Empty: Groovy's `[].sum()` is *null*; the `sum(init)`/`inject(init)` forms return `init`.
        if (m == 'sum' && (args.isEmpty() || args.size() == 1)) {
            Object[] r = listAggHandles(recv)
            if (r == null) return null
            // old.xs.sum() keys the array as old$xs, but the element type lives under the live name xs.
            String aggName = (String) r[0]
            String elemKey = aggName.startsWith('old$') ? aggName.substring('old$'.length()) : aggName
            ClassNode et = listElementTypes.get(elemKey)
            if (et == null) {                          // Int list → numeric sum
                Object init = args.isEmpty() ? session.intLit(0L) : translate(args.get(0))
                if (init == null) return null
                Object base = sumOf(r[1], r[2], r[3])
                return args.isEmpty() ? base : session.plus(init, base)
            }
            if (isDecimalElementType(et)) {             // List<BigDecimal> → Real sum (Phase 70)
                Object init = args.isEmpty() ? session.realLit('0') : asReal(args.get(0))
                if (init == null) return null
                Object base = sumRealOf(r[1], r[2], r[3])
                return args.isEmpty() ? base : session.plus(init, base)
            }
            if (isStringElementType(et)) {              // String list → concatenation (`['a','b'].sum()`)
                Object strSort = session.declareSort('String')
                Object init = args.isEmpty() ? session.litOfSort(strSort, '') : translateInSort(args.get(0), strSort)
                if (init == null) return null
                Object base = strConcatOf(r[1], r[2], r[3])
                return args.isEmpty() ? base : session.stringConcat(init, base)
            }
            return null                                 // other element domain → honest skip
        }
        if (m == 'inject' && args.size() == 2 && args.get(1) instanceof ClosureExpression) {
            String op = foldClosureOp((ClosureExpression) args.get(1))   // '*' (product), '+' (sum), or null
            if (op != null) {
                Object[] r = listAggHandles(recv)
                // Int-element only: the * / + folds are numeric (string concat is `sum()`, handled above).
                if (r != null && listElementTypes.get((String) r[0]) == null) {
                    Object init = translate(args.get(0))
                    if (init != null) {
                        if (op == '*') return session.times(init, prodOf(r[1], r[2], r[3]))
                        if (op == '+') return session.plus(init, sumOf(r[1], r[2], r[3]))
                    }
                }
            }
        }

        // xs.max() / xs.min() over an Int *or* BigDecimal list/array — the witnessed-extremum spec a
        // Groovy developer writes as `result == a.max()` instead of spelling the every/any by hand.
        // Int contents (Phase 60) and Real contents (`List<BigDecimal>`, Phase 76) share the sort-generic
        // `maxMinOf`; other element domains (String/enum) skip honestly.
        if ((m == 'max' || m == 'min') && args.isEmpty()) {
            Object[] r = listAggHandles(recv)
            if (r == null) return null
            String aggName = (String) r[0]
            String elemKey = aggName.startsWith('old$') ? aggName.substring('old$'.length()) : aggName
            ClassNode et = listElementTypes.get(elemKey)
            if (et == null) {                              // Int list → Int extremum
                return maxMinOf(recv.text + '#' + m, r[1], r[2], r[3], m == 'max', session.intSort(), false)
            }
            if (isDecimalElementType(et)) {                // List<BigDecimal> → Real extremum
                return maxMinOf(recv.text + '#' + m, r[1], r[2], r[3], m == 'max', session.realSort(), false)
            }
            if (isFpElementType(et)) {                     // double[] / List<Double> → FP extremum (NaN-guarded)
                return maxMinOf(recv.text + '#' + m, r[1], r[2], r[3], m == 'max', sortFor(et), true)
            }
            return null                                    // String / enum element → skip
        }

        // Fib.of(i) — the Fibonacci spec helper (Phase 55), lowered to the axiomatised fib$ primitive.
        boolean isFib = (recv instanceof VariableExpression && ((VariableExpression) recv).name == 'Fib') ||
                        (recv instanceof PropertyExpression && ((PropertyExpression) recv).propertyAsString == 'Fib') ||
                        (recv instanceof ClassExpression && ((ClassExpression) recv).type?.nameWithoutPackage == 'Fib')
        if (m == 'of' && isFib && args.size() == 1) {
            Object k = translate(args.get(0))
            return k == null ? null : fibOf(k)
        }

        // Trib.of(i) — the tribonacci spec helper (HumanEval 063 fibfib), lowered to the trib$ primitive.
        boolean isTrib = (recv instanceof VariableExpression && ((VariableExpression) recv).name == 'Trib') ||
                         (recv instanceof PropertyExpression && ((PropertyExpression) recv).propertyAsString == 'Trib') ||
                         (recv instanceof ClassExpression && ((ClassExpression) recv).type?.nameWithoutPackage == 'Trib')
        if (m == 'of' && isTrib && args.size() == 1) {
            Object k = translate(args.get(0))
            return k == null ? null : tribOf(k)
        }

        // Tetra.of(i) — the fib4 / tetranacci spec helper (HumanEval 046 fib4), lowered to the tetra$ primitive.
        boolean isTetra = (recv instanceof VariableExpression && ((VariableExpression) recv).name == 'Tetra') ||
                          (recv instanceof PropertyExpression && ((PropertyExpression) recv).propertyAsString == 'Tetra') ||
                          (recv instanceof ClassExpression && ((ClassExpression) recv).type?.nameWithoutPackage == 'Tetra')
        if (m == 'of' && isTetra && args.size() == 1) {
            Object k = translate(args.get(0))
            return k == null ? null : tetraOf(k)
        }

        // Gcd.of(a, b) — the Euclid gcd spec helper (HumanEval 013), lowered to the gcd$ primitive.
        boolean isGcd = (recv instanceof VariableExpression && ((VariableExpression) recv).name == 'Gcd') ||
                        (recv instanceof PropertyExpression && ((PropertyExpression) recv).propertyAsString == 'Gcd') ||
                        (recv instanceof ClassExpression && ((ClassExpression) recv).type?.nameWithoutPackage == 'Gcd')
        if (m == 'of' && isGcd && args.size() == 2) {
            Object a = translate(args.get(0))
            Object b = translate(args.get(1))
            return (a == null || b == null) ? null : gcdOf(a, b)
        }

        // Lcm.of(a, b) — the least-common-multiple spec helper, lowered to the lcm$ primitive (built on gcd$).
        boolean isLcm = (recv instanceof VariableExpression && ((VariableExpression) recv).name == 'Lcm') ||
                        (recv instanceof PropertyExpression && ((PropertyExpression) recv).propertyAsString == 'Lcm') ||
                        (recv instanceof ClassExpression && ((ClassExpression) recv).type?.nameWithoutPackage == 'Lcm')
        if (m == 'of' && isLcm && args.size() == 2) {
            Object a = translate(args.get(0))
            Object b = translate(args.get(1))
            return (a == null || b == null) ? null : lcmOf(a, b)
        }

        boolean isSets = (recv instanceof VariableExpression && ((VariableExpression) recv).name == 'Sets') ||
                         (recv instanceof PropertyExpression && ((PropertyExpression) recv).propertyAsString == 'Sets') ||
                         (recv instanceof ClassExpression && ((ClassExpression) recv).type?.nameWithoutPackage == 'Sets')
        if (m == 'boundedBy' && isSets && args.size() == 2) {
            return translateSetsBounded(args.get(0), args.get(1))
        }
        // Sets.boundedCount(s, k) — the bounded-sum cardinality as a primitive (Phase 21), carrying
        // its bound axiom and (at set mutations) the per-add law. The recursive Phase-20 spelling
        // earns the same bound by induction; this form threads across a mutation. Distinct from
        // Groovy's GDK Collection.count(value) (which counts occurrences); the `bounded` prefix
        // marks the [0, k)-slice semantics.
        if (m == 'boundedCount' && isSets && args.size() == 2) {
            String key = setKeyFor(args.get(0))
            if (key == null) return null
            Object elemSort = setKeySortForKey(key)
            Object kH = translate(args.get(1))
            if (kH == null) return null
            if (elemSort == session.intSort()) {
                return setCountOf(setFor(key), kH)
            }
            // Phase 29 — enum-element set: when k equals the enum's domain size,
            // Sets.boundedCount(s, k) is morally the set's cardinality (no partial-domain "first k
            // constants" ordering exists). Alias to cardOf — the pigeonhole + full-coverage iff
            // were asserted at setFor time, so the user-visible identity
            // `Sets.boundedCount(s, N) == N ⟺ every enum constant ∈ s` follows by the iff.
            ClassNode enumType = elementTypeForSetKey(key)
            if (enumType != null && (enumType.isEnum() || isEnumLikeType(enumType))) {
                Long kLong = tryFoldToLong(args.get(1))
                int enumSize = enumConstantNames(enumType).size()
                if (kLong != null && kLong.longValue() == (long) enumSize) {
                    return cardOf(setFor(key))
                }
            }
            return null   // non-matching k or unsupported element sort — honest skip
        }

        // Native GDK quantifier idioms (Phase 9) — the universal a Groovy developer would
        // actually write, mapped to the same bounded `forall`. Only the recognised
        // range/indices/collection shapes become quantifiers; any other `every` returns
        // null and falls through to a loud "outside fragment" skip.
        if ((m == 'every' || m == 'any') && args.size() == 1 && args.get(0) instanceof ClosureExpression) {
            // Phase 75 — `iterate(seed, f).limit(n).every{ P }` over an infinite stream/iterator: a
            // property you cannot test (a true `every` over an unbounded source never returns), proved
            // by unrolling (literal limit) or by induction (unbounded). Tried before the collection forms.
            Object streamQ = translateStreamEvery(mce, recv, (ClosureExpression) args.get(0), m == 'any')
            if (streamQ != null) return streamQ
            Object q = translateBoundedQuantifier(recv, (ClosureExpression) args.get(0), m == 'any')
            if (q != null) return q
        }

        // Phase 28 — `Color.values().size()` (the method-form of `.length`) folds to the literal
        // enum-constant count, same as the property form above.
        if (m == 'size' && args.isEmpty()) {
            Integer cnt = enumValuesCountFor(recv)
            if (cnt != null) return session.intLit(cnt.longValue())
        }

        // Map receivers: m.get(k) / m[k] read the value array; containsKey/size/isEmpty go through the
        // key-set (a set, so size is its cardinality and the membership/law machinery is shared). The
        // key argument is translated in the map's key sort (Phase 27 — Int by default, String/Enum
        // when typed).
        String mapLog = mapLogicalFor(recv)
        if (mapLog != null) {
            ClassNode[] mapPair = mapTypes.get(mapLog)
            Object kSort = sortFor(mapPair != null ? mapPair[0] : null)
            if (m == 'get' && args.size() == 1) {
                Object k = translateInSort(args.get(0), kSort)
                return k == null ? null : session.select(mapValsFor(mapLog), k)
            }
            if (m == 'containsKey' && args.size() == 1) {
                Object k = translateInSort(args.get(0), kSort)
                return k == null ? null : member(mapKeysFor(mapLog), k)
            }
            if (m == 'size' && args.isEmpty()) return cardOf(mapKeysFor(mapLog))
            if (m == 'isEmpty' && args.isEmpty()) return session.eq(cardOf(mapKeysFor(mapLog)), session.intLit(0L))
            // Phase 32a — m.containsValue(v) for enum-keyed maps: lower to the finite disjunction
            // (m[c_1] == v) ∨ … ∨ (m[c_N] == v) over the enum's key constants. The bounded
            // existential mirror of the Phase-30 finite-conjunction subset lowering. Int-keyed
            // and String-keyed maps skip (no finite key-domain to enumerate).
            if (m == 'containsValue' && args.size() == 1) {
                Object q = translateMapContainsValue(mapLog, args.get(0))
                if (q != null) return q
            }
            // Phase 39 — m.getOrDefault(k, d): the canonical defensive-read idiom. Lowers to
            // {@code ite(containsKey(k), m[k], d)}, with the default translated in the map's
            // value sort so types compose cleanly.
            if (m == 'getOrDefault' && args.size() == 2) {
                Object k = translateInSort(args.get(0), kSort)
                Object vSort = mapValueSort(mapLog)
                Object d = translateInSort(args.get(1), vSort)
                if (k == null || d == null) return null
                Object present = member(mapKeysFor(mapLog), k)
                Object value = session.select(mapValsFor(mapLog), k)
                return session.ite(present, value, d)
            }
            // keySet/values/putAll/etc. still need unbounded quantifiers or new theory —
            // out of fragment: null so it surfaces as a loud "skipped", never a silent pass.
            return null
        }

        // Set receivers (s.contains(x) / s.size() / s.isEmpty()) take precedence over the list/array
        // oracles below: a set is a characteristic array, its size is the uninterpreted cardinality.
        // The element is translated in the set's element sort (Phase 27).
        String setKey = setKeyFor(recv)
        if (setKey != null) {
            Object elemSort = setKeySortForKey(setKey)
            if (m == 'contains' && args.size() == 1) {
                Object e = translateInSort(args.get(0), elemSort)
                return e == null ? null : member(setFor(setKey), e)
            }
            if (m == 'size' && args.isEmpty()) return cardOf(setFor(setKey))
            if (m == 'isEmpty' && args.isEmpty()) return session.eq(cardOf(setFor(setKey)), session.intLit(0L))
            // Phase 30 — s.containsAll(t) for enum-element sets, lowered to the finite conjunction
            // ∧ (c_i ∈ t ⟹ c_i ∈ s) over the enum's constants (the same shape Phase 29 uses for
            // full-coverage). Phase 31 — Int subset under a Sets.boundedBy(t, n) context, lowered
            // to a bounded universal over [0, n).
            if (m == 'containsAll' && args.size() == 1) {
                Object q = translateContainsAll(setKey, args.get(0))
                if (q != null) return q
            }
            // Phase 32b — s.equals(t) ≡ s.containsAll(t) ∧ t.containsAll(s), composed from the
            // subset lowering above. Verifies for any element sort the subset path handles (enum
            // always; Int with mutual bounds); otherwise the conjunction has a null operand and
            // the whole thing skips honestly.
            if (m == 'equals' && args.size() == 1) {
                Object q = translateSetEquals(setKey, args.get(0))
                if (q != null) return q
            }
            return null
        }

        // Phase 38 — factory receiver (List.of / Set.of / Map.of / Groovy literals): peephole-fold
        // .size / .isEmpty / .contains / .containsKey / .containsValue / .get to ground SMT terms
        // when the receiver is a recognised immutable-container literal. Composes with other
        // dispatch paths cleanly — no named handle minted, no axioms emitted.
        FactoryContainer factory = factoryContainerFor(recv)
        if (factory != null) {
            Object q = foldFactoryMethodCall(factory, m, args)
            if (q != null) return q
            // Not a recognised op on this kind — fall through to honest skip rather than masking.
            return null
        }

        // Phase 36 — `m[k].contains(x)` / `m[k].containsAll(s)` on a Map<K, Set<V>>: lower through
        // the inner set as a transient SMT array term, never minted as a named handle. .size() and
        // mutations on the inner set are out of scope (would need to mint a handle and update law).
        NestedSetReceiver nr = nestedSetReceiverFor(recv)
        if (nr != null) {
            if (m == 'contains' && args.size() == 1) {
                Object e = translateInSort(args.get(0), nr.innerElemSort)
                return e == null ? null : member(nr.innerSet, e)
            }
            if (m == 'containsAll' && args.size() == 1) {
                Object q = translateNestedContainsAll(nr, args.get(0))
                if (q != null) return q
            }
            return null
        }

        // Phase 33 — inline set union / intersection on the receiver side: (s + t).contains(x)
        // and s.intersect(t).contains(x) lower lazily without minting a new set handle. The
        // operands must both be known sets with matching element sort; otherwise skip.
        SetBinop binop = setBinopFor(recv)
        if (binop != null) {
            if (m == 'contains' && args.size() == 1) {
                Object e = translateInSort(args.get(0), binop.elemSort)
                if (e == null) return null
                Object lMem = member(setFor(binop.leftKey), e)
                Object rMem = member(setFor(binop.rightKey), e)
                return setCombineMembership(binop.kind, lMem, rMem)
            }
            if (m == 'containsAll' && args.size() == 1) {
                Object q = translateContainsAllOnBinop(binop, args.get(0))
                if (q != null) return q
            }
            // .size() on a binop needs inclusion-exclusion (out of scope); other ops skip too.
            return null
        }

        // xs.count(v) / old.a.count(v) -> the occurrence-count term. Lists route through bcount
        // bounded by [0, sizeOf) (Phase 41 — faithful to Groovy's GDK list count semantics under
        // size-changing mutations); arrays keep the unbounded count (Phase 12, permutation — fixed
        // size, no semantic mismatch). The receiver-name lookup tolerates both bare {@code xs} and
        // {@code old.xs} via {@link #isListName} stripping the {@code old$} prefix.
        if (m == 'count' && args.size() == 1 && !(args.get(0) instanceof ClosureExpression)) {
            Object arr = arrayHandleFor(recv)
            if (arr != null) {
                Object v = translate(args.get(0))
                if (v == null) return null
                String rname = receiverArrayName(recv)
                if (rname != null && isListName(rname)) {
                    return session.bcount(arr, v, session.intLit(0L), sizeOf(rname))
                }
                return session.count(arr, v)
            }
        }

        // Phase 46a — String-typed receivers route to the string-predicate translations
        // (startsWith/endsWith/contains/isEmpty) before the list-style named-receiver dispatch
        // below: the latter would mistakenly interpret {@code s.contains(p)} on a String as a
        // bounded existential over array indices.
        if (isStringReceiver(recv)) {
            Object strSort = session.declareSort('String')
            Object sH = translateInSort(recv, strSort)
            if (sH == null) return null
            // Phase 46b — {@code s.length()} and its GDK alias {@code s.size()} route to the
            // length oracle. {@code s.isEmpty()} lowers to {@code length(s) == 0} — replacing
            // the Phase-46a uninterpreted predicate with a length-coupled one, so
            // {@code s.isEmpty()} and {@code s.length() == 0} stay equivalent for the solver.
            if ((m == 'length' || m == 'size') && args.isEmpty()) return session.stringLength(sH)
            if (m == 'isEmpty' && args.isEmpty()) {
                return session.eq(session.stringLength(sH), session.intLit(0L))
            }
            if (args.size() == 1 && (m == 'startsWith' || m == 'endsWith' || m == 'contains')) {
                Object pH = translateInSort(args.get(0), strSort)
                if (pH == null) return null
                if (m == 'startsWith') return session.stringStartsWith(sH, pH)
                if (m == 'endsWith')   return session.stringEndsWith(sH, pH)
                if (m == 'contains')   return session.stringContainsSub(sH, pH)
            }
            // Phase 46e — {@code s.charAt(i)} returns the codepoint at position {@code i}. The
            // implicit bounds obligation ({@code 0 <= i < s.length()}) is synthesised by the
            // ObligationCollector as a {@link StringCharAtSite}, not here — translation returns
            // the value term only.
            if (m == 'charAt' && args.size() == 1) {
                Object idx = translate(args.get(0))
                return idx == null ? null : session.stringCharAt(sH, idx)
            }
            // Phase 47 — substring extraction. Groovy uses {@code (beginIndex, endIndex)} like
            // Java; Z3's {@code str.substr} takes {@code (offset, length)}. Convert by
            // {@code length = end - begin}. The single-arg form {@code s.substring(begin)} uses
            // {@code length = stringLength(s) - begin}. Implicit bounds obligations
            // ({@code 0 <= begin <= end <= length(s)}) live in the ObligationCollector.
            if (m == 'substring' && args.size() == 2) {
                Object begin = translate(args.get(0))
                Object end = translate(args.get(1))
                if (begin == null || end == null) return null
                Object len = session.minus(end, begin)
                return session.stringSubstring(sH, begin, len)
            }
            if (m == 'substring' && args.size() == 1) {
                Object begin = translate(args.get(0))
                if (begin == null) return null
                Object len = session.minus(session.stringLength(sH), begin)
                return session.stringSubstring(sH, begin, len)
            }
            // Phase 47 — {@code s.concat(t)} method form. The {@code +} operator form is
            // handled in {@link #translateBinary} where the type discrimination has the
            // operand handles already.
            if (m == 'concat' && args.size() == 1) {
                Object t = translateInSort(args.get(0), strSort)
                return t == null ? null : session.stringConcat(sH, t)
            }
            // Phase 47b/47f — {@code replace} / {@code replaceFirst} / {@code replaceAll}. Sound by
            // construction (the old {@code replace} path lowered replace-*all* to Z3's first-occurrence
            // {@code str.replace}, which over-claimed whenever the target occurred twice):
            //  (1) all-constant operands fold via the *real* Groovy/Java method → an exact literal. This
            //      works for any regex (the JDK computes it); a malformed regex/replacement just skips.
            //  (2) symbolic operands — {@code replace(CharSequence, CharSequence)} is literal replace-all,
            //      so it lowers to the uninterpreted replace-all model (sound weak axioms: absent ⇒ no-op,
            //      equal-length ⇒ length-preserving). {@code replaceFirst}/{@code replaceAll} take a *regex*:
            //      only a *plain-literal* pattern (no metacharacters) with a {@code $}/{@code \}-free
            //      replacement coincides with the string model — first-occurrence {@code str.replace} for
            //      {@code replaceFirst}, the replace-all model for {@code replaceAll}. Any real regex skips
            //      loudly rather than be mis-modelled as a literal substring.
            if ((m == 'replace' || m == 'replaceFirst' || m == 'replaceAll') && args.size() == 2) {
                String recvK = constStr(recv), oldK = constStr(args.get(0)), newK = constStr(args.get(1))
                if (recvK != null && oldK != null && newK != null) {
                    String folded
                    try {
                        folded = (m == 'replace')      ? recvK.replace(oldK, newK)
                               : (m == 'replaceFirst') ? recvK.replaceFirst(oldK, newK)
                               :                         recvK.replaceAll(oldK, newK)
                    } catch (Exception ignored) { return null }   // bad regex / replacement → honest skip
                    return session.litOfSort(strSort, folded)
                }
                Object oldSub = translateInSort(args.get(0), strSort)
                Object newSub = translateInSort(args.get(1), strSort)
                if (oldSub == null || newSub == null) return null
                if (m == 'replace') return session.stringReplaceAll(sH, oldSub, newSub)   // literal replace-all
                // replaceFirst / replaceAll: a plain-literal pattern + metachar-free replacement only.
                if (oldK == null || !isPlainLiteralRegex(oldK)) return null
                if (newK == null || newK.contains('$') || newK.contains('\\')) return null
                return (m == 'replaceFirst') ? session.stringReplace(sH, oldSub, newSub)
                                             : session.stringReplaceAll(sH, oldSub, newSub)
            }
            // Phase 47b — {@code s.indexOf(sub)} and {@code s.indexOf(sub, fromIndex)}.
            // Returns the leftmost position {@code i >= fromIndex} where {@code sub} occurs,
            // or {@code -1} if not found. No bounds obligation — {@code -1} is a legitimate
            // return value Groovy callers test against.
            if (m == 'indexOf' && args.size() == 1) {
                Object sub = translateInSort(args.get(0), strSort)
                if (sub == null) return null
                return session.stringIndexOf(sH, sub, session.intLit(0L))
            }
            if (m == 'indexOf' && args.size() == 2) {
                Object sub = translateInSort(args.get(0), strSort)
                Object from = translate(args.get(1))
                if (sub == null || from == null) return null
                return session.stringIndexOf(sH, sub, from)
            }
            // Phase 47c — {@code s.matches(regex)} for regex literals the inline parser can
            // handle (literals, alternation, concatenation, {@code .}, {@code */+/?},
            // character classes {@code [a-z]}/{@code [abc]}, groups). Unsupported features
            // return null and surface as honest skips.
            if (m == 'matches' && args.size() == 1) {
                Object re = parseRegexLiteral(args.get(0))
                if (re == null) return null
                return session.stringInRegex(sH, re)
            }
            // Phase 47f — {@code s.lastIndexOf(sub)} as uninterpreted with weak axioms.
            // Groovy's no-arg default for fromIndex is {@code length(s)} (search the whole string).
            if (m == 'lastIndexOf' && args.size() == 1) {
                Object sub = translateInSort(args.get(0), strSort)
                if (sub == null) return null
                return session.stringLastIndexOf(sH, sub, session.stringLength(sH))
            }
            if (m == 'lastIndexOf' && args.size() == 2) {
                Object sub = translateInSort(args.get(0), strSort)
                Object from = translate(args.get(1))
                if (sub == null || from == null) return null
                return session.stringLastIndexOf(sH, sub, from)
            }
            // Phase 47g — case folding. Uninterpreted with per-literal pinning (ASCII via
            // Locale.ROOT) and structural axioms (length, idempotence, cascade).
            if (m == 'toUpperCase' && args.isEmpty()) return session.stringToUpper(sH)
            if (m == 'toLowerCase' && args.isEmpty()) return session.stringToLower(sH)
            // Phase 47i — {@code s.reverse()} (GDK). Uninterpreted with per-literal pinning; literal
            // involution and length fall out, symbolic identities are out (no universals — see 47g).
            if (m == 'reverse' && args.isEmpty()) return session.stringReverse(sH)
            // Phase 100 — `s.next(i)` / `s.next()` (Groovy 6: the last character incremented by `i`, default 1
            // — `'A'.next(2) == 'C'`, `'A'.next(25) == 'Z'`). First slice: *single-character* receivers, ASCII,
            // no wraparound. Modelled as a fresh single-char string whose code point is `charAt(s,0) + i`,
            // *conditioned* on `s` being single-char — so a multi-character receiver leaves the result
            // unconstrained (honest "could not decide"), never a wrong answer. Range membership (`in 'A'..'Z'`,
            // Phase 99b) bridges to the result's char code in Z3, so `'A'.next(i)` for `i in 0..25` proves
            // `result in 'A'..'Z'`.
            if (m == 'next' && args.size() <= 1) {
                Object iH = args.isEmpty() ? session.intLit(1L) : translate(args.get(0))
                if (iH == null) return null
                Object zero = session.intLit(0L), one = session.intLit(1L)
                Object r = session.varOfSort('next$' + (quantCounter++), strSort)
                Object sSingle = session.eq(session.stringLength(sH), one)
                session.assertExpr(session.implies(sSingle, session.and([
                    session.eq(session.stringLength(r), one),
                    session.eq(session.stringCharAt(r, zero),
                               session.plus(session.stringCharAt(sH, zero), iH))])))
                return r
            }
            // {@code s.equalsIgnoreCase(t)} ≡ {@code toLower(s) == toLower(t)}. ASCII-faithful,
            // matches the Locale.ROOT contract used at the literal mint.
            if (m == 'equalsIgnoreCase' && args.size() == 1) {
                Object t = translateInSort(args.get(0), strSort)
                if (t == null) return null
                return session.eq(session.stringToLower(sH), session.stringToLower(t))
            }
            return null   // unsupported op on a String receiver — honest skip, don't fall through to list dispatch
        }

        // size() / isEmpty() / contains() need a named receiver for their oracle. The receiver
        // can be a bare {@code xs} (VariableExpression) or {@code old.xs} (PropertyExpression with
        // an old receiver) — the old form maps to the entry-snapshot key {@code old$xs}, which
        // checkPath pins to the entry value before any size-changing mutation runs.
        String rn = null
        if (!mce.implicitThis && recv instanceof VariableExpression) {
            rn = ((VariableExpression) recv).name
        } else if (recv instanceof PropertyExpression && isOldReceiver(((PropertyExpression) recv).objectExpression)) {
            rn = 'old$' + ((PropertyExpression) recv).propertyAsString
        }
        if (rn != null) {
            if (m == 'size' && args.isEmpty()) {
                return sizeOf(rn)
            }
            if (m == 'isEmpty' && args.isEmpty()) {
                return session.eq(sizeOf(rn), session.intLit(0L))
            }
            if (m == 'contains' && args.size() == 1) {
                // Precise membership: ∃ i. 0 <= i < rn.size ∧ rn[i] == y, over the modelled contents
                // (an upgrade from the old opaque uninterpreted predicate — `contains` now relates to
                // actual element values, e.g. `xs.contains(xs[k])`).
                Object y = translate(args.get(0))
                if (y == null) return null
                Object iv = session.boundIntVar('contains$q' + (quantCounter++))
                Object sel = session.select(arrayFor(rn), iv)
                Object range = session.and([session.le(session.intLit(0L), iv), session.lt(iv, sizeOf(rn))])
                return session.exists([iv], session.and([range, session.eq(sel, y)]), [sel])
            }
            // Phase 39 — common non-mutating list idioms as syntactic sugar for the existing
            // array-access path. {@code xs.get(i)} → {@code (select xs i)}; the bounds check
            // travels through the existing IndexSite machinery because BodyEncoder's
            // ObligationCollector lifts the same shape (xs.get(i) is also a deref site).
            if (m == 'get' && args.size() == 1) {
                Object idx = translate(args.get(0))
                return idx == null ? null : session.select(arrayFor(rn), idx)
            }
            // {@code xs.first()} / {@code xs.head()} → {@code xs[0]}. Sugar; the caller still
            // needs {@code xs.size() > 0} to discharge the implicit bounds check on xs[0].
            if ((m == 'first' || m == 'head') && args.isEmpty()) {
                return session.select(arrayFor(rn), session.intLit(0L))
            }
            // {@code xs.last()} → {@code xs[size - 1]}.
            if (m == 'last' && args.isEmpty()) {
                Object lastIdx = session.minus(sizeOf(rn), session.intLit(1L))
                return session.select(arrayFor(rn), lastIdx)
            }
        }

        // equals(): accept the method form of numeric equality, x.equals(y) === x == y.
        if (m == 'equals' && args.size() == 1) {
            Object l = translate(recv)
            Object r = translate(args.get(0))
            return (l == null || r == null) ? null : session.eq(l, r)
        }

        return null
    }

    /**
     * Phase 8a — pure same-class function calls. Three cases, in order:
     * <ol>
     *   <li><b>Closed evaluation:</b> all arguments fold to constants → compute the call to a
     *       literal ({@code pow2(10)} → 1024), via {@link PureEvaluator}.</li>
     *   <li><b>Bounded symbolic unfolding:</b> a symbolic argument with fuel remaining → inline the
     *       function's (single-expression) body, substituting the arguments, and translate that —
     *       re-entering here for nested calls, so recursion unfolds one level per call. A ternary
     *       body becomes an {@code ite}. (cf. F\*'s {@code fuel}.)</li>
     *   <li><b>Uninterpreted bottom:</b> fuel exhausted, or a body we can't inline → model the call
     *       as an unknown-but-fixed integer {@link SmtSession#uninterpretedFunc}. Sound: the result
     *       is constrained only through the levels actually unfolded.</li>
     * </ol>
     * {@link #unfoldDepth} is a per-encoder (≈ per-VC) total-unfold budget; it only decrements, which
     * guarantees termination. A consequence is that two separate applications of the same function in
     * one obligation may unfold to different depths, so proofs that rely on syntactically equating
     * them are not guaranteed — that is the inductive case (Phase 7), not this one.
     */
    private Object translateCall(Expression e) {
        if (pureEvaluator == null) return null

        // (1) closed evaluation
        Long v = pureEvaluator.tryEvaluate(e)
        if (v != null) return session.intLit(v)

        PureEvaluator.Call c = pureEvaluator.callInfo(e)
        if (c == null) return null   // not a same-class call — outside the fragment

        // The call as a *shared* uninterpreted symbol f#(args). Two occurrences of the same call are the
        // same term (congruence) — which is what lets an inductive proof equate `chain(u,d)` with the
        // hypothesis's `chain(next[u],d-1)`, where the old inline-the-body unfolding produced unequal terms
        // at different fuel depths.
        List<Object> handles = new ArrayList<Object>()
        for (Expression a : c.args) {
            Object h = translate(a)
            if (h == null) return null
            handles.add(h)
        }
        // The call's shared symbol f#(args). Int-returning helpers keep the historic Int-only declaration
        // (byte-identical to before); a helper whose return type is an enum or Boolean (e.g. a security
        // lattice's leq/join/meet) is declared over its real range sort via applyUF, which also infers the
        // domain sorts from the argument handles. Without this, an enum-sorted argument hits a sort mismatch
        // against the Int-only declaration. The range comes from the callee's signature, so it is stable
        // across occurrences (congruence) even before the body is unfolded.
        ClassNode pureRt = pureEvaluator.returnType(c)
        Object fSharp = isNonIntPureRange(pureRt)
            ? session.applyUF(c.name, handles, sortFor(pureRt))
            : session.uninterpretedFunc(c.name, handles)

        // Assert its defining equation f#(args) == body[params↦args] (the function's definition — sound by
        // its purity). Asserted once per distinct term and fuel-bounded, so recursion unfolds to a finite
        // depth *as equations* over the shared symbol — making the definition visible across a lemma boundary
        // (Phase 8a, the recursive-defs-in-contracts upgrade). When fuel runs out, or the body is un-encodable,
        // f#(args) is left fully uninterpreted — a sound over-approximation.
        if (unfoldDepth > 0 && definedCalls.add(fSharp)) {
            Expression body = pureEvaluator.unfoldBody(c)
            if (body != null) {
                int prev = unfoldDepth
                unfoldDepth = prev - 1
                try {
                    Object bodyH = translate(body)
                    if (bodyH != null) session.assertExpr(session.eq(fSharp, bodyH))
                } finally {
                    unfoldDepth = prev
                }
            }
        }
        return fSharp
    }

    /**
     * Lower {@code Sets.boundedBy(s, n)} (the cardinality axiom) to
     * {@code card(s) <= n ∧ (card(s) < n ∨ coverage)} where {@code coverage} is the
     * "every domain element ∈ s" predicate. Two element-sort cases:
     *
     * - **Int** (Phase 19): {@code coverage = ∀ i. 0 <= i < n ⟹ i ∈ s} — bounded universal over
     *   {@code [0, n)}, the natural domain when {@code s} is Int-element.
     * - **Enum** (Phase 29): {@code coverage = c1 ∈ s ∧ … ∧ cN ∈ s} — finite conjunction over
     *   the enum's constants, applied when {@code n} folds to the enum's domain size. Without an
     *   ordering on the enum sort there is no "first n constants" notion, so non-matching {@code n}
     *   skips with an honest "outside fragment" diagnostic.
     */
    private Object translateSetsBounded(Expression setExpr, Expression nExpr) {
        String key = setKeyFor(setExpr)
        if (key == null) return null
        Object nH = translate(nExpr)
        if (nH == null) return null
        Object setH = setFor(key)
        Object card = cardOf(setH)
        Object elemSort = setKeySortForKey(key)
        if (elemSort == session.intSort()) {
            // Phase 31 — record the bound so a later s.containsAll(t) on Int sets can find a
            // domain to range its universal over. Side-effect, scoped per encoder/session.
            intSubsetBounds.put(key, nH)
            Object everyDomain = domainCoverageForall(setH, nH)
            return session.and([session.le(card, nH), session.or([session.lt(card, nH), everyDomain])])
        }
        // Phase 29 — enum case: only meaningful when n matches the enum's domain size.
        ClassNode enumType = elementTypeForSetKey(key)
        if (enumType != null && (enumType.isEnum() || isEnumLikeType(enumType))) {
            Long nLong = tryFoldToLong(nExpr)
            int enumSize = enumConstantNames(enumType).size()
            if (nLong != null && nLong.longValue() == (long) enumSize) {
                Object everyEnum = finiteEnumCoverage(setH, enumType)
                return session.and([session.le(card, nH), session.or([session.lt(card, nH), everyEnum])])
            }
        }
        null   // non-matching n or unsupported element sort — honest skip
    }

    /**
     * Translate {@code Forall.range(lo, hi, { i -> body })} to the bounded
     * universal {@code ∀ i. (lo <= i < hi) ⇒ body}. The closure's single
     * parameter is bound to a fresh quantified integer while the body is
     * translated — shadowing any same-named variable in scope, restored
     * afterwards — and the {@code (select arr i)} terms the body produces become
     * the quantifier's instantiation triggers.
     */
    private Object translateForallRange(Expression lo, Expression hi, ClosureExpression clo) {
        String pname = closureParamName(clo)
        Expression bodyExpr = singleExprOf(clo?.code)
        if (pname == null || bodyExpr == null) return null
        return emitForall(pname, translate(lo), translate(hi), bodyExpr, null)
    }

    /**
     * {@code Sorted.ascending(a)} (and {@code descending} / {@code strictlyAscending} /
     * {@code strictlyDescending}) over a bare array/list variable — the canonical sortedness
     * precondition, emitted as the flat two-variable axiom
     * {@code ∀ j,k. 0 <= j < k < n ⇒ a[j] R a[k]} with the multi-pattern trigger {@code {a[j], a[k]}}
     * (via {@link SmtBackend#forallMultiPattern}). This pins the instantiation the hand-nested
     * {@code every} leaves to Z3's auto-pattern, so the random-access "gap" fact ({@code a[i] R a[mid]})
     * fires in one deterministic step. Pure sugar over the asserted fact — no new assumption.
     *
     * <p>The element comparison ({@code <=} / {@code <}) rides Z3's numeric order, so an Int or exact-Real
     * element sort verifies and any other (e.g. String) cleanly skips via the {@code try} — the term is
     * only built here, never asserted, so a sort-mismatch throw can't corrupt the session.
     */
    private Object translateSorted(String m, Expression arg) {
        if (!(arg instanceof VariableExpression)) return null
        boolean strict, ascending
        switch (m) {
            case 'ascending':          ascending = true;  strict = false; break
            case 'descending':         ascending = false; strict = false; break
            case 'strictlyAscending':  ascending = true;  strict = true;  break
            case 'strictlyDescending': ascending = false; strict = true;  break
            default: return null
        }
        String name = ((VariableExpression) arg).name
        try {
            Object arr = arrayFor(name)
            Object hi = sizeOf(name)
            if (arr == null || hi == null) return null
            Object jv = session.boundIntVar('sortJ$q' + (quantCounter++))
            Object kv = session.boundIntVar('sortK$q' + (quantCounter++))
            Object aj = session.select(arr, jv)
            Object ak = session.select(arr, kv)
            if (aj == null || ak == null) return null
            Object range = session.and([session.le(session.intLit(0L), jv), session.lt(jv, kv), session.lt(kv, hi)])
            Object rel = ascending ? (strict ? session.lt(aj, ak) : session.le(aj, ak))
                                   : (strict ? session.lt(ak, aj) : session.le(ak, aj))
            Object body = session.implies(range, rel)
            return session.forallMultiPattern([jv, kv], body, [aj, ak])
        } catch (Exception ignored) {
            return null   // unmodelled element sort / no size oracle → honest skip
        }
    }

    /**
     * Phase 99 — `i in lo..hi` and `(lo..hi).contains(i)` for an *integer* range and integer value. The
     * default `..`/`..<` range has step 1, so every integer in the (order-agnostic) interval is a member —
     * i.e. {@code contains} coincides exactly with {@link #translateContainsWithinBounds} there. Guarded to
     * integral endpoints AND an integral value: for a decimal range or value the two diverge (a
     * step-sensitive `(1..3).contains(2.5)` is {@code false} while 2.5 is *within bounds*), so those skip.
     */
    private Object translateIntRangeContains(Expression rangeRecv, Expression value) {
        if (!(rangeRecv instanceof RangeExpression)) return null
        RangeExpression re = (RangeExpression) rangeRecv
        // Integer range (step 1, integer endpoints) — so contains is integer membership = bounds. The endpoint
        // literals carry a reliable type; the queried value is a free closure variable (AST type Object), so
        // gate it by its *modelled sort* instead: an Int term is fine, a decimal/Real one is skipped because
        // step-sensitive contains diverges from pure bounds there (a non-Int term makes the bounds comparison
        // throw inside translateContainsWithinBounds → a clean null skip anyway).
        if (!isIntLikeType(re.from?.getType()) || !isIntLikeType(re.to?.getType())) return null
        Object vH = translate(value)
        if (vH == null || session.isReal(vH)) return null
        return translateContainsWithinBounds(rangeRecv, value)
    }

    /**
     * Phase 99b — `s in 'A'..'Z'` / `('A'..'Z').contains(s)` for a single-character {@code String} range.
     * Such a range *is* the regex character class {@code [A-Z]}, so it lowers to {@code str.in_re(s,
     * re.range('A','Z'))} — the identical construction the regex engine uses for {@code [a-z]} (Phase 47d).
     * That gives the semantics for free: {@code re.range} matches exactly one character in the code-point
     * interval, so a multi-character or empty {@code s} is (correctly) a non-member, no length constraint
     * needed. Endpoints are constant single-char Strings, so direction and {@code ..<}/{@code <..} exclusivity
     * collapse to constant code-point arithmetic on the {@code [lo, hi]} interval; an empty interval matches
     * nothing. The value must be String-typed (multi-char / symbolic endpoints, or a non-String value, skip).
     */
    private Object translateStringRangeContains(Expression rangeRecv, Expression value) {
        if (!(rangeRecv instanceof RangeExpression) || !isStringReceiver(value)) return null
        RangeExpression re = (RangeExpression) rangeRecv
        Integer fromCode = singleCharCode(re.from)
        Integer toCode = singleCharCode(re.to)
        if (fromCode == null || toCode == null) return null
        int lo, hi
        if (fromCode <= toCode) {                 // ascending: exclusiveLeft drops `from`, exclusiveRight `to`
            lo = fromCode + (re.exclusiveLeft ? 1 : 0); hi = toCode - (re.exclusiveRight ? 1 : 0)
        } else {                                  // descending: the `to` endpoint is the minimum
            lo = toCode + (re.exclusiveRight ? 1 : 0); hi = fromCode - (re.exclusiveLeft ? 1 : 0)
        }
        Object strSort = session.declareSort('String')
        Object vH = translateInSort(value, strSort)
        if (vH == null) return null
        if (lo > hi) return session.boolLit(false)   // empty range — nothing is a member
        Object regex = session.reRange(session.litOfSort(strSort, String.valueOf((char) lo)),
                                       session.litOfSort(strSort, String.valueOf((char) hi)))
        return session.stringInRegex(vH, regex)
    }

    /** The code point of a single-character {@code String}/{@code Character} constant, else null. */
    private static Integer singleCharCode(Expression e) {
        if (e instanceof ConstantExpression) {
            Object v = ((ConstantExpression) e).value
            if (v instanceof String && ((String) v).length() == 1) return (int) ((String) v).charAt(0)
            if (v instanceof Character) return (int) ((Character) v).charValue()
        }
        null
    }

    /**
     * {@code range.containsWithinBounds(v)} for every Groovy range form — fully-closed {@code a..b},
     * left-open {@code a<..b}, right-open {@code a..<b}, open {@code a<..<b} — plus the
     * {@code new NumberRange(a,b,step)} / {@code new IntRange(a,b)} constructors (always closed).
     *
     * <p>{@code containsWithinBounds} ignores the step, so it lowers to an interval with per-endpoint
     * strictness. Decoded from {@code NumberRange.containsWithinBounds} (which sorts its endpoints and is
     * {@code reverse}-aware), each endpoint keeps <em>its own</em> inclusivity in both order-orientations,
     * giving an order-agnostic predicate exact for forward, reverse, <em>and</em> equal bounds:
     * {@code (a ≤/< v ∧ v ≤/< b) || (b ≤/< v ∧ v ≤/< a)} — {@code ≤} where the endpoint is inclusive,
     * {@code <} where exclusive. The comparisons are built as synthetic {@code <}/{@code <=} expressions
     * and re-translated, so they ride the per-sort dispatch (Int / exact Real) — decimal bounds for free.
     *
     * <p>Pure bounds for <em>every</em> range kind — this is the documented {@code Range} contract
     * ({@code containsWithinBounds} is "between the from and to values", explicitly distinct from
     * {@code contains}; the interface Javadoc gives {@code containsWithinBounds(2) == true} while
     * {@code contains(2) == false}). {@code IntRange.containsWithinBounds} used to delegate to
     * {@code contains} (integer membership), so {@code (2..4).containsWithinBounds(2.5)} returned
     * {@code false} while {@code NumberRange} returned {@code true} for the same interval — fixed in
     * GROOVY-12067 ({@code IntRange} is now pure-bounds too). The verifier models pure bounds for all range
     * kinds, matching both the fixed runtime and the contract, so any numeric {@code v} is exact regardless
     * of endpoint type. A character/{@code String} range skips (no modelled order). The {@code try} keeps a
     * non-arithmetic comparison a clean skip — terms aren't asserted until {@code checkPath}, so a throw
     * can't corrupt the session.
     */
    private Object translateContainsWithinBounds(Expression recv, Expression value) {
        Expression lo, hi
        boolean loIncl = true, hiIncl = true     // constructors below are always fully-closed
        if (recv instanceof RangeExpression) {
            RangeExpression re = (RangeExpression) recv
            lo = re.from; hi = re.to
            loIncl = !re.exclusiveLeft
            hiIncl = !re.exclusiveRight
        } else if (recv instanceof ConstructorCallExpression) {
            ConstructorCallExpression cce = (ConstructorCallExpression) recv
            String tn = cce.type?.nameWithoutPackage
            List<Expression> cargs = ctorArgList(cce)
            // NumberRange(from, to[, step]) / IntRange(from, to): endpoints are the first two args (the
            // step is irrelevant to a bounds test). Reject the boolean-first IntRange(inclusive, …) overload.
            boolean boolFirst = !cargs.isEmpty() && cargs.get(0) instanceof ConstantExpression &&
                                ((ConstantExpression) cargs.get(0)).value instanceof Boolean
            if (!((tn == 'NumberRange' || tn == 'IntRange') && cargs.size() >= 2 && !boolFirst)) return null
            lo = cargs.get(0); hi = cargs.get(1)
        } else {
            return null
        }
        // Numeric-only: a character/String range would reach an arithmetic comparison on a String sort.
        if (isStringReceiver(lo) || isStringReceiver(hi) || isStringReceiver(value)) return null
        try {
            // Each endpoint keeps its own inclusivity; OR the two orderings to be min/max-agnostic.
            Object loV = translateCompare(lo, value, loIncl)     // a ≤/< v
            Object vHi = translateCompare(value, hi, hiIncl)     // v ≤/< b
            Object hiV = translateCompare(hi, value, hiIncl)     // b ≤/< v
            Object vLo = translateCompare(value, lo, loIncl)     // v ≤/< a
            if (loV == null || vHi == null || hiV == null || vLo == null) return null
            return session.or([session.and([loV, vHi]), session.and([hiV, vLo])])
        } catch (Exception ignored) {
            return null   // non-arithmetic sort or unmodelled bound — loud skip, never a crash
        }
    }

    /** Translate {@code l < r} (inclusive=false) or {@code l <= r} (inclusive=true), routed through per-sort dispatch. */
    private Object translateCompare(Expression l, Expression r, boolean inclusive) {
        int tok = inclusive ? Types.COMPARE_LESS_THAN_EQUAL : Types.COMPARE_LESS_THAN
        BinaryExpression be = new BinaryExpression(l, Token.newSymbol(tok, -1, -1), r)
        return translate(be)
    }

    private static List<Expression> ctorArgList(ConstructorCallExpression cce) {
        Expression a = cce.arguments
        if (a instanceof ArgumentListExpression) return ((ArgumentListExpression) a).expressions
        if (a instanceof TupleExpression) return ((TupleExpression) a).expressions
        return Collections.<Expression> emptyList()
    }

    /** A compound-assignment op type → its base binary op type, or -1 if not a modelled compound assignment. */
    private static int compoundBaseOp(int t) {
        if (t == Types.PLUS_EQUAL)     return Types.PLUS
        if (t == Types.MINUS_EQUAL)    return Types.MINUS
        if (t == Types.MULTIPLY_EQUAL) return Types.MULTIPLY
        if (t == Types.DIVIDE_EQUAL)   return Types.DIVIDE
        if (t == Types.MOD_EQUAL)      return Types.MOD
        -1
    }

    /** True if {@code e} is a compound assignment {@code lhs += rhs} (or {@code -= *= /= %=}). */
    static boolean isCompoundAssign(Expression e) {
        e instanceof BinaryExpression && compoundBaseOp(((BinaryExpression) e).operation.type) >= 0
    }

    /**
     * Desugar a compound assignment {@code lhs OP= rhs} to the plain assignment {@code lhs = (lhs OP rhs)},
     * so the existing assignment handling (variable / field / array-element targets) applies unchanged.
     * Phase 85 — purely a statement-level rewrite; contract closures never contain assignments.
     */
    static BinaryExpression desugarCompoundAssign(BinaryExpression be) {
        Token op = be.operation
        Token baseTok = Token.newSymbol(compoundBaseOp(op.type), op.startLine, op.startColumn)
        Expression combined = new BinaryExpression(be.leftExpression, baseTok, be.rightExpression)
        Token assignTok = Token.newSymbol(Types.ASSIGN, op.startLine, op.startColumn)
        new BinaryExpression(be.leftExpression, assignTok, combined)
    }

    /** The {@code ++}/{@code --} operation and operand of a postfix/prefix expression, or null. */
    private static Object[] incDecParts(Expression e) {
        if (e instanceof PostfixExpression) return [((PostfixExpression) e).operation, ((PostfixExpression) e).expression] as Object[]
        if (e instanceof PrefixExpression)  return [((PrefixExpression) e).operation, ((PrefixExpression) e).expression] as Object[]
        null
    }

    /** True if {@code e} is an increment/decrement {@code i++} / {@code ++i} / {@code i--} / {@code --i}. */
    static boolean isIncDec(Expression e) {
        Object[] p = incDecParts(e)
        if (p == null) return false
        int t = ((Token) p[0]).type
        t == Types.PLUS_PLUS || t == Types.MINUS_MINUS
    }

    /**
     * Desugar an increment/decrement <em>statement</em> {@code i++} / {@code ++i} / {@code i--} / {@code --i}
     * to {@code i = i + 1} / {@code i = i - 1}. As a statement the pre/post distinction is irrelevant (it
     * differs only in the expression's *value*, which a statement discards) — and the operand may be a
     * variable, array element, or field, so the existing assignment paths apply (Phase 86).
     */
    static BinaryExpression desugarIncDec(Expression e) {
        Object[] p = incDecParts(e)
        Token op = (Token) p[0]
        Expression operand = (Expression) p[1]
        int baseType = (op.type == Types.PLUS_PLUS) ? Types.PLUS : Types.MINUS
        Token baseTok = Token.newSymbol(baseType, op.startLine, op.startColumn)
        Expression combined = new BinaryExpression(operand, baseTok, new ConstantExpression(Integer.valueOf(1)))
        Token assignTok = Token.newSymbol(Types.ASSIGN, op.startLine, op.startColumn)
        new BinaryExpression(operand, assignTok, combined)
    }

    /**
     * Expand each statement's single <em>expression-position</em> increment/decrement into an explicit
     * two-statement sequence, so the path/loop processors see only plain assignments. A <b>post</b>-form
     * (`x = i++`, `a[i++] = v`, `x = a[i++]`) becomes `[…uses i…, i = i + 1]` — the old value is used, then the
     * side effect — and a <b>pre</b>-form (`x = ++i`) becomes `[i = i + 1, x = i]` — side effect first, then the
     * new value. A <em>top-level</em> `i++` statement is left alone ({@link #desugarIncDec} handles it), as is a
     * statement with no inc/dec, or with more than one (sequencing several is ambiguous — skip loudly rather
     * than risk mis-ordering). Phase: `++`/`--` in expression position.
     */
    static List<Statement> expandIncDecStatements(List<Statement> stmts) {
        List<Statement> out = new ArrayList<Statement>(stmts.size())
        for (Statement st : stmts) {
            List<Statement> exp = expandStatementIncDec(st)
            if (exp != null) out.addAll(exp) else out.add(st)
        }
        out
    }

    private static List<Statement> expandStatementIncDec(Statement st) {
        if (!(st instanceof ExpressionStatement)) return null
        Expression e = ((ExpressionStatement) st).expression
        if (isIncDec(e)) return null                 // top-level `i++` — desugarIncDec handles it
        // Phase 127 — array store `arr[idx] = value` whose value mutates a variable used in idx (e.g.
        // `a[i] = ++i`, `r[i] = spec(++i)`): snapshot idx into a fresh local first so the index reads the
        // pre-value, then the value's inc/dec hoists cleanly. Without this the store lands at the wrong slot.
        List<Statement> snapped = expandArrayStoreSnapshot(st, e)
        if (snapped != null) return snapped
        List<Object[]> incs = new ArrayList<Object[]>()   // each: [operand, isPre, opToken]
        collectIncDecs(e, incs)
        if (incs.isEmpty()) return null
        for (Object[] inc : incs) {
            if (!(inc[0] instanceof VariableExpression)) return null     // array-element/field target → skip
        }
        // Two sound routes to hoist. Either closes the unsound case where a variable is read again *after*
        // its own inc/dec — `x = i++ + i`, where Java advances `i` mid-statement so the 2nd `i` is the new
        // value — which must NOT be hoisted (it would silently mis-model).
        if (!(appearsOnceSafe(e, incs) || evalOrderAssignSafe(e, incs))) return null
        Expression rewritten = replaceAllIncDec(e)
        if (anyIncDec(rewritten)) return null                            // an inc/dec the rewriter couldn't reach → skip
        List<Statement> pre = new ArrayList<Statement>(), post = new ArrayList<Statement>()
        for (Object[] inc : incs) {
            (((boolean) inc[1]) ? pre : post).add(incAssignStatement((Expression) inc[0], (Token) inc[2], st))
        }
        Statement mainStmt = new ExpressionStatement(rewritten)
        mainStmt.setSourcePosition(st)
        List<Statement> out = new ArrayList<Statement>(pre)
        out.add(mainStmt)
        out.addAll(post)
        out
    }

    private static final java.util.concurrent.atomic.AtomicInteger SNAP_COUNTER =
        new java.util.concurrent.atomic.AtomicInteger()

    /**
     * Phase 127 — for an array store {@code arr[idx] = value} whose {@code value} increments a variable that
     * also appears in {@code idx} (so the index must read the *pre*-value, but a naive hoist of the increment
     * before the statement would make it read the post-value), snapshot {@code idx} into a fresh local and
     * rewrite to {@code [$snapN = idx, arr[$snapN] = value]}. The rewritten store's index no longer aliases the
     * incremented variable, so the value's inc/dec then hoists soundly through the normal routes. Returns null
     * when the shape doesn't apply (the normal expansion handles everything else, including `a[i++] = v`).
     */
    private static List<Statement> expandArrayStoreSnapshot(Statement st, Expression e) {
        if (!(e instanceof BinaryExpression) || ((BinaryExpression) e).operation.type != Types.ASSIGN) return null
        BinaryExpression be = (BinaryExpression) e
        if (!(be.leftExpression instanceof BinaryExpression)) return null
        BinaryExpression sub = (BinaryExpression) be.leftExpression
        if (sub.operation.type != Types.LEFT_SQUARE_BRACKET || !(sub.leftExpression instanceof VariableExpression)) return null
        Expression idx = sub.rightExpression
        Expression value = be.rightExpression
        if (anyIncDec(idx) || !anyIncDec(value)) return null      // index has its own inc/dec, or nothing to snapshot for
        List<Object[]> incs = new ArrayList<Object[]>()
        collectIncDecs(value, incs)
        boolean aliases = false
        for (Object[] inc : incs) {
            if (!(inc[0] instanceof VariableExpression)) return null
            if (countVarOccurrences(idx, ((VariableExpression) inc[0]).name) > 0) aliases = true
        }
        if (!aliases) return null                                 // index doesn't read an incremented var → normal routes suffice
        String tmp = '$snap' + SNAP_COUNTER.incrementAndGet()
        Token assignTok = Token.newSymbol(Types.ASSIGN, st.lineNumber, st.columnNumber)
        Statement snapStmt = new ExpressionStatement(new BinaryExpression(new VariableExpression(tmp), assignTok, idx))
        snapStmt.setSourcePosition(st)
        BinaryExpression newSub = new BinaryExpression(sub.leftExpression, sub.operation, new VariableExpression(tmp))
        Statement mainStmt = new ExpressionStatement(new BinaryExpression(newSub, be.operation, value))
        mainStmt.setSourcePosition(st)
        List<Statement> expanded = expandStatementIncDec(mainStmt)
        List<Statement> out = new ArrayList<Statement>()
        out.add(snapStmt)
        if (expanded != null) out.addAll(expanded) else out.add(mainStmt)
        out
    }

    /**
     * Route 1 — every inc/dec is on a variable that occurs *exactly once* in the statement (only at its own
     * inc/dec site). There is then no ordering interaction at all: pre-forms move before, post-forms after, in
     * any order, same result. Shape-agnostic (it just counts), so it covers method-call args etc. too. Enables
     * the two-cursor `dst[j++] = src[i++]` (distinct `i`, `j`, each once).
     */
    private static boolean appearsOnceSafe(Expression e, List<Object[]> incs) {
        Set<String> seen = new HashSet<String>()
        for (Object[] inc : incs) {
            String name = ((VariableExpression) inc[0]).name
            if (!seen.add(name)) return false                    // same var incremented twice → order matters
            if (countVarOccurrences(e, name) != 1) return false  // var read elsewhere → can't move blindly
        }
        true
    }

    /**
     * Route 2 — evaluation-order analysis for idioms like `dst[i] = src[i++]`, where a variable appears more
     * than once but the hoist is still sound. Restricted to a slice we can reason about exactly: an assignment
     * {@code LHS = RHS} with (a) only sub-expressions whose evaluation order is plain left-to-right (variables,
     * constants, arithmetic/subscript {@code BinaryExpression}s, inc/decs — no method calls, properties or
     * ternaries), (b) no inc/dec in the LHS, and (c) every inc/dec on a simple variable that is not the
     * assignment target. Java evaluates the LHS index, then the RHS, then stores. The check, per inc/dec, in
     * evaluation order:
     * <ul>
     *   <li><b>post</b> ({@code i++}) hoists to *after* the statement (every read sees the old value), so it
     *       must be the <em>last</em> occurrence of its variable — e.g. {@code dst[i] = src[i++]} (the LHS `i`
     *       is earlier, reads old), but not {@code x = i++ + i} (a later read would want the new value).</li>
     *   <li><b>pre</b> ({@code ++i}) hoists to *before* the statement (every read sees the new value), so it
     *       must be the <em>first</em> occurrence — e.g. {@code x = ++i + i}, but not {@code dst[i] = src[++i]}
     *       (the LHS index `i`, evaluated first, must read the old value).</li>
     * </ul>
     */
    private static boolean evalOrderAssignSafe(Expression e, List<Object[]> incs) {
        Expression lhs, rhs
        if (e instanceof DeclarationExpression) {
            lhs = ((DeclarationExpression) e).leftExpression; rhs = ((DeclarationExpression) e).rightExpression
        } else if (e instanceof BinaryExpression && ((BinaryExpression) e).operation.type == Types.ASSIGN) {
            lhs = ((BinaryExpression) e).leftExpression; rhs = ((BinaryExpression) e).rightExpression
        } else {
            return false                                          // not a plain assignment → out of this slice
        }
        if (!onlySafeShapes(lhs) || !onlySafeShapes(rhs)) return false   // unknown eval order → bail
        if (anyIncDec(lhs)) return false                          // the slice: inc/decs live in the RHS only
        // The assignment target variable (if a simple var): excluded from reads, and never itself inc/dec'd
        // here — `i = i++` / `i = ++i` would clobber (Java's store wins; the hoisted increment would not).
        String target = (lhs instanceof VariableExpression) ? ((VariableExpression) lhs).name : null
        for (Object[] inc : incs) {
            if (((VariableExpression) inc[0]).name == target) return false
        }
        // Evaluation-order occurrences (reads + inc/dec operands), skipping the simple-var write target.
        List<Object[]> ev = new ArrayList<Object[]>()             // each: [varName, kind] (0 read, 1 post, 2 pre)
        if (!(lhs instanceof VariableExpression)) evalOrderOccurrences(lhs, ev)  // array LHS: its index reads count
        evalOrderOccurrences(rhs, ev)
        for (int p = 0; p < ev.size(); p++) {
            int kind = (int) ev[p][1]
            if (kind == 0) continue
            String v = (String) ev[p][0]
            if (kind == 1) {                                      // post-inc hoists *after* — must be the LAST read
                for (int q = p + 1; q < ev.size(); q++) if (ev[q][0] == v) return false
            } else {                                              // pre-inc hoists *before* — must be the FIRST read
                for (int q = 0; q < p; q++) if (ev[q][0] == v) return false
            }
        }
        true
    }

    /** True iff {@code e} is built only from shapes whose evaluation order is plain left-to-right. */
    private static boolean onlySafeShapes(Expression e) {
        if (e instanceof VariableExpression || e instanceof ConstantExpression) return true
        if (isIncDec(e)) return onlySafeShapes((Expression) incDecParts(e)[1])
        if (e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e
            return onlySafeShapes(be.leftExpression) && onlySafeShapes(be.rightExpression)
        }
        false
    }

    /** Append {@code [varName, kind]} (0 read, 1 post-inc, 2 pre-inc) for each occurrence in evaluation order. */
    private static void evalOrderOccurrences(Expression e, List<Object[]> ev) {
        if (e instanceof VariableExpression) { ev.add([((VariableExpression) e).name, 0] as Object[]); return }
        if (e instanceof ConstantExpression) return
        if (isIncDec(e)) {
            Expression op = (Expression) incDecParts(e)[1]
            if (op instanceof VariableExpression) ev.add([((VariableExpression) op).name, (e instanceof PrefixExpression) ? 2 : 1] as Object[])
            else evalOrderOccurrences(op, ev)
            return
        }
        if (e instanceof BinaryExpression) {
            evalOrderOccurrences(((BinaryExpression) e).leftExpression, ev)
            evalOrderOccurrences(((BinaryExpression) e).rightExpression, ev)
        }
    }

    /** Collect every inc/dec in the BinaryExpression-reachable shapes as {@code [operand, isPre, opToken]}. */
    private static void collectIncDecs(Expression e, List<Object[]> out) {
        if (isIncDec(e)) {
            Object[] p = incDecParts(e)
            out.add([(Expression) p[1], (e instanceof PrefixExpression), (Token) p[0]] as Object[])
            return
        }
        if (e instanceof BinaryExpression) {
            collectIncDecs(((BinaryExpression) e).leftExpression, out)
            collectIncDecs(((BinaryExpression) e).rightExpression, out)
        }
    }

    /** Replace every inc/dec (BinaryExpression-reachable) with its operand, preserving source positions. */
    private static Expression replaceAllIncDec(Expression e) {
        if (isIncDec(e)) return (Expression) incDecParts(e)[1]
        if (e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e
            return stampedBinary(replaceAllIncDec(be.leftExpression), be.operation, replaceAllIncDec(be.rightExpression), be)
        }
        e
    }

    /** Total occurrences of the variable {@code name} anywhere in {@code e} (a complete traversal — sound). */
    private static int countVarOccurrences(Expression e, String name) {
        int[] c = [0] as int[]
        e.visit(new org.codehaus.groovy.ast.CodeVisitorSupport() {
            @Override void visitVariableExpression(VariableExpression ve) { if (ve.name == name) c[0]++ }
        })
        c[0]
    }

    /** True if any inc/dec remains anywhere in {@code e} (a complete traversal). */
    private static boolean anyIncDec(Expression e) {
        boolean[] f = [false] as boolean[]
        e.visit(new org.codehaus.groovy.ast.CodeVisitorSupport() {
            @Override void visitPostfixExpression(PostfixExpression pe) { if (isIncDec(pe)) f[0] = true; super.visitPostfixExpression(pe) }
            @Override void visitPrefixExpression(PrefixExpression pe) { if (isIncDec(pe)) f[0] = true; super.visitPrefixExpression(pe) }
        })
        f[0]
    }

    /** The hoisted increment statement {@code operand = operand ± 1}, carrying {@code src}'s source position. */
    private static Statement incAssignStatement(Expression operand, Token op, Statement src) {
        int baseType = (op.type == Types.PLUS_PLUS) ? Types.PLUS : Types.MINUS
        Token baseTok = Token.newSymbol(baseType, op.startLine, op.startColumn)
        Expression incExpr = new BinaryExpression(operand,
            Token.newSymbol(Types.ASSIGN, op.startLine, op.startColumn),
            new BinaryExpression(operand, baseTok, new ConstantExpression(Integer.valueOf(1))))
        Statement incStmt = new ExpressionStatement(incExpr)
        incStmt.setSourcePosition(src)
        incStmt
    }

    /**
     * A reconstructed BinaryExpression carrying the source position of the node it replaces. Without the
     * position, an implicit obligation anchored to the synthetic node (e.g. the bounds check on a rewritten
     * {@code a[i]} from {@code a[i++]}) has its diagnostic *silently dropped* — the Phase-49c trap.
     */
    private static BinaryExpression stampedBinary(Expression l, Token op, Expression r, Expression src) {
        BinaryExpression b = new BinaryExpression(l, op, r)
        b.setSourcePosition(src)
        b
    }

    /**
     * Translate a postcondition as a <em>proof goal</em> (as opposed to an assumption). Walks the goal to
     * mark the positive-polarity stream-{@code every} nodes, so the unbounded-stream induction encoding —
     * which is stronger than the {@code every} it stands for, hence sound only when proven, not assumed —
     * may fire for exactly those. Cleared afterwards so ordinary (assumption) translations never see it.
     */
    Object translateGoal(Expression e) {
        goalPositiveEvery.clear()
        markPositiveEvery(e, true)
        try {
            return translateBool(e)
        } finally {
            goalPositiveEvery.clear()
        }
    }

    /**
     * Phase 8c — translate {@code e} in a <b>boolean position</b> (a contract, assert, guard, or boolean-operator
     * operand), applying **Groovy truth** to a non-Boolean value as Groovy itself does. Recurses through
     * {@code &&}/{@code ||}/{@code !}/{@code ==>} (coercing each operand), and at a leaf coerces a non-Boolean via
     * {@link #truthy}. Returns null (caller skips loudly) when an operand's truth can't be modelled — never a
     * silent drop or a sort-mismatch crash. This is what makes `@Requires({ xs })`, `assert s`, and
     * `@Ensures({ result })` mean what they mean in Groovy.
     */
    Object translateBool(Expression e) {
        return truthy(e, translate(e))            // translate handles the structure (incl. &&/||/! operand
                                                  // coercion); this coerces the result to Boolean if it isn't one
    }

    /**
     * Groovy truth of {@code e} (whose translated value is {@code h}) as a Boolean term — by *sort* where the
     * value carries it (already Boolean → unchanged; Int → {@code != 0}; String/Seq → non-null ∧ length &gt; 0)
     * and by *name* otherwise (a list/set/map → non-null ∧ size &gt; 0; a plain object reference → non-null).
     * Returns null when the kind's truth isn't modelled (a decimal, an {@code asBoolean()}-customiser, or an
     * un-nameable reference) so the caller skips loudly — never a silent pass or a crash.
     */
    private Object truthy(Expression e, Object h) {
        if (h != null && session.isBool(h)) return h                  // already Boolean — nothing to coerce
        // A known sized container is checked first — its value handle may be Int-sorted (a size), which would
        // otherwise be mis-read as integral truth. Groovy truth: non-null ∧ size > 0.
        if (e instanceof VariableExpression) {
            String name = ((VariableExpression) e).name
            if (listElementTypes.containsKey(name) || listNames.contains(name) ||
                setElementTypes.containsKey(name) || mapTypes.containsKey(name)) {
                return session.and([session.not(nullityOf(name)), session.gt(sizeOf(name), session.intLit(0L))])
            }
        }
        if (h != null) {
            if (session.isSeq(h)) {                                   // String: non-null ∧ length > 0
                Object lenPos = session.gt(session.stringLength(h), session.intLit(0L))
                if (!(e instanceof VariableExpression)) return lenPos // a literal / concat is non-null by construction
                return session.and([session.not(nullityOf(((VariableExpression) e).name)), lenPos])
            }
            if (session.isInt(h)) return session.ne(h, session.intLit(0L))   // integral truth: != 0
        }
        if (e instanceof VariableExpression) {                       // a plain object reference: non-null
            String name = ((VariableExpression) e).name
            ClassNode st = scalarTypes.get(name)
            if (objectParams.containsKey(name) || (st != null && isPlainObjectTruth(st))) {
                return session.not(nullityOf(name))
            }
        }
        null
    }

    /**
     * Polarity walk: record the stream-{@code every} call nodes reachable in <em>positive</em> polarity.
     * Positive polarity is preserved through {@code &&}/{@code ||} and the consequent of {@code ==>};
     * flipped by {@code !} and the antecedent of {@code ==>}. Any other construct (comparisons, ternary
     * condition, method arguments, …) is treated as polarity-indeterminate and stops the walk — so the
     * stronger induction encoding is only ever used where it is genuinely sound.
     */
    private void markPositiveEvery(Expression e, boolean positive) {
        if (e == null) return
        if (positive && isStreamEveryCall(e)) goalPositiveEvery.add(e)
        if (e instanceof NotExpression) {
            markPositiveEvery(((NotExpression) e).expression, !positive)
        } else if (e instanceof BooleanExpression) {
            markPositiveEvery(((BooleanExpression) e).expression, positive)
        } else if (e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e
            int op = be.operation.type
            if (op == Types.LOGICAL_AND || op == Types.LOGICAL_OR) {
                markPositiveEvery(be.leftExpression, positive)
                markPositiveEvery(be.rightExpression, positive)
            } else if (be.operation.text == '==>') {
                markPositiveEvery(be.leftExpression, !positive)   // antecedent flips
                markPositiveEvery(be.rightExpression, positive)
            }
            // other binary ops (comparisons, etc.) are not boolean-goal positions — stop here.
        } else if (e instanceof TernaryExpression) {
            TernaryExpression te = (TernaryExpression) e
            markPositiveEvery(te.trueExpression, positive)
            markPositiveEvery(te.falseExpression, positive)
        }
    }

    /** True if {@code e} is {@code <iterate-source>[.limit/.take(n)].every|any{ … }} — an infinite-stream quantifier. */
    private boolean isStreamEveryCall(Expression e) {
        if (!(e instanceof MethodCallExpression)) return false
        MethodCallExpression mc = (MethodCallExpression) e
        String m = mc.methodAsString
        if (m != 'every' && m != 'any') return false
        List<Expression> a = argList(mc)
        if (a.size() != 1 || !(a.get(0) instanceof ClosureExpression)) return false
        return parseStreamSource(unwrapImmutableWrap(mc.objectExpression)) != null
    }

    /**
     * Recognise an {@code iterate(seed, f)[.limit(n)|.take(n)]} chain — the generator shape behind an
     * infinite {@code Stream}/iterator. Returns {@code [seed, fClosure, limitExpr-or-null]}, or null.
     * The holder of {@code iterate} is not pinned (works for {@code Stream}/{@code IntStream}/a GDK
     * iterator); we key on the method shape: {@code iterate(seed, oneArgClosure)}.
     */
    private Expression[] parseStreamSource(Expression recv) {
        if (recv == null) return null
        Expression inner = recv
        Expression limit = null
        if (recv instanceof MethodCallExpression) {
            MethodCallExpression mc = (MethodCallExpression) recv
            String m = mc.methodAsString
            if (m == 'limit' || m == 'take') {
                List<Expression> la = argList(mc)
                if (la.size() == 1) { limit = la.get(0); inner = unwrapImmutableWrap(mc.objectExpression) }
            }
        }
        String im = null
        List<Expression> ia = null
        if (inner instanceof MethodCallExpression) {
            im = ((MethodCallExpression) inner).methodAsString
            ia = argList((MethodCallExpression) inner)
        } else if (inner instanceof StaticMethodCallExpression) {
            im = ((StaticMethodCallExpression) inner).method
            ia = exprsOf(((StaticMethodCallExpression) inner).arguments)
        }
        if (im != 'iterate' || ia == null || ia.size() != 2 || !(ia.get(1) instanceof ClosureExpression)) return null
        return [ia.get(0), ia.get(1), limit] as Expression[]
    }

    /**
     * Translate {@code iterate(seed, f).limit(n).every|any{ P }} (Phase 75). A {@code .limit(n)}/{@code .take(n)}
     * is <em>required</em> (see the runtime-termination note in the body); given one, two regimes:
     * <ul>
     *   <li><b>bounded unroll</b> — a literal {@code .limit(N)} (N ≤ {@link #STREAM_UNROLL_CAP}) expands to
     *       {@code ⋀ₖ P(fᵏ(seed))} (or {@code ⋁} for {@code any}); an <em>exact</em> equivalence — it proves
     *       exactly the bounded contract the runtime checks, and a failing element gives a counterexample.</li>
     *   <li><b>induction</b> — a <em>symbolic</em> or large limit: {@code every{P}} becomes
     *       {@code P(seed) ∧ ∀x. (P(x) ⟹ P(f(x)))} — base + preservation, the same induction the loop VCs do.
     *       This proves P for <em>all</em> elements (hence for the runtime's actual {@code n}, whatever it is) —
     *       the verifier reaching past the runtime's spot-check depth. It is <em>stronger</em> than the bounded
     *       {@code every} (sufficient, not necessary), so it is emitted only in positive goal position
     *       ({@link #goalPositiveEvery}); {@code any} (an existential) is not provable this way and skips.</li>
     * </ul>
     * Int-element streams only (a decimal/FP seed skips). Returns null (loud skip / fall-through) otherwise.
     */
    private Object translateStreamEvery(MethodCallExpression mce, Expression recv, ClosureExpression pred, boolean existential) {
        Expression[] src = parseStreamSource(recv)
        if (src == null) return null
        Expression seed = src[0]
        ClosureExpression f = (ClosureExpression) src[1]
        Expression limit = src[2]
        if (isDecimalExpr(seed) || isFpValued(seed)) return null   // Int-element streams only, this slice

        // Dual runtime+verify: groovy-contracts compiles this contract into an *eager* runtime assert, so a
        // terminal `every`/`any` over an unbounded source would loop forever at runtime (a true `every`
        // never short-circuits). We therefore require a `.limit(n)`/`.take(n)` bound — that is what lets the
        // contract degrade to a terminating runtime spot-check. Without one, skip loudly (it must not be
        // blessed as a verified-but-hanging contract). The bound's *value* is the runtime's spot-check
        // depth; the verifier still proves far beyond it (all elements, by induction below).
        if (limit == null) return null

        Integer litN = constIntLimit(limit)
        if (litN != null && litN >= 0 && litN <= STREAM_UNROLL_CAP) {
            // Bounded unroll — exact.
            Object cur = translate(seed)
            if (cur == null) return null
            List<Object> terms = new ArrayList<Object>()
            for (int k = 0; k < litN; k++) {
                Object pk = evalClosure(pred, cur)
                if (pk == null) return null
                terms.add(pk)
                if (k < litN - 1) {
                    cur = evalClosure(f, cur)
                    if (cur == null) return null
                }
            }
            if (terms.isEmpty()) {                       // limit(0): empty stream — every⇒true, any⇒false
                Object tru = session.le(session.intLit(0L), session.intLit(0L))
                return existential ? session.not(tru) : tru
            }
            return existential ? session.or(terms) : session.and(terms)
        }

        // Induction — symbolic / large limit (runtime checks the actual n; we prove all elements).
        // Universal only, positive goal only.
        if (existential) return null
        if (!goalPositiveEvery.contains(mce)) return null
        Object seedTerm = translate(seed)
        if (seedTerm == null) return null
        Object base = evalClosure(pred, seedTerm)                 // P(seed)
        if (base == null) return null
        Object x = session.boundIntVar('gvStream$' + (quantCounter++))
        Object px = evalClosure(pred, x)                          // P(x)
        Object fx = evalClosure(f, x)                             // f(x)
        if (px == null || fx == null) return null
        Object pfx = evalClosure(pred, fx)                        // P(f(x))
        if (pfx == null) return null
        Object step = session.forall([x], session.implies(px, pfx), new ArrayList<Object>())
        return session.and([base, step])
    }

    /** Evaluate a one-parameter closure body with its parameter bound to {@code argTerm} (an SMT handle). */
    private Object evalClosure(ClosureExpression clo, Object argTerm) {
        String p = closureParamName(clo)
        Expression body = singleExprOf(clo?.code)
        if (p == null || body == null || argTerm == null) return null
        Object prev = env.get(p)
        env.put(p, argTerm)
        try {
            return translate(body)
        } finally {
            if (prev == null) env.remove(p) else env.put(p, prev)
        }
    }

    /** The literal int value of a {@code .limit(n)} argument, or null for an absent / non-literal (symbolic) bound. */
    private static Integer constIntLimit(Expression limit) {
        if (limit == null) return null
        if (limit instanceof ConstantExpression && ((ConstantExpression) limit).value instanceof Number) {
            return ((Number) ((ConstantExpression) limit).value).intValue()
        }
        null
    }

    private static List<Expression> exprsOf(Expression a) {
        if (a instanceof ArgumentListExpression) return ((ArgumentListExpression) a).expressions
        if (a instanceof TupleExpression) return ((TupleExpression) a).expressions
        return Collections.<Expression> emptyList()
    }

    /**
     * Native GDK quantifier idioms (Phase 9), each a bounded universal:
     * <ul>
     *   <li>{@code (lo..<hi).every { … }} / {@code (lo..hi).every { … }} — over the index range;</li>
     *   <li>{@code xs.indices.every { … }} — over {@code [0, xs.size)};</li>
     *   <li>{@code xs.every { it … }} — over the <em>elements</em>: the closure parameter is
     *       {@code (select xs i)}, the universal ranging {@code i} over {@code [0, xs.size)}.</li>
     * </ul>
     * These read like ordinary Groovy and stay runtime-evaluable, so the groovy-contracts check
     * still works. Returns null for any other receiver shape — a loud skip, never a silent pass.
     */
    private Object translateBoundedQuantifier(Expression recv, ClosureExpression clo, boolean existential) {
        String pname = closureParamName(clo)
        Expression bodyExpr = singleExprOf(clo?.code)
        if (pname == null || bodyExpr == null) return null

        // (lo..<hi).every|any / (lo..hi).every|any  -> index over the range
        if (recv instanceof RangeExpression) {
            RangeExpression re = (RangeExpression) recv
            Object loH = translate(re.from)
            Object hiH = translate(re.to)
            if (loH == null || hiH == null) return null
            // A `..` range is inclusive; normalise to the half-open [lo, hi) the encoder uses.
            if (re.inclusive) hiH = session.plus(hiH, session.intLit(1L))
            return emitQuantifier(pname, loH, hiH, bodyExpr, null, existential)
        }

        // xs.indices.every|any  -> index over [0, xs.size)
        if (recv instanceof PropertyExpression) {
            PropertyExpression pe = (PropertyExpression) recv
            if (pe.propertyAsString == 'indices' && pe.objectExpression instanceof VariableExpression) {
                String xs = ((VariableExpression) pe.objectExpression).name
                return emitQuantifier(pname, session.intLit(0L), sizeOf(xs), bodyExpr, null, existential)
            }
            return null
        }

        // xs.every|any { it … }  -> element over [0, xs.size); the parameter is the element xs[i]
        if (recv instanceof VariableExpression) {
            String xs = ((VariableExpression) recv).name
            return emitQuantifier(pname, session.intLit(0L), sizeOf(xs), bodyExpr, arrayFor(xs), existential)
        }

        return null
    }

    private Object emitForall(String pname, Object loH, Object hiH, Expression bodyExpr, Object elementArr) {
        emitQuantifier(pname, loH, hiH, bodyExpr, elementArr, false)
    }

    /**
     * Emit a bounded quantifier over the closure's parameter, binding it while the body translates
     * — shadowing any same-named variable in scope, restored afterwards. {@code existential=false}
     * gives {@code ∀ i. (lo <= i < hi) ⇒ body}; {@code existential=true} gives
     * {@code ∃ i. (lo <= i < hi) ∧ body}. When {@code elementArr} is non-null the parameter is an
     * <em>element</em>, bound to {@code (select arr i)} (also the instantiation trigger); otherwise it
     * is the index {@code i} and the body's own {@code (select arr i)} terms become the triggers.
     */
    private Object emitQuantifier(String pname, Object loH, Object hiH, Expression bodyExpr,
                                  Object elementArr, boolean existential) {
        if (loH == null || hiH == null) return null
        Object iv = session.boundIntVar(pname + '$q' + (quantCounter++))
        List<Object> triggers = new ArrayList<Object>()
        Object binding = iv
        if (elementArr != null) {
            Object sel = session.select(elementArr, iv)
            triggers.add(sel)
            binding = sel
        }
        Object prevBinding = env.get(pname)
        List<Object> prevSink = triggerSink
        env.put(pname, binding)
        triggerSink = triggers
        try {
            Object bodyH = translate(bodyExpr)
            if (bodyH == null) return null
            Object range = session.and([session.le(loH, iv), session.lt(iv, hiH)])
            if (existential) {
                return session.exists([iv], session.and([range, bodyH]), triggers)
            }
            return session.forall([iv], session.implies(range, bodyH), triggers)
        } finally {
            triggerSink = prevSink
            if (prevBinding == null) env.remove(pname) else env.put(pname, prevBinding)
        }
    }

    /** True if {@code e} is the {@code this} receiver of an instance-field access. */
    private static boolean isThisReceiver(Expression e) {
        e instanceof VariableExpression && ((VariableExpression) e).name == 'this'
    }

    /** True if {@code e} is the {@code old} map of a postcondition ({@code old.field}). */
    static boolean isOldReceiver(Expression e) {
        e instanceof VariableExpression && ((VariableExpression) e).name == 'old'
    }

    /** The array-content handle for a named array {@code xs} or the entry snapshot {@code old.xs}; null otherwise. */
    private Object arrayHandleFor(Expression recv) {
        if (recv instanceof VariableExpression) {
            return arrayFor(((VariableExpression) recv).name)
        }
        if (recv instanceof PropertyExpression && isOldReceiver(((PropertyExpression) recv).objectExpression)) {
            return arrayFor('old$' + ((PropertyExpression) recv).propertyAsString)
        }
        null
    }

    /**
     * Phase 41 — the canonical array-name for a receiver shape, mirroring {@link #arrayHandleFor}:
     * a bare {@code xs} returns {@code "xs"}; an {@code old.xs} snapshot returns {@code "old$xs"}.
     * Used by the {@code .count} dispatch to decide bounded vs unbounded count and to look up
     * the right {@code sizeOf} oracle.
     */
    private static String receiverArrayName(Expression recv) {
        if (recv instanceof VariableExpression) {
            return ((VariableExpression) recv).name
        }
        if (recv instanceof PropertyExpression && isOldReceiverStatic(((PropertyExpression) recv).objectExpression)) {
            return 'old$' + ((PropertyExpression) recv).propertyAsString
        }
        null
    }

    /** Static mirror of {@link #isOldReceiver} for use from static helpers. */
    private static boolean isOldReceiverStatic(Expression e) {
        e instanceof VariableExpression && ((VariableExpression) e).name == 'old'
    }

    /** The closure's single parameter name, or Groovy's implicit {@code it}; null if it has several. */
    private static String closureParamName(ClosureExpression clo) {
        if (clo == null) return null
        Parameter[] ps = clo.parameters
        if (ps == null || ps.length == 0) return 'it'
        if (ps.length == 1) return ps[0].name
        return null
    }

    /** The single expression a closure/contract body reduces to, or null if it isn't a lone expression. */
    private static Expression singleExprOf(Statement code) {
        if (code instanceof BlockStatement) {
            List<Statement> ss = ((BlockStatement) code).statements
            return ss.size() == 1 ? singleExprOf(ss.get(0)) : null
        }
        if (code instanceof ExpressionStatement) return ((ExpressionStatement) code).expression
        if (code instanceof ReturnStatement) return ((ReturnStatement) code).expression
        return null
    }

    /** The reference operand of a {@code x == null}/{@code x != null}, or null if neither shape. */
    private static VariableExpression nullComparisonTarget(BinaryExpression be) {
        if (isNullLiteral(be.rightExpression) && be.leftExpression instanceof VariableExpression) {
            return (VariableExpression) be.leftExpression
        }
        if (isNullLiteral(be.leftExpression) && be.rightExpression instanceof VariableExpression) {
            return (VariableExpression) be.rightExpression
        }
        return null
    }

    /** Phase 37 — a recognised indexed access ({@code xs[i]} or {@code xs.get(i)}). Public so {@code VerifyChecker.Collect} can spot deref sites by the same rule the contract translation uses. */
    @CompileStatic static class IndexedNullTarget {
        String containerName
        Expression indexExpr
    }

    /** Recognise {@code xs[i] == null} / {@code null == xs[i]} (and {@code .get(i)} mirror); returns the indexed-access target. */
    private static IndexedNullTarget indexedNullComparisonTarget(BinaryExpression be) {
        Expression maybeIdx
        if (isNullLiteral(be.rightExpression)) maybeIdx = be.leftExpression
        else if (isNullLiteral(be.leftExpression)) maybeIdx = be.rightExpression
        else return null
        return indexedAccessTarget(maybeIdx)
    }

    /**
     * If {@code e} is {@code xs[i]} (BinaryExpression with LEFT_SQUARE_BRACKET) or {@code xs.get(i)}
     * over a named container, return its {@link IndexedNullTarget}; null otherwise. The check is
     * shape-based and permissive — any name with a single-arg subscript / get call qualifies —
     * since the implicit deref obligation depends on the *use*, not on declared type metadata.
     */
    static IndexedNullTarget indexedAccessTarget(Expression e) {
        if (e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e
            if (be.operation.type == Types.LEFT_SQUARE_BRACKET &&
                be.leftExpression instanceof VariableExpression) {
                IndexedNullTarget t = new IndexedNullTarget()
                t.containerName = ((VariableExpression) be.leftExpression).name
                t.indexExpr = be.rightExpression
                return t
            }
        }
        if (e instanceof MethodCallExpression) {
            MethodCallExpression mce = (MethodCallExpression) e
            if (mce.methodAsString == 'get' && mce.objectExpression instanceof VariableExpression) {
                List<Expression> args = argList(mce)
                if (args.size() == 1) {
                    IndexedNullTarget t = new IndexedNullTarget()
                    t.containerName = ((VariableExpression) mce.objectExpression).name
                    t.indexExpr = args.get(0)
                    return t
                }
            }
        }
        return null
    }

    private static boolean isNullLiteral(Expression e) {
        e instanceof ConstantExpression && ((ConstantExpression) e).value == null
    }

    private static List<Expression> argList(MethodCallExpression mce) {
        Expression a = mce.arguments
        if (a instanceof ArgumentListExpression) return ((ArgumentListExpression) a).expressions
        if (a instanceof TupleExpression) return ((TupleExpression) a).expressions
        return Collections.<Expression> emptyList()
    }

}
