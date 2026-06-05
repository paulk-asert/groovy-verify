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
import org.codehaus.groovy.ast.Parameter
import org.codehaus.groovy.ast.expr.ArgumentListExpression
import org.codehaus.groovy.ast.expr.BinaryExpression
import org.codehaus.groovy.ast.expr.BooleanExpression
import org.codehaus.groovy.ast.expr.ClassExpression
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.NotExpression
import org.codehaus.groovy.ast.expr.PropertyExpression
import org.codehaus.groovy.ast.expr.RangeExpression
import org.codehaus.groovy.ast.expr.StaticMethodCallExpression
import org.codehaus.groovy.ast.expr.TernaryExpression
import org.codehaus.groovy.ast.expr.TupleExpression
import org.codehaus.groovy.ast.expr.UnaryMinusExpression
import org.codehaus.groovy.ast.expr.UnaryPlusExpression
import org.codehaus.groovy.ast.expr.VariableExpression
import org.codehaus.groovy.ast.stmt.BlockStatement
import org.codehaus.groovy.ast.stmt.ExpressionStatement
import org.codehaus.groovy.ast.stmt.ReturnStatement
import org.codehaus.groovy.ast.stmt.Statement
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

    Encoder(SmtSession session, PureEvaluator pureEvaluator = null,
            Map<String, ClassNode> setElementTypes = null,
            Map<String, ClassNode[]> mapTypes = null,
            Map<String, ClassNode> listElementTypes = null,
            Map<String, ClassNode> scalarTypes = null,
            Map<String, Integer> enumDomainSizes = null) {
        this.session = session
        this.pureEvaluator = pureEvaluator
        this.setElementTypes = setElementTypes != null ? setElementTypes : new HashMap<String, ClassNode>()
        this.mapTypes = mapTypes != null ? mapTypes : new HashMap<String, ClassNode[]>()
        this.listElementTypes = listElementTypes != null ? listElementTypes : new HashMap<String, ClassNode>()
        this.scalarTypes = scalarTypes != null ? scalarTypes : new HashMap<String, ClassNode>()
        this.enumDomainSizes = enumDomainSizes != null ? enumDomainSizes : new HashMap<String, Integer>()
    }

    /**
     * The Z3 sort for a Groovy element type. Int / Integer → the built-in Int sort (the existing
     * default); String → the uninterpreted {@code String!Sort}; an enum class → a per-class
     * uninterpreted sort named after the enum's nameWithoutPackage. {@code null} or any other type
     * falls back to Int (the default-Int policy preserves today's behaviour for unannotated
     * receivers). Used by {@link #setElementSort} / {@link #mapKeySort} / {@link #mapValueSort} /
     * {@link #listElementSort}.
     */
    private Object sortFor(ClassNode t) {
        if (t == null) return session.intSort()
        String name = t.name
        if (name == 'java.lang.String') return session.declareSort('String')
        if (isIntLikeType(t)) return session.intSort()
        if (t.isEnum() || isEnumLikeType(t)) return session.declareSort(enumSortName(t))
        session.intSort()   // default — preserves today's Int-only behaviour for unrecognised types
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
        for (org.codehaus.groovy.ast.FieldNode f : t.fields) {
            if ((f.modifiers & 0x4000) != 0) count++   // 0x4000 = ACC_ENUM
        }
        count
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
    /** The Z3 sort for a map receiver's value type. */
    Object mapValueSort(String name) {
        ClassNode[] pair = mapTypes.get(name)
        sortFor(pair != null ? pair[1] : null)
    }
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
        // Phase 27 step 9 — a non-Int scalar (String, Enum) parameter/field dispatches to
        // varForOfSort, which caches in sortedEnv. The standard env stays Int-only so the
        // counterexample model walk (which iterates Z3Backend.vars) keeps pinning Int values
        // unchanged for everything else.
        ClassNode declared = scalarTypes.get(name)
        if (declared != null) {
            Object sort = sortFor(declared)
            if (sort != session.intSort()) return varForOfSort(name, sort)
        }
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
        String key = name + ':' + sort.toString()
        Object cached = sortedEnv.get(key)
        if (cached != null) return cached
        Object v = session.varOfSort(name, sort)
        sortedEnv.put(key, v)
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

    /** Explicit binding, used to wire formal parameters to actual-argument expressions. */
    void bind(String name, Object handle) {
        env.put(name, handle)
    }

    /** Current scalar/array binding, or null if unbound — for save/restore around a call's framing. */
    Object peekVar(String name) { env.get(name) }
    Object peekArray(String name) { arrEnv.get(name) }

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
        session.assertExpr(session.ge(v, session.intLit(0L)))  // a size is never negative
        sizeEnv.put(key, v)
        v
    }

    /** True if a size oracle has already been minted for {@code recv} (i.e. a contract referenced its size). */
    boolean hasSizeOracle(String recv) { sizeEnv.containsKey(recv + '.size') }

    /** True if a nullity oracle has already been minted for {@code recv}. */
    boolean hasNullityOracle(String recv) { nullEnv.containsKey(recv) }

    /**
     * Get-or-declare the array-content handle for a source-level name. Shares its
     * key with nothing else — the size oracle ({@link #sizeOf}) bounds the valid
     * index range, this models the element values. Element sort dispatch via
     * {@link #arrayElementSortFor} (Phase 27): a non-Int element list or a non-Int
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
            ClassNode[] pair = mapTypes.get(logical)
            return [sortFor(pair != null ? pair[0] : null),
                    sortFor(pair != null ? pair[1] : null)] as Object[]
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
     * enum-domain {@code Sets.bounded}/{@code Sets.count} specialisation.
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
        for (org.codehaus.groovy.ast.FieldNode f : t.fields) {
            if ((f.modifiers & 0x4000) != 0) names.add(f.name)
        }
        names
    }

    /**
     * Phase 29 — try to fold {@code e} to a {@code Long} at translate time. Recognises ordinary
     * integer ConstantExpressions and the Phase 28 {@code <EnumClass>.values().length} /
     * {@code .size()} shapes. Used to detect whether a {@code Sets.bounded}/{@code Sets.count}
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
     * Phase 30 — lower {@code s.containsAll(t)} to the finite conjunction
     * {@code ∧ (c_i ∈ t ⟹ c_i ∈ s)} over the enum domain when both sets share an enum element
     * sort. Returns null for Int/String/sort-mismatch or when the receiving set isn't an enum
     * set — the caller treats null as "outside fragment" and falls through to skip. Int-element
     * subset needs a bounded-domain context (Sets.bounded on the subset operand) and is a
     * separate, larger increment.
     */
    private Object translateContainsAll(String sKey, Expression tExpr) {
        String tKey = setKeyFor(tExpr)
        if (tKey == null) return null
        Object sElemSort = setKeySortForKey(sKey)
        Object tElemSort = setKeySortForKey(tKey)
        if (sElemSort != tElemSort) return null   // sort mismatch
        ClassNode elemType = elementTypeForSetKey(sKey)
        if (elemType == null || !(elemType.isEnum() || isEnumLikeType(elemType))) return null
        Object sH = setFor(sKey)
        Object tH = setFor(tKey)
        Object enumSort = session.declareSort(enumSortName(elemType))
        List<Object> conjuncts = new ArrayList<Object>()
        for (String constName : enumConstantNames(elemType)) {
            Object constLit = session.litOfSort(enumSort, constName)
            conjuncts.add(session.implies(member(tH, constLit), member(sH, constLit)))
        }
        conjuncts.isEmpty() ? session.boolLit(true) : session.and(conjuncts)
    }

    /**
     * Phase 29 — finite-domain conjunction {@code c1 ∈ s ∧ c2 ∈ s ∧ ... ∧ cN ∈ s} over the
     * enum's constants. The encoder-side replacement for the Int-domain bounded universal
     * {@code ∀ i. 0<=i<n ⟹ i ∈ s}, used when {@code Sets.bounded}/{@code Sets.count} reach an
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

    /**
     * Translate a Groovy expression to an SMT handle. Returns null
     * if anything in the subtree is outside the fragment.
     */
    Object translate(Expression expr) {
        if (expr == null) return null

        if (expr instanceof ConstantExpression) {
            Object v = ((ConstantExpression) expr).value
            if (v instanceof Integer || v instanceof Long || v instanceof Short || v instanceof Byte) {
                return session.intLit(((Number) v).longValue())
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
            return varFor(name)
        }

        if (expr instanceof UnaryMinusExpression) {
            Object inner = translate(((UnaryMinusExpression) expr).expression)
            return inner == null ? null : session.neg(inner)
        }

        if (expr instanceof UnaryPlusExpression) {
            return translate(((UnaryPlusExpression) expr).expression)
        }

        if (expr instanceof NotExpression) {
            Object inner = translate(((NotExpression) expr).expression)
            return inner == null ? null : session.not(inner)
        }

        if (expr instanceof BooleanExpression) {
            // Groovy wraps if/while conditions in BooleanExpression
            return translate(((BooleanExpression) expr).expression)
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

        if (expr instanceof PropertyExpression) {
            PropertyExpression pe = (PropertyExpression) expr
            String prop = pe.propertyAsString
            Expression obj = pe.objectExpression
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
            // Phase 28 — `Color.values().length` folds to the literal enum-constant count, so a
            // contract like `Sets.bounded(s, Color.values().length)` or a body returning the count
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
            Object r = translateMethodCall((MethodCallExpression) expr)
            return r != null ? r : translateCall(expr)
        }

        // Phase 8a — a resolved static call (e.g. `C.pow2(n)`) only reaches the verifier
        // already in this form; try the pure-function paths (closed eval / unfolding).
        if (expr instanceof StaticMethodCallExpression) {
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

    private Object translateBinary(BinaryExpression be) {
        // Phase 8a — normalise-then-SMT: fold a closed numeric subexpression to a
        // literal before encoding. This dissolves the NIA opt-out for *constant*
        // products (e.g. `(2 + 2) * (2 + 2)`), which would otherwise be skipped.
        // Reuses Groovy's own constant folder, so the arithmetic semantics match.
        Object folded = tryFoldConstant(be)
        if (folded != null) return folded

        int op = be.operation.type

        // Array subscript a[i] -> (select a i). The element value, modelled under
        // Z3's array theory (Phase 6). Recorded as a trigger when inside a quantifier.
        // The base is a named array a, or old.a (the entry-snapshot array, keyed old$a).
        if (op == Types.LEFT_SQUARE_BRACKET) {
            // m[k] over a map reads its value array (key in map's key sort); a[i] over an array
            // or list reads its contents (index in Int). Phase 27: route map keys through the
            // declared key sort so a Map<String, Integer> can do m["admin"] cleanly.
            String mlog = mapLogicalFor(be.leftExpression)
            Object arr = mlog != null ? mapValsFor(mlog) : arrayHandleFor(be.leftExpression)
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
            String setKey = setKeyFor(be.rightExpression)
            String mapLog = setKey == null ? mapLogicalFor(be.rightExpression) : null
            if (setKey != null || mapLog != null) {
                Object elemSort = setKey != null ? setKeySortForKey(setKey) :
                                  sortFor(mapTypes.get(mapLog) != null ? mapTypes.get(mapLog)[0] : null)
                Object elem = translateInSort(be.leftExpression, elemSort)
                if (elem == null) return null
                Object setH = setKey != null ? setFor(setKey) : mapKeysFor(mapLog)
                Object mem = member(setH, elem)
                return sym == 'in' ? mem : session.not(mem)
            }
        }

        // Nullity: x == null / x != null, before we try to translate `null`.
        if (op == Types.COMPARE_EQUAL || op == Types.COMPARE_NOT_EQUAL) {
            VariableExpression ref = nullComparisonTarget(be)
            if (ref != null) {
                Object isNull = nullityOf(ref.name)
                return op == Types.COMPARE_EQUAL ? isNull : session.not(isNull)
            }
        }

        Object L = translate(be.leftExpression)
        Object R = translate(be.rightExpression)
        if (L == null || R == null) return null
        switch (op) {
            case Types.PLUS:                return session.plus(L, R)
            case Types.MINUS:               return session.minus(L, R)
            case Types.MULTIPLY:
                // Pure-NIA opt-out: refuse if BOTH sides are non-literal,
                // so the encoder stays in QF_LIA for the spike.
                if (!(be.leftExpression instanceof ConstantExpression) &&
                    !(be.rightExpression instanceof ConstantExpression)) {
                    return null
                }
                return session.times(L, R)
            case Types.COMPARE_EQUAL:       return session.eq(L, R)
            case Types.COMPARE_NOT_EQUAL:   return session.ne(L, R)
            case Types.COMPARE_LESS_THAN:           return session.lt(L, R)
            case Types.COMPARE_LESS_THAN_EQUAL:     return session.le(L, R)
            case Types.COMPARE_GREATER_THAN:        return session.gt(L, R)
            case Types.COMPARE_GREATER_THAN_EQUAL:  return session.ge(L, R)
            case Types.LOGICAL_AND:         return session.and([L, R])
            case Types.LOGICAL_OR:          return session.or([L, R])
            default:                        return null
        }
    }

    private Object translateMethodCall(MethodCallExpression mce) {
        String m = mce.methodAsString
        if (m == null) return null
        Expression recv = mce.objectExpression
        List<Expression> args = argList(mce)

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

        // Sets.bounded(s, n) — the cardinality axiom (Phase 19): a set bounded by the domain [0, n).
        // Lowered to card(s) <= n ∧ (card(s) < n ∨ ∀ i ∈ [0,n)· i ∈ s), a faithful boolean definition.
        // `Sets` reaches us three ways: a bare import (VariableExpression) and FQN `verification.Sets`
        // (PropertyExpression) in re-parsed contracts, and a resolved ClassExpression when it appears in a
        // method *body* (e.g. a loop guard `Sets.count(...) < n`).
        boolean isSets = (recv instanceof VariableExpression && ((VariableExpression) recv).name == 'Sets') ||
                         (recv instanceof PropertyExpression && ((PropertyExpression) recv).propertyAsString == 'Sets') ||
                         (recv instanceof ClassExpression && ((ClassExpression) recv).type?.nameWithoutPackage == 'Sets')
        if (m == 'bounded' && isSets && args.size() == 2) {
            return translateSetsBounded(args.get(0), args.get(1))
        }
        // Sets.count(s, k) — the bounded-sum cardinality as a primitive (Phase 21), carrying its bound
        // axiom and (at set mutations) the per-add law. The recursive Phase-20 spelling earns the same
        // bound by induction; this form threads across a mutation.
        if (m == 'count' && isSets && args.size() == 2) {
            String key = setKeyFor(args.get(0))
            if (key == null) return null
            Object elemSort = setKeySortForKey(key)
            Object kH = translate(args.get(1))
            if (kH == null) return null
            if (elemSort == session.intSort()) {
                return setCountOf(setFor(key), kH)
            }
            // Phase 29 — enum-element set: when k equals the enum's domain size,
            // Sets.count(s, k) is morally the set's cardinality (no partial-domain "first k
            // constants" ordering exists). Alias to cardOf — the pigeonhole + full-coverage iff
            // were asserted at setFor time, so the user-visible identity
            // `Sets.count(s, N) == N ⟺ every enum constant ∈ s` follows by the iff.
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
            // containsValue/keySet/values/putAll/etc. need an (unbounded) quantifier over the domain —
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
            // full-coverage). Int subset needs a bounded-domain context (Sets.bounded on t) to
            // close the universal — deferred until that plumbing lands; today it skips honestly.
            if (m == 'containsAll' && args.size() == 1) {
                Object q = translateContainsAll(setKey, args.get(0))
                if (q != null) return q
            }
            // union/intersect/etc. still need unbounded quantifiers — out of fragment, return null.
            return null
        }

        // xs.count(v) / old.a.count(v) -> the occurrence-count term (Phase 12, permutation). Its
        // value is governed by the per-store update law asserted in checkPath, not a literal value.
        if (m == 'count' && args.size() == 1 && !(args.get(0) instanceof ClosureExpression)) {
            Object arr = arrayHandleFor(recv)
            if (arr != null) {
                Object v = translate(args.get(0))
                if (v != null) return session.count(arr, v)
            }
        }

        // size() / isEmpty() / contains() need a named receiver for their oracle.
        if (!mce.implicitThis && recv instanceof VariableExpression) {
            String rn = ((VariableExpression) recv).name
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
     * {@link #unfoldFuel} is a per-encoder (≈ per-VC) total-unfold budget; it only decrements, which
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
        Object fSharp = session.uninterpretedFunc(c.name, handles)

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
     * Lower {@code Sets.bounded(s, n)} (the cardinality axiom) to
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
