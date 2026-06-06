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
import org.codehaus.groovy.ast.expr.CastExpression
import org.codehaus.groovy.ast.expr.ListExpression
import org.codehaus.groovy.ast.expr.MapEntryExpression
import org.codehaus.groovy.ast.expr.MapExpression
import org.codehaus.groovy.ast.expr.ClassExpression
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.expr.ConstantExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.GStringExpression
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
            Map<String, Integer> enumDomainSizes = null,
            Map<String, ClassNode> nestedSetValueTypes = null,
            Set<String> listNames = null,
            Map<String, ClassNode> objectParams = null) {
        this.session = session
        this.pureEvaluator = pureEvaluator
        this.setElementTypes = setElementTypes != null ? setElementTypes : new HashMap<String, ClassNode>()
        this.mapTypes = mapTypes != null ? mapTypes : new HashMap<String, ClassNode[]>()
        this.listElementTypes = listElementTypes != null ? listElementTypes : new HashMap<String, ClassNode>()
        this.scalarTypes = scalarTypes != null ? scalarTypes : new HashMap<String, ClassNode>()
        this.enumDomainSizes = enumDomainSizes != null ? enumDomainSizes : new HashMap<String, Integer>()
        this.nestedSetValueTypes = nestedSetValueTypes != null ? nestedSetValueTypes : new HashMap<String, ClassNode>()
        this.listNames = listNames != null ? listNames : new HashSet<String>()
        this.objectParams = objectParams != null ? objectParams : new LinkedHashMap<String, ClassNode>()
    }

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
        List<org.codehaus.groovy.ast.FieldNode> fs = t.fields
        if (fs != null) for (org.codehaus.groovy.ast.FieldNode f : fs) out.add(f.name)
        out
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
                 m == 'toUpperCase' || m == 'toLowerCase') &&
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
            return varForRaw(receiverPrefix + '$' + name)
        }
        // Phase 27 step 9 — a non-Int scalar (String, Enum) parameter/field dispatches to
        // varForOfSort, which caches in sortedEnv. The standard env stays Int-only so the
        // counterexample model walk (which iterates Z3Backend.vars) keeps pinning Int values
        // unchanged for everything else.
        ClassNode declared = scalarTypes.get(name)
        if (declared != null) {
            Object sort = sortFor(declared)
            if (sort != session.intSort()) return varForOfSort(name, sort)
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
        for (org.codehaus.groovy.ast.FieldNode f : t.fields) {
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
        boolean isUnion           // true = union (+); false = intersection (.intersect)
    }

    /** True if {@code e} is a known set union/intersection — see {@link SetBinop}. Null otherwise. */
    private SetBinop setBinopFor(Expression e) {
        // Unwrap an outer cast — e.g. `a.intersect(b) as Set<Role>` (Groovy's GDK intersect returns
        // Collection, so a Set-typed target needs the explicit cast). The cast doesn't change the
        // set semantics; the wrapped expression is the one we recognise.
        if (e instanceof CastExpression) e = ((CastExpression) e).expression
        if (e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e
            if (be.operation.type == Types.PLUS) {
                return tryMakeSetBinop(be.leftExpression, be.rightExpression, true)
            }
        }
        if (e instanceof MethodCallExpression) {
            MethodCallExpression mce = (MethodCallExpression) e
            if (mce.methodAsString == 'intersect' && argList(mce).size() == 1) {
                return tryMakeSetBinop(mce.objectExpression, argList(mce).get(0), false)
            }
        }
        null
    }

    private SetBinop tryMakeSetBinop(Expression leftExpr, Expression rightExpr, boolean isUnion) {
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
        b.isUnion = isUnion
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
            Object rhsExpr = binop.isUnion ? session.or([inA, inB]) : session.and([inA, inB])
            session.assertExpr(session.eq(inU, rhsExpr))
        }
        true
    }

    private Object translateContainsAllOnBinop(SetBinop binop, Expression uExpr) {
        String uKey = setKeyFor(uExpr)
        if (uKey == null) return null
        if (setKeySortForKey(uKey) != binop.elemSort) return null
        // Enum-only for the binop case (Int would need a bound on u — Phase 31's plumbing applied
        // to a binop receiver; small follow-up but not in this slice).
        ClassNode elemType = binop.elemType
        if (elemType == null || !(elemType.isEnum() || isEnumLikeType(elemType))) return null
        Object sH = setFor(binop.leftKey)
        Object tH = setFor(binop.rightKey)
        Object uH = setFor(uKey)
        Object enumSort = session.declareSort(enumSortName(elemType))
        List<Object> conjuncts = new ArrayList<Object>()
        for (String constName : enumConstantNames(elemType)) {
            Object constLit = session.litOfSort(enumSort, constName)
            Object inS = member(sH, constLit)
            Object inT = member(tH, constLit)
            Object rhs = binop.isUnion ? session.or([inS, inT]) : session.and([inS, inT])
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
        if (f == null) return false
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

        // Phase 46e — {@code (int) "hello".charAt(0)} bridges Groovy's char-vs-int distinction
        // at the return path: charAt returns char, the method may return int, so the user adds
        // a numeric cast. The verifier treats the cast as transparent — the inner term's sort
        // is already Int — and translates through.
        if (expr instanceof CastExpression) {
            return translate(((CastExpression) expr).expression)
        }

        // Phase 47h — GString interpolation. {@code "hello $name"} parses as a
        // {@link GStringExpression} with parallel lists of static strings and interpolated
        // values; translate to chained {@code stringConcat} via Z3's seq theory. Each value
        // is converted to its String representation via {@link #translateValueAsString} —
        // String values flow directly, integers go through {@code intToString}, others skip.
        if (expr instanceof GStringExpression) {
            return translateGString((GStringExpression) expr)
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
                        return varForRaw(recvName + '$' + prop)
                    }
                }
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
            // Phase 38 — `[a, b, c][i]` / `Map.of(k, v)[k']` / `[k:v][k']`: factory receiver
            // peephole-folds to the i-th element (for constant i) or an ite-chain over entries.
            FactoryContainer factoryL = factoryContainerFor(be.leftExpression)
            if (factoryL != null) {
                if (factoryL.kind == 'list')
                    return foldFactoryListIndex(factoryL.args, be.rightExpression)
                if (factoryL.kind == 'map')
                    return foldFactoryMapLookup(factoryL, be.rightExpression)
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
                Object mem = binop.isUnion ? session.or([lMem, rMem]) : session.and([lMem, rMem])
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

        Object L = translate(be.leftExpression)
        Object R = translate(be.rightExpression)
        if (L == null || R == null) return null
        // Phase 48 — operator-text dispatch for {@code /} and {@code %}: Groovy's parser
        // assigns {@code %} a token outside {@code Types.MOD} (same caveat ObligationCollector
        // notes), so {@code op.text} is the robust key. Used for both div and mod for parity
        // with the existing divide-site collection logic.
        String opText = be.operation.text
        if (opText == '/' || opText == '\\') {
            return session.intDiv(L, R)
        }
        if (opText == '%') {
            return session.intMod(L, R)
        }
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
        // Phase 38c — strip a transparent immutability wrapper on the receiver so subsequent
        // dispatch sees the inner expression directly. Idempotent for non-wrapper receivers.
        Expression recv = unwrapImmutableWrap(mce.objectExpression)
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
                return binop.isUnion ? session.or([lMem, rMem]) : session.and([lMem, rMem])
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
            // Phase 47b — {@code s.replace(old, new)} — first-occurrence replacement via
            // Z3's {@code str.replace}. Groovy/Java define {@code replace} as replace-all; this
            // is a known semantic gap until Z3 ships {@code mkReplaceAll}. Tests deliberately
            // use single-occurrence patterns where first/all coincide.
            if (m == 'replace' && args.size() == 2) {
                Object oldSub = translateInSort(args.get(0), strSort)
                Object newSub = translateInSort(args.get(1), strSort)
                if (oldSub == null || newSub == null) return null
                return session.stringReplace(sH, oldSub, newSub)
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
            // Phase 47f — {@code s.replaceAll(old, new)} as uninterpreted with weak axioms.
            // The verifier knows non-occurrence is a no-op and same-length-replacement preserves
            // length, nothing else. Sound under-approximation.
            if (m == 'replaceAll' && args.size() == 2) {
                Object oldSub = translateInSort(args.get(0), strSort)
                Object newSub = translateInSort(args.get(1), strSort)
                if (oldSub == null || newSub == null) return null
                return session.stringReplaceAll(sH, oldSub, newSub)
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
