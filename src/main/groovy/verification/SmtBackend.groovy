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

/**
 * Minimal SMT backend surface — just enough for the spike's
 * linear-integer + boolean fragment. The one implementation is
 * {@link Z3Backend}; the seam exists so {@link Encoder} can be written
 * against an interface rather than Z3 types directly.
 *
 * The fragment is deliberately small: integer variables, integer
 * literals, +/-/*-by-literal, comparisons, boolean and/or/not.
 * Anything else surfaces through {@link Encoder} as a
 * "fragment-not-supported" warning before it reaches the backend.
 */
@CompileStatic
interface SmtBackend {

    /** Opens a fresh assertion context. Caller must close(). */
    SmtSession session()
}

@CompileStatic
interface SmtSession extends AutoCloseable {

    /** Declare an integer variable; returns a backend-specific handle. */
    Object intVar(String name)

    /**
     * Declare a boolean variable; returns a backend-specific handle.
     * Used for nullity tracking (a reference's "is null" flag) — a separate
     * sort from the integer values the rest of the fragment lives in.
     */
    Object boolVar(String name)

    // ---- Non-Int element sorts (Phase 27) -------------------------------------------------
    // The original surface above is Int-only — every constant, array index/value, and set
    // element lives in {@code Int}. Phase 27 adds non-Int element domains (String, Enum) for
    // sets/maps/lists. Existing call sites stay unchanged; the new methods sit alongside.

    /**
     * The built-in integer sort — the existing surface above is implicitly typed here.
     * Returning it as a handle lets the Encoder mention {@code Int} uniformly when picking a
     * key/value/element sort for an array, without the backend leaking through.
     */
    Object intSort()

    /**
     * The Boolean sort, as an opaque handle. Lets the Encoder name {@code Bool} as the range of a
     * Boolean-returning pure function (so {@code leq(l1, l2)}-style predicates over a non-Int domain
     * can be declared via {@link #applyUF}), without the backend type leaking through.
     */
    Object boolSort()

    /**
     * Declare-or-get an uninterpreted sort by {@code name}. Idempotent — two calls with the
     * same name return the same handle, so a {@code Set<String>} in one method and a
     * {@code Set<String>} in another share the {@code String!Sort}. Used to model element types
     * the encoder doesn't otherwise interpret (a Groovy {@code String} or enum class) as a
     * decidable equality domain — Z3 reasons about distinctness, nothing else.
     */
    Object declareSort(String name)

    /** Declare a constant of the given sort — the polymorphic generalisation of {@link #intVar}. */
    Object varOfSort(String name, Object sort)

    /**
     * Declare-or-get a literal constant of the given sort, interned by {@code literalKey}. Two
     * calls with the same {@code (sort, literalKey)} pair return the same handle. On each new
     * mint within a sort, the new constant is asserted distinct from every previously-minted
     * constant of that sort — so {@code "a" != "b"} is a fact the solver knows, lazily and
     * pairwise (O(n) on the nth mint, O(n^2) total per sort — fine for the dozens-of-literals
     * scale the fragment expects).
     */
    Object litOfSort(Object sort, String literalKey)

    /**
     * Declare an array constant {@code Array key -> val} of arbitrary key/value sorts — the
     * polymorphic generalisation of {@link #arrayVar} ({@code Int -> Int}) and the eventual
     * home for set characteristic arrays {@code key -> Int} and map value-arrays {@code key -> val}.
     */
    Object arrayVarOfSort(String name, Object keySort, Object valSort)

    /**
     * Build the array sort {@code Array key -> val} as a value — *not* a constant of that sort.
     * Used to construct nested array sorts like {@code Array<K, Array<V, Int>>} for
     * {@code Map<K, Set<V>>} (Phase 36): the outer map's value sort needs to be the
     * characteristic-array sort of the inner set, but no Z3 constant is minted for the inner
     * sort itself — only the outer map handle binds a constant.
     */
    Object arraySort(Object keySort, Object valSort)

    /**
     * Apply a named uninterpreted integer function {@code Int^n -> Int} to its
     * arguments, declaring it on first use; two applications of the same
     * {@code name}/arity share one declaration. This is the "bottom" of bounded
     * symbolic unfolding (roadmap Phase 8a): a recursive pure-function call left
     * unexpanded once the fuel runs out is modelled as some unknown-but-fixed
     * integer, a sound over-approximation — the residual constrains the result
     * only through the fuel levels actually unfolded.
     */
    Object uninterpretedFunc(String name, List<Object> intArgs)

    /**
     * Phase A (higher-order) — apply an uninterpreted function {@code name} to {@code args}, declared
     * lazily from the args' actual sorts → {@code rangeSort}. Unlike {@link #uninterpretedFunc} (Int-only),
     * this works over any sorts, so a {@code java.util.function.Function} parameter's {@code f.apply(x)} can
     * be modelled as an uninterpreted map over a value sort. Sound by construction: the only fact asserted is
     * functional congruence (equal arguments yield equal results), nothing about what the function computes.
     */
    Object applyUF(String name, List<Object> args, Object rangeSort)

    /**
     * Phase B (carrier model) — a single-field immutable wrapper carrier (`@Monadic` Identity-shaped) as a
     * one-constructor datatype: {@code mk$type(content$type: contentSort)}. {@link #wrapperSort} declares it,
     * {@link #wrapperUnit} applies the constructor ("of"), {@link #wrapperContent} the selector (field read).
     * Z3's datatype theory supplies both round-trips automatically.
     */
    Object wrapperSort(String typeName, Object contentSort)
    Object wrapperUnit(String typeName, Object contentSort, Object value)
    Object wrapperContent(String typeName, Object contentSort, Object carrier)

    /**
     * Phase M-A (multi-case carriers) — an N-constructor algebraic datatype (the generalisation of the
     * single-constructor wrapper, for {@code Some(v) | None}-shaped carriers). {@code constructors} is a list of
     * {@code [String ctorName, List<[String fieldName, Object sort]> fields]}; a nullary constructor (like
     * {@code None}) has an empty field list. Z3's datatype theory then supplies the case-analysis, selector
     * round-trips ({@code content(some(v)) == v}), and constructor distinctness ({@code some(v) != none()}) for
     * free. {@link #datatypeConstruct} applies a constructor, {@link #datatypeSelect} a field selector, and
     * {@link #datatypeRecognize} the {@code is$Ctor} tester (a Bool).
     */
    Object datatypeSort(String typeName, List<Object[]> constructors)
    Object datatypeConstruct(String typeName, String ctorName, List<Object> args)
    Object datatypeSelect(String typeName, String ctorName, String fieldName, Object carrier)
    Object datatypeRecognize(String typeName, String ctorName, Object carrier)

    /**
     * Phase M-B — the distinguished {@code null} element of an (uninterpreted) value sort, minted once per sort.
     * It's an ordinary value of the sort (so a Vavr-style {@code Some(null)} is a real, distinct carrier), but it
     * is the element a function can map *to*, and the one an Optional-style {@code map} collapses to {@code None}.
     * {@code x == nullValue(sort)} is exactly the collapse predicate.
     */
    Object nullValue(Object valueSort)

    /** If-then-else over integer branches — Z3 {@code (ite cond thenV elseV)}. */
    Object ite(Object cond, Object thenV, Object elseV)

    /**
     * Declare an integer array variable {@code Array Int -> Int}, modelling the
     * *contents* of an array/list named {@code name}. The element at index
     * {@code i} is {@link #select}; an update is {@link #store}. Index and value
     * sorts are both Int — the spike's only modelled element type. (See
     * roadmap Phase 6.)
     */
    Object arrayVar(String name)

    /**
     * A constant {@code Int -> Int} array whose every element equals {@code value} — Z3's
     * {@code ((as const (Array Int Int)) value)}. Models a freshly-allocated {@code new int[n]},
     * which Java zero-fills, as the const-0 array (so an unwritten element reads its default).
     */
    Object constIntArray(Object value)

    /** The element {@code arr[i]} — Z3 {@code (select arr i)}. */
    Object select(Object arr, Object idx)

    /** The array equal to {@code arr} except index {@code idx} holds {@code val} — Z3 {@code (store arr idx val)}. */
    Object store(Object arr, Object idx, Object val)

    /**
     * Phase 41 — the bounded occurrence count {@code #{ i : lo <= i < hi ∧ arr[i] == v }} — an
     * uninterpreted {@code (Array, Int, Int, Int) -> Int} modelling Groovy's GDK
     * {@code list.count(v)} faithfully (the runtime call iterates {@code [0, size)}, not the
     * unbounded index domain {@link #count} models). Used by the encoder for List receivers; the
     * unbounded {@link #count} stays in place for arrays where size is fixed and the two
     * interpretations agree. Two applications with the same {@code (arr, v, lo, hi)} share the
     * term; the *meaning* comes from the per-store law on writes within {@code [lo, hi)} and the
     * boundary law on extensions / contractions of the range — emitted by the caller, not the backend.
     */
    Object bcount(Object arr, Object v, Object lo, Object hi)

    /**
     * The bounded sum of element *values* {@code sum(arr, lo, hi) = Σ_{lo <= i < hi} arr[i]} — an
     * uninterpreted {@code (Array, Int, Int) -> Int}. The value-sum analogue of {@link #bcount}'s
     * occurrence-count. Two applications with the same {@code (arr, lo, hi)} share the term; its
     * meaning comes from the base ({@code hi <= lo ⟹ sum == 0}) and step
     * ({@code lo < hi ⟹ sum(arr,lo,hi) == sum(arr,lo,hi-1) + arr[hi-1]}) axioms the caller asserts,
     * which let a loop invariant {@code s == sum(arr,0,i)} be preserved by {@code s = s + arr[i]}.
     */
    Object sum(Object arr, Object lo, Object hi)

    // Phase 70 — Real-element aggregation for List<BigDecimal>/decimal arrays: a Real-codomain bounded
    // sum over an {@code Array Int Real}, plus the Real sort and a sort test (so the encoder can avoid
    // double-coercing an already-Real handle, e.g. a decimal element read).
    Object realSort()
    Object sumReal(Object arr, Object lo, Object hi)   // (Array Int Real, Int, Int) -> Real
    boolean isReal(Object handle)
    boolean isInt(Object handle)                       // true if the term has the Int sort
    boolean isSeq(Object handle)                       // true if the term has the String/sequence sort
    boolean isBool(Object handle)                      // true if the term has the Boolean sort
    /** Phase 126 — evaluate {@code handle} in the most recent SAT model and render it for display
     *  (Int → number, String/Seq → quoted text), or null if there's no model / unsupported sort. */
    String evalDisplay(Object handle)

    // Phase 73 — IEEE-754 floating point (Z3's FP theory): faithful double/float, bit-exact with the
    // JVM runtime (round-nearest-even, NaN, ±inf, signed zero). Arithmetic rounds RNE; `fpEq` is IEEE
    // equality (NaN != NaN), distinct from structural eq. `isDouble` picks Float64 vs Float32.
    Object fpLit(double v, boolean isDouble)
    Object fpVar(String name, boolean isDouble)
    Object fpAdd(Object a, Object b)
    Object fpSub(Object a, Object b)
    Object fpMul(Object a, Object b)
    Object fpDiv(Object a, Object b)
    Object fpNeg(Object a)
    Object fpSqrt(Object a)             // RNE-rounded IEEE square root (sqrt of a negative is NaN)
    Object fpAbs(Object a)
    Object fpEq(Object a, Object b)     // IEEE == (NaN != NaN)
    Object fpLt(Object a, Object b)
    Object fpLeq(Object a, Object b)
    Object fpGt(Object a, Object b)
    Object fpGeq(Object a, Object b)
    Object fpIsNaN(Object a)
    Object fpIsInfinite(Object a)
    boolean isFp(Object handle)
    /** The IEEE-754 sort itself (Float64 / Float32) — for FP-element arrays (`double[]`/`List<Double>`). */
    Object fpSort(boolean isDouble)

    /**
     * The bounded product of element values {@code prod(arr, lo, hi) = Π_{lo <= i < hi} arr[i]} — the
     * multiplicative sibling of {@link #sum}. Meaning comes from the base ({@code hi <= lo ⟹ prod == 1},
     * the empty product) and step ({@code lo < hi ⟹ prod(arr,lo,hi) == prod(arr,lo,hi-1) * arr[hi-1]})
     * axioms the caller asserts. Recognised from the Groovy fold idiom {@code inject(1){ a, x -> a * x }}.
     */
    Object prod(Object arr, Object lo, Object hi)

    /**
     * The bounded *string concatenation* {@code concat(arr, lo, hi) = arr[lo] ++ … ++ arr[hi-1]} over a
     * {@code (Int -> String)} array — the String-monoid analogue of {@link #sum}, modelling Groovy's
     * duck-typed {@code ['a','b','c'].sum() == 'abc'}. Meaning from the base ({@code hi <= lo ⟹ concat ==
     * ""}) and step ({@code lo < hi ⟹ concat(arr,lo,hi) == concat(arr,lo,hi-1) ++ arr[hi-1]}, via
     * {@link #stringConcat}) axioms the caller asserts.
     */
    Object strConcatRange(Object arr, Object lo, Object hi)

    /**
     * The Fibonacci function {@code fib(k)} — an uninterpreted {@code Int -> Int}. Meaning from the base
     * ({@code fib(0)==0}, {@code fib(1)==1}) and step ({@code ∀k. k>=2 ⟹ fib(k)==fib(k-1)+fib(k-2)})
     * axioms the caller asserts (mint-once, globally). Recognised from the {@code Fib.of(i)} helper.
     */
    Object fib(Object k)

    /**
     * The tribonacci-style function {@code trib(k)} — an uninterpreted {@code Int -> Int} (HumanEval 063
     * {@code fibfib}). Meaning from base ({@code trib(0)==0}, {@code trib(1)==0}, {@code trib(2)==1}) and
     * step ({@code ∀k. k>=3 ⟹ trib(k)==trib(k-1)+trib(k-2)+trib(k-3)}) axioms the caller asserts
     * (mint-once, globally). Recognised from the {@code Trib.of(i)} helper — the three-term sibling of {@code fib}.
     */
    Object trib(Object k)

    /**
     * The fib4 / tetranacci-style function {@code tetra(k)} — an uninterpreted {@code Int -> Int} (HumanEval 046
     * {@code fib4}). Meaning from base ({@code tetra(0)==0}, {@code tetra(1)==0}, {@code tetra(2)==2},
     * {@code tetra(3)==0}) and step ({@code ∀k. k>=4 ⟹ tetra(k)==tetra(k-1)+tetra(k-2)+tetra(k-3)+tetra(k-4)})
     * axioms the caller asserts (mint-once, globally). Recognised from {@code Tetra.of(i)} — the four-term sibling.
     */
    Object tetra(Object k)

    /**
     * The greatest-common-divisor function {@code gcd(a, b)} — an uninterpreted {@code (Int, Int) -> Int}
     * (HumanEval 013 {@code greatest_common_divisor}). Meaning from Euclid's base ({@code ∀x. gcd(x, 0)==x})
     * and step ({@code ∀x,y. y!=0 ⟹ gcd(x, y)==gcd(y, x % y)}) axioms the caller asserts (mint-once,
     * globally). Recognised from the {@code Gcd.of(a, b)} helper — the two-argument sibling of {@code fib}.
     */
    Object gcd(Object a, Object b)

    /**
     * The least-common-multiple function {@code lcm(a, b)} — an uninterpreted {@code (Int, Int) -> Int}.
     * Meaning from the caller's base ({@code ∀a. lcm(a,0)==0}, {@code ∀b. lcm(0,b)==0}) and the fundamental
     * identity {@code ∀a,b. lcm(a,b) * gcd(a,b) == a * b} axioms (so it composes with {@link #gcd}).
     * Recognised from the {@code Lcm.of(a, b)} helper.
     */
    Object lcm(Object a, Object b)

    /**
     * Integer exponentiation {@code base ** exp} — an uninterpreted {@code (Int, Int) -> Int}. Z3 has no
     * variable-exponent power in its arithmetic theory, so this carries no value axioms: two applications
     * with the same {@code (base, exp)} share the term (congruence), so {@code result == base ** exp}
     * proves, while value properties (e.g. {@code 2 ** n >= 1}) honestly stay "could not decide". First
     * slice of {@code **} (Groovy's power returns {@code Number}, so the surface is {@code (b ** e).intValue()}).
     */
    Object pow(Object base, Object exp)

    /**
     * The occurrence count {@code #{ i : arr[i] == v }} — an uninterpreted {@code (Array, Int) -> Int}
     * modelling Groovy's GDK {@code arr.count(v)} (roadmap Phase 12, permutation). Two applications
     * with the same {@code (arr, v)} share the term. The count's *meaning* comes from the per-store
     * update law the caller asserts on each {@code a[i] = val} — there is no built-in axiom here.
     */
    Object count(Object arr, Object v)

    /**
     * Declare a finite set variable, modelled as a <em>characteristic</em> array {@code Array Int -> Int}
     * where element {@code x} is a member iff {@code (select set x) == 1} (and absent at {@code 0}) — the
     * "sets" phase. Membership, add ({@code (store set x 1)}) and remove ({@code (store set x 0)}) are built
     * from {@link #select}/{@link #store} in the encoder, so they ride Z3's array theory directly. The
     * element sort is Int — the only modelled set element type (a finite node/key domain).
     */
    Object setVar(String name)

    /**
     * The cardinality {@code |set|} — an uninterpreted {@code (Array) -> Int} (analogue of {@link #count}).
     * Its meaning comes entirely from the per-mutation update law the caller asserts on each
     * {@code s.add}/{@code s.remove} ({@code card(store(s,x,1)) = card(s) + (x in s ? 0 : 1)}); there is no
     * built-in axiom. This is the building block a set-valued {@code @Decreases} measure rests on.
     */
    Object setCard(Object set)

    /**
     * The bounded-sum cardinality {@code bcount(set, k) = #{ i : 0 <= i < k ∧ i ∈ set }} — an uninterpreted
     * {@code (Array, Int) -> Int} (the primitive form of the Phase-20 recursive {@code bcount}). Two
     * applications with the same {@code (set, k)} share the term. Its meaning comes from the sound bound
     * axiom ({@code 0 <= bcount <= k}) and the <b>per-mutation law</b> the caller asserts on each
     * {@code s.add}/{@code s.remove} ({@code bcount(store(s,x,1), k) = bcount(s, k) + (0<=x<k ∧ x∉s ? 1 : 0)}) —
     * the bcount analogue of {@link #count}'s per-store law, threading the count across a set mutation.
     */
    Object setCount(Object set, Object k)

    /**
     * Phase 46a — string predicates as uninterpreted Bool functions over the {@code String!Sort}.
     * Two arguments (receiver, query) interpreted symbolically — Z3 reasons only about the
     * predicate's value at a given point, not its decomposition over characters. The encoder
     * routes {@code s.startsWith(p)}/{@code s.endsWith(q)}/{@code s.contains(sub)} on String-typed
     * receivers here. Two applications with the same {@code (s, p)} share the term, so a contract
     * naming the predicate connects to a body that names the same predicate by syntactic identity.
     * No axioms beyond translation: the verifier knows {@code startsWith(s, p)} is *some* boolean,
     * but not what relates it to {@code length} or to other strings — adequate for "every result
     * element satisfied the filter predicate"-shape proofs, insufficient for length-coupled claims.
     */
    Object stringStartsWith(Object s, Object prefix)
    Object stringEndsWith(Object s, Object suffix)
    Object stringContainsSub(Object s, Object sub)

    /**
     * Phase 46e — character indexing: an uninterpreted {@code (String!Sort, Int) -> Int}
     * returning the codepoint at the given position. Literal pinning happens at the backend
     * for each interned string constant — for {@code "hello"} the mint asserts
     * {@code charAt$("hello", 0) == 104}, etc., one assertion per character (capped at a
     * literal-length threshold to keep mint cost bounded). The encoder lowers
     * {@code s.charAt(i)} on a String-typed receiver to this, synthesising an
     * {@code IndexSite}-like obligation so {@code 0 <= i < s.length()} is enforced like
     * any other indexed read.
     */
    Object stringCharAt(Object s, Object i)

    /**
     * Phase 47 — string length, {@code str.len(s)} from Z3's native string theory.
     * Non-negativity ({@code length(s) >= 0}) and literal-length identities
     * ({@code length("hello") == 5}) are theory consequences, not axioms the backend asserts.
     * The encoder lowers both {@code s.length()} and the GDK alias {@code s.size()} here;
     * {@code s.isEmpty()} lowers to {@code length(s) == 0}.
     *
     * <p>(Phase 46b — 46c history: this was an uninterpreted {@code (String!Sort) -> Int} with
     * mint-time literal pinning and three universally-quantified axioms. Phase 47 retires both
     * the uninterpreted function and the axioms; the SMT-LIB string theory provides them.)
     */
    Object stringLength(Object s)

    /**
     * Phase 47 — string concatenation, {@code str.++(a, b)}. The encoder lowers Groovy's
     * {@code s.concat(t)} method form and {@code s + t} operator form (when both operands
     * are String-typed) to this.
     */
    Object stringConcat(Object a, Object b)

    /**
     * Phase 47 — substring extraction, {@code str.substr(s, offset, length)}. The encoder
     * lowers Groovy's {@code s.substring(begin, end)} here with {@code length = end - begin};
     * the single-arg form {@code s.substring(begin)} uses
     * {@code length = stringLength(s) - begin}. Implicit bounds obligations
     * ({@code 0 <= begin <= end <= s.length()}) are synthesised by the encoder.
     */
    Object stringSubstring(Object s, Object offset, Object length)

    /**
     * Phase 47b — {@code str.replace(s, src, dst)} — replace the *first* occurrence of
     * {@code src} in {@code s} with {@code dst}. Z3's seq theory provides this directly. The
     * encoder uses it for Groovy's {@code s.replaceFirst(regex, repl)} when the regex is a *plain
     * literal* (so the first regex match is the first literal occurrence) and the replacement is
     * metacharacter-free. Groovy's literal {@code replace} is replace-*all* and goes through
     * {@link #stringReplaceAll} instead. Returns a SeqExpr.
     */
    Object stringReplace(Object s, Object oldSub, Object newSub)

    /**
     * Phase 47b — {@code str.indexof(s, sub, fromIndex)} — leftmost position {@code i >= fromIndex}
     * where {@code sub} occurs in {@code s}, or {@code -1} if absent. The encoder lowers Groovy's
     * {@code s.indexOf(sub)} with {@code fromIndex = 0}.
     */
    Object stringIndexOf(Object s, Object sub, Object fromIndex)

    /**
     * Phase 47c — {@code str.in_re(s, regex)} — string-in-regex membership. The encoder lowers
     * Groovy's {@code s.matches(regex)} for regex literals it can parse (literals, alternation,
     * concatenation, {@code .}, {@code *}/{@code +}/{@code ?}, character classes
     * {@code [a-z]}/{@code [abc]}, groups). Unsupported regex features (anchors, predefined
     * classes {@code \d}/{@code \w}/{@code \s}, lookbehind, backreferences, {@code {n,m}}) return
     * null and surface as honest skips.
     */
    Object stringInRegex(Object s, Object regex)

    /**
     * Phase 47c — regex constructors. Build a Z3 {@code ReExpr} bottom-up from a parsed
     * pattern. {@link #stringInRegex} consumes the result. {@code reToRe(s)} converts a
     * string expression (typically a single-char literal or short fixed substring) into an
     * exact-match regex; {@code reRange(loChar, hiChar)} takes two single-char string
     * expressions and produces the character range; {@code reAllChar()} is the SMT-LIB
     * {@code re.allchar} (any single character).
     */
    Object reToRe(Object stringExpr)
    Object reUnion(Object a, Object b)
    Object reConcat(Object a, Object b)
    Object reStar(Object re)
    Object rePlus(Object re)
    Object reOption(Object re)
    Object reRange(Object loChar, Object hiChar)
    Object reAllChar()

    /**
     * Phase 47d — regex complement and intersection. {@code reIntersect(reAllChar, reComplement(re))}
     * is the standard idiom for "any single character that doesn't match {@code re}", which is how
     * negated character classes {@code [^…]} and the {@code \D} / {@code \W} / {@code \S} predefined
     * classes are translated.
     */
    Object reComplement(Object re)
    Object reIntersect(Object a, Object b)

    /**
     * Phase 47d — quantified-range regex. {@code reLoop(re, lo, hi)} matches {@code re} repeated
     * between {@code lo} and {@code hi} times; {@code reLoopAtLeast(re, lo)} repeats at least
     * {@code lo} times with no upper bound. The encoder lowers Groovy's {@code re{n,m}} /
     * {@code re{n}} / {@code re{n,}} to these.
     */
    Object reLoop(Object re, int lo, int hi)
    Object reLoopAtLeast(Object re, int lo)

    /**
     * Phase 47e — integer-to-string conversion ({@code str.from_int} in SMT-LIB). Z3's
     * semantics: maps a non-negative integer to its decimal representation; maps a negative
     * integer to the empty string. Java's {@code Integer.toString} returns {@code "-n"} for
     * negative inputs — a known semantic gap. The encoder dispatches Java's
     * {@code Integer.toString(n)} / {@code String.valueOf(n)} here; users who reason over
     * negative inputs see refutes that surprise them. ROADMAP notes the gap.
     */
    Object stringFromInt(Object n)

    /**
     * Phase 47e — string-to-integer conversion ({@code str.to_int} in SMT-LIB). Z3's
     * semantics: returns the integer value if the string is a sequence of decimal digits,
     * else {@code -1}. Java's {@code Integer.parseInt} parses signs and throws on bad input.
     * Another known semantic gap (signs, whitespace, non-decimal). The encoder dispatches
     * {@code Integer.parseInt(s)} here.
     */
    Object parseIntFromString(Object s)

    /**
     * A Bool term: true iff {@code Integer.parseInt(s)} would not throw — the sign-stripped magnitude
     * is a valid digit sequence. Used for the loud {@code NumberFormatException} obligation, the
     * companion to the sign-faithful {@link #parseIntFromString}.
     */
    Object parseIntValid(Object s)

    /**
     * Phase 47f — {@code s.replaceAll(old, new)} as an uninterpreted {@code (String, String, String)
     * -> String} pending Z3's {@code mkReplaceAll}. The session asserts weak axioms on first
     * use: identity when {@code old} doesn't occur in {@code s}, and length-preservation when
     * {@code old} and {@code new} have equal length. The encoder dispatches Groovy's
     * {@code s.replaceAll(old, new)} here. Sound under-approximation: the verifier knows less
     * than Z3 native would, but everything it does know is true.
     */
    Object stringReplaceAll(Object s, Object oldSub, Object newSub)

    /**
     * Phase 47f — {@code s.lastIndexOf(sub, fromIndex)} as an uninterpreted {@code (String, String,
     * Int) -> Int} pending a Z3 primitive. Weak axioms on first use: result is {@code >= -1};
     * result is {@code -1} when {@code sub} doesn't occur in {@code s}. The encoder dispatches
     * Groovy's {@code s.lastIndexOf(sub)} with {@code fromIndex = length(s)} (Groovy default).
     */
    Object stringLastIndexOf(Object s, Object sub, Object fromIndex)

    /**
     * Phase 47g — ASCII case folding as uninterpreted {@code (String) -> String}. Z3's string
     * theory has no native case-folding primitive, so we ship hybrid coverage:
     * <ul>
     *   <li>Every minted String literal pins its upper / lower form at the backend's
     *       {@code litOfSort} site, computed via {@code Locale.ROOT} (ASCII-faithful — no
     *       Turkish-locale {@code i}/{@code İ} surprise). So {@code "Hello".toUpperCase() == "HELLO"}
     *       folds at the mint, like length and per-position content do for native theory.</li>
     *   <li>Three structural axioms asserted on first use: length-preservation
     *       ({@code length(toUpper(s)) == length(s)}, same for toLower), idempotence
     *       ({@code toUpper(toUpper(s)) == toUpper(s)}), and the case-folding cascade
     *       ({@code toUpper(toLower(s)) == toUpper(s)}, {@code toLower(toUpper(s)) == toLower(s)}).</li>
     * </ul>
     * What it doesn't reach: per-position character claims for symbolic strings (no
     * universal-over-charAt axiom), and non-ASCII locale semantics. Both are deferred.
     */
    Object stringToUpper(Object s)
    Object stringToLower(Object s)

    /**
     * Phase 47i — {@code s.reverse()} (the GDK adds it to {@code String}) as an uninterpreted
     * {@code (String) -> String}, in the case-folding mould. Z3's seq theory has no native reverse,
     * and — as Phase 47g found — a universal over a {@code (Seq Char) -> Seq Char} uninterpreted
     * function defeats Z3's model construction, so this ships <em>literal pinning only</em>:
     * <ul>
     *   <li>Every minted String literal pins {@code reverse(lit) == mkString(rev(key))} at the
     *       backend's {@code litOfSort} site (Java {@code StringBuilder.reverse}). Pinning is
     *       <em>bidirectional</em> — the reversed literal is itself minted and pinned — so literal
     *       involution ({@code "abc".reverse().reverse() == "abc"}) and literal length
     *       ({@code "abc".reverse().length() == 3}) fall out for free as theory consequences.</li>
     * </ul>
     * What it doesn't reach: <em>symbolic</em> algebraic identities ({@code s.reverse().reverse() == s}
     * or {@code s.reverse().length() == s.length()} for a variable {@code s}), which would need the
     * universals Phase 47g showed Z3 can't model over this sort. Sound under-approximation: the
     * verifier knows less than the full algebra, but everything it does know is true.
     */
    Object stringReverse(Object s)

    /**
     * A fresh integer constant to be universally quantified over by {@link
     * #forall}. Distinct from {@link #intVar}: the caller binds the source-level
     * loop variable to this handle while translating the quantifier body, then
     * abstracts it away in the {@code forall}.
     */
    Object boundIntVar(String name)

    /**
     * Universally quantify {@code body} over {@code bound} (handles from {@link
     * #boundIntVar}), using {@code triggers} as the instantiation patterns —
     * typically the {@code (select arr i)} terms of the body. Scope is the
     * bounded-universal shape {@code ∀ i. lo <= i < hi ⇒ matrix} that Z3 handles
     * predictably; see the trigger-cliff risk in the roadmap.
     */
    Object forall(List<Object> bound, Object body, List<Object> triggers)

    /**
     * Universally quantify {@code body} over {@code bound} using ONE multi-pattern built from all of
     * {@code patternTerms} together — every term must match simultaneously for an instantiation. This
     * is the shape a multi-variable axiom needs: sortedness {@code ∀ j,k. a[j] <= a[k]} must trigger on
     * the pair {@code {a[j], a[k]}}, because a per-term pattern (the {@link #forall} default) covers only
     * one of {j, k} and Z3 rejects a pattern that leaves a bound variable uncovered — forcing the outer
     * variable onto auto-pattern/MBQI. Pinning both terms makes the random-access "gap" instantiation
     * (e.g. {@code a[i] <= a[mid]}) fire deterministically the moment both selects are ground.
     */
    Object forallMultiPattern(List<Object> bound, Object body, List<Object> patternTerms)

    /**
     * Existentially quantify {@code body} over {@code bound} — the mirror of {@link #forall},
     * for the bounded-existential shape {@code ∃ i. lo <= i < hi ∧ matrix} (e.g. {@code a.any { … }},
     * and precise {@code xs.contains(y)}). {@code triggers} are the instantiation patterns.
     */
    Object exists(List<Object> bound, Object body, List<Object> triggers)

    /** Build expressions. Args are handles previously returned by this session. */
    Object intLit(long n)
    Object plus(Object a, Object b)
    Object minus(Object a, Object b)
    Object times(Object a, Object b)
    Object neg(Object a)

    /**
     * Integer division / modulo / remainder, mapped to model Groovy's three distinct operations
     * (Phase 50 — corrected from the Phase 48 Java/Euclidean conflation):
     * <ul>
     *   <li>{@code intMod} → SMT-LIB {@code (mod a b)} (Euclidean, always {@code [0, |b|)}). This is
     *       Groovy's {@code a.mod(b)} ({@code BigInteger.mod}): non-negative, and the caller adds a
     *       {@code b > 0} obligation (Groovy throws {@code ArithmeticException} on a non-positive
     *       modulus).</li>
     *   <li>{@code intRem} → SMT-LIB {@code (rem a b)} (truncated, sign-of-dividend). This is Groovy's
     *       {@code %} operator and {@code a.remainder(b)} ({@code -5 % 2 == -1}).</li>
     *   <li>{@code intDiv} → SMT-LIB {@code (div a b)} (Euclidean/floor). Used only to build Groovy's
     *       {@code a.intdiv(b)} / {@code (int)(a / b)} (truncate-toward-zero) as
     *       {@code intDiv(a - intRem(a, b), b)} — an exact division, so floor and truncation agree.</li>
     * </ul>
     * The Groovy {@code /} operator itself is <em>not</em> integer division — it yields a
     * {@code BigDecimal} ({@code 5 / 2 == 2.5G}), which the integer fragment doesn't model, so the
     * encoder skips it loudly. The {@code b != 0} obligation is collected as a {@code DivideSite}.
     */
    Object intDiv(Object a, Object b)
    Object intMod(Object a, Object b)
    Object intRem(Object a, Object b)

    // Bitwise operators on Int operands, modelled via Z3's bit-vector theory at Java's 32-bit width:
    // each converts both operands to 32-bit two's-complement bit-vectors, applies the BV op, and reads
    // the result back as a signed Int. Faithful to Java `int` semantics (wraparound, sign extension).
    // Shifts mask the count to 5 bits (Java's `x << (k & 31)`); `bvShr` is the arithmetic (sign-filling)
    // right shift, matching Java `>>`, and `bvLShr` the logical (zero-filling) one, matching Java `>>>`.
    Object bvAnd(Object a, Object b)
    Object bvOr(Object a, Object b)
    Object bvXor(Object a, Object b)
    Object bvShl(Object a, Object b)
    Object bvShr(Object a, Object b)
    Object bvLShr(Object a, Object b)

    // Phase 61 — exact-rational (Z3 Real) support for Groovy's BigDecimal arithmetic. The
    // arithmetic/comparison ops above (plus/minus/times/eq/lt/…) are sort-polymorphic and accept
    // Real operands directly; only these four are Real-specific.
    Object realLit(String rational)        // a rational numeral string, e.g. "25/10" for 2.5G
    Object realVar(String name)
    Object realDiv(Object a, Object b)      // exact real division (a/b over Reals)
    Object intToReal(Object a)              // coerce an Int handle into the Real sort

    Object eq(Object a, Object b)
    Object ne(Object a, Object b)
    Object lt(Object a, Object b)
    Object le(Object a, Object b)
    Object gt(Object a, Object b)
    Object ge(Object a, Object b)

    Object and(List<Object> xs)
    Object or(List<Object> xs)
    Object not(Object x)
    Object implies(Object a, Object b)

    Object boolLit(boolean b)

    /** Assert a boolean expression. */
    void assertExpr(Object boolExpr)

    /**
     * Check the current assertion set. Returns:
     *   - VERIFIED if UNSAT (i.e. the property holds)
     *   - REFUTED with a counterexample if SAT
     *   - UNKNOWN if the solver gave up / timed out
     *
     * NOTE: the caller asserts the *negation* of what they want to
     * prove. SAT means the negation has a model, i.e. the property
     * fails on that model.
     */
    CheckResult check()

    /**
     * VERIFY_EXPLAIN — register the authored precondition's per-conjunct breakdown for a post-proof ablation
     * read-out. Passive and opt-in: only ever called when the flag is on, so an OFF run carries no state and no
     * behaviour change. {@code preTerm} is the fused precondition already asserted (excluded from the held-fixed
     * base during ablation); {@code labels}/{@code clauseTerms} are the individual top-level {@code &&} conjuncts.
     */
    void explainRegister(Object preTerm, List<String> labels, List<Object> clauseTerms)

    /**
     * VERIFY_EXPLAIN — note a *structural* fact (a class invariant, a JVM integral bound) as an attributable,
     * droppable assumption, so the read-out can surface it when the proof leaned on it. {@code label} is the
     * pre-formatted display string (e.g. {@code "@Invariant (size >= 0)"}); {@code term} is its asserted handle.
     */
    void explainNoteFact(String label, Object term)

    /**
     * VERIFY_EXPLAIN — for the just-checked (VERIFIED) goal, the load-bearing verdict per attributable fact
     * (authored {@code @Requires} conjunct or noted structural fact), found by drop-one-and-re-prove in fresh
     * full-strength solvers (never the weaker unsat-core mode, so the result is exact and the main solver is never
     * touched). Structural facts appear only when load-bearing. {@code null} if nothing was registered or the proof
     * can't be reproduced from the captured set (fail closed — never a fabricated explanation).
     */
    Map<String, Boolean> explainLoadBearing()

    /** VERIFY_EXPLAIN — note that a precondition existed but a conjunct fell outside the encodable fragment, so the
     *  read-out is a genuine gap (distinct from "no authored {@code @Requires} at all"). */
    void explainMarkGap()

    /** VERIFY_EXPLAIN — whether {@link #explainMarkGap} fired for this obligation. */
    boolean explainHadGap()

    @Override
    void close()
}

@CompileStatic
class CheckResult {
    enum Status { VERIFIED, REFUTED, UNKNOWN }
    Status status
    /** Variable name -> concrete value, populated only on REFUTED. */
    Map<String, Long> counterexample = [:]
    /**
     * Non-Int variable name -> the literal key text the model pinned (Phase 27). A String
     * parameter the solver constrained to {@code "admin"} appears here as
     * {@code [name: "admin"]}; an Enum parameter as {@code [name: "RED"]} (the property
     * name, without the class prefix — the {@link Reporter} adds the class on render).
     * Empty unless the refutation involves a non-Int sort.
     */
    Map<String, String> sortedCounterexample = [:]
    /** Free-text reason, populated on UNKNOWN. */
    String reason
    /**
     * A runnable call that exhibits the failure, reconstructed from the counterexample
     * (Phase 9 diagnostics) — e.g. {@code g(new int[0], -1)}. Best-effort and illustrative;
     * set by the caller, not the solver. Null when no repro could be built.
     */
    String failingCall
    /**
     * Phase 126 — extra free-text diagnostic lines the caller computes from the live model and appends to
     * the rendered counterexample (e.g. {@code r[0] = "🥤" — the spec requires "🐝"}), each shown on its own
     * line. Empty unless the caller surfaced something the scalar counterexample doesn't carry.
     */
    List<String> notes = []

    static CheckResult verified() {
        new CheckResult(status: Status.VERIFIED)
    }
    static CheckResult refuted(Map<String, Long> ce) {
        new CheckResult(status: Status.REFUTED, counterexample: ce)
    }
    static CheckResult unknown(String why) {
        new CheckResult(status: Status.UNKNOWN, reason: why)
    }
}
