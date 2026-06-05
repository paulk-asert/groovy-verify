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

    /** The element {@code arr[i]} — Z3 {@code (select arr i)}. */
    Object select(Object arr, Object idx)

    /** The array equal to {@code arr} except index {@code idx} holds {@code val} — Z3 {@code (store arr idx val)}. */
    Object store(Object arr, Object idx, Object val)

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
