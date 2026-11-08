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
import org.codehaus.groovy.ast.ClassNode
import org.codehaus.groovy.ast.MethodNode
import org.codehaus.groovy.ast.expr.BinaryExpression
import org.codehaus.groovy.ast.expr.ClosureExpression
import org.codehaus.groovy.ast.expr.Expression
import org.codehaus.groovy.ast.expr.MethodCallExpression
import org.codehaus.groovy.ast.expr.PropertyExpression

/**
 * A pluggable <b>domain encoding</b>: recognisers and axioms for a library/domain vocabulary (a spec-helper
 * family, JSR 385 quantities, a time or money library, …), contributed from outside the core encoder. The
 * boundary is principled: <b>packs model library/domain vocabularies; the core models the language</b>
 * (ints, arrays, operators, closures, {@code String} theory stay in the {@code Encoder}).
 *
 * <p>Discovery is via {@link java.util.ServiceLoader} ({@code META-INF/services/verification.EncodingPack}
 * on the compile classpath — the same mechanism that registers the contract transform), applied in
 * name-sorted order at a fixed slot in the encoder's method-call dispatch registry: after the core scalar
 * and aggregation forms, before the collection oracles. Within one pack, dispatch internally.
 *
 * <p>The first pack in tree is {@link NumberTheoryPack} (the {@code Fib}/{@code Trib}/{@code Tetra}/
 * {@code Gcd}/{@code Lcm} spec helpers) — the reference for the shape: a runtime-executable helper class,
 * a recogniser per spelling, defining axioms asserted once per VC via {@link TheoryApi#axiomsOnce}, and a
 * pinned verify/refute case corpus (its groups predate the SPI and double as its regression mesh).
 *
 * <p>This SPI is <b>experimental</b> and minimal by design; scope collection, normalizer rewrites, and
 * counterexample rendering are the known growth surfaces, to be added when a pack demonstrably needs
 * them. (Property/operator recognisers arrived with UnitsPack — Phase 188; the STC-companion surfaces
 * {@code resolveDynamicProperty}/{@code resolveDynamicMethod} with MetaProgrammingPack — Phase 209.)
 */
@CompileStatic
interface EncodingPack {

    /** Stable pack name — used for deterministic (name-sorted) dispatch order, the {@code VERIFY_PACKS}
     *  selection knob, and diagnostics/catalog provenance. */
    String name()

    /**
     * Phase 209 — the STC companion (type-checking half). A pack may TYPE an unresolved property the
     * static checker would otherwise reject — e.g. {@code n.fizzBuzz} backed by a statically-visible
     * {@code Integer.metaClass.getFizzBuzz = { … }} registration in {@code enclosingClass}. Return the
     * type to store for the property expression, or null to decline. Blessing is principled: a pack must
     * only resolve what it can also faithfully MODEL (or the model refuses loudly) — this is the narrow
     * gate through which slim dynamic-Groovy support returns to the {@code @TypeChecked} world.
     */
    default ClassNode resolveDynamicProperty(ClassNode receiverType, PropertyExpression pexp,
                                             ClassNode enclosingClass) { null }

    /**
     * Phase 209 — the STC companion for a missing METHOD (e.g. the operator method
     * {@code Integer.multiply(String)} added via {@code metaClass}, or a {@code delegate}-dispatched call
     * inside a registration closure). Return a synthetic {@link MethodNode} carrying the resolved
     * signature (name/params/return type), or null to decline. {@code enclosingClosure} is non-null when
     * the call sits inside a closure (a registration body's {@code delegate} calls resolve against the
     * registration's target type).
     */
    default MethodNode resolveDynamicMethod(ClassNode receiverType, String name, ClassNode[] argTypes,
                                            ClassNode enclosingClass, ClosureExpression enclosingClosure) { null }

    /**
     * The capability-group names (the {@code group:} keys of the case corpus) that pin this pack's
     * behaviour — its regression mesh and its {@code catalog.json} provenance. The doc-drift lint fails
     * the build if a named group has no cases, so the claim cannot silently rot; an empty list is legal
     * but means the pack ships no evidence (see PACKS.md on the corpus obligation).
     */
    default List<String> corpusGroups() { Collections.<String> emptyList() }

    /**
     * The external-specification skeletons this pack contributes (Phase 227): fully-qualified class
     * names whose {@code META-INF/groovy-verify/specs/<fqn>.groovy} resources ship in the pack's jar.
     * Declaring them buys three things a bare classpath resource does not get: <b>lifecycle
     * coherence</b> (deselecting the pack via {@code VERIFY_PACKS} also deselects its specs — an FQN
     * declared by a discovered-but-disabled pack is never consumed), the <b>trusted-inventory lint</b>
     * (each declared skeleton must parse and carry contracts, exactly as the core's do — a malformed
     * pack spec is silent trust loss), and <b>catalog attribution</b>. The soundness obligation
     * extends accordingly: a pack may only spec what is provably true of the library — the runtime
     * rung's grid cross-checks apply to pack-shipped specs unchanged.
     */
    default List<String> specFqns() { Collections.<String> emptyList() }

    /**
     * Try to translate a method call. {@code m} is the method name (non-null), {@code recv} the receiver
     * with any transparent immutability wrapper stripped, {@code args} the flat argument expressions.
     * Return {@link TheoryApi#NO_MATCH} when the guard does not fire, {@code null} for matched-but-
     * untranslatable (aborts the dispatch — a loud skip), else the SMT handle.
     */
    Object translateCall(TheoryApi api, MethodCallExpression mce, String m, Expression recv, List<Expression> args)

    /** Try to translate a property read {@code obj.prop} (same tri-state as {@link #translateCall}).
     *  Dispatched after the core's carrier/record branches, before the JDK-constant folds. */
    default Object translateProperty(TheoryApi api, PropertyExpression pe, Expression obj, String prop) {
        TheoryApi.NO_MATCH
    }

    /** Try to translate a binary expression (same tri-state); {@code opType} is the
     *  {@link org.codehaus.groovy.syntax.Types} operator constant. Dispatched from the core's
     *  binary translator at the domain-comparison slot (before string/numeric handling). */
    default Object translateBinary(TheoryApi api, BinaryExpression be, int opType) {
        TheoryApi.NO_MATCH
    }

    /** Try to translate a cast {@code (T) x} / {@code x as T} (same tri-state as {@link #translateCall}). Dispatched from
     *  the core's cast translator before it treats the cast as transparent (Phase 533 — a JSR 385 value read out
     *  {@code as BigDecimal} converts a RationalNumber to 34 digits). */
    default Object translateCast(TheoryApi api, org.codehaus.groovy.ast.expr.CastExpression ce) {
        TheoryApi.NO_MATCH
    }

    /** True iff {@code e} is a pack-domain value that scalar classifiers must not claim — e.g. a JSR 385
     *  {@code quantity / quantity} is Quantity.divide, not BigDecimal division (so no Real classification
     *  and no divide-by-zero obligation on the divisor). Static context: no {@link TheoryApi} available. */
    default boolean claimsExpression(Expression e) { false }

    /** True iff {@code e} is a construction this pack can model as a named value's source — the checker
     *  then aliases the (scalar-handle-less) name to the expression, which the pack's readers resolve via
     *  {@link TheoryApi#sourceAlias}. */
    default boolean claimsValueSource(TheoryApi api, Expression e) { false }
    /** Phase 538 — true iff the statement {@code e} changes nothing the program reads, by this pack's knowledge of
     *  its library (e.g. Pekko's {@code super(context)} in an {@code AbstractBehavior} subclass, measured to run no
     *  subclass code). The body walk then takes it as an empty step. Static context, like {@link #claimsExpression}. */
    default boolean claimsNoEffect(Expression e) { false }
    /** Phase 539 — the reference parameters of {@code m} that this pack knows its library never passes as
     *  {@code null} (e.g. the message of a Pekko handler registered with {@code onMessage}, measured in
     *  {@code PekkoSemanticsTest}). Each is assumed non-null on entry, as a {@code @NonNull} parameter is, and recorded
     *  in the trust ledger as a {@code pack fact}. A pack must answer only for methods nothing but the library can call:
     *  the fact puts no obligation on a caller. */
    default List<String> nonNullOnEntry(MethodNode m) { Collections.<String> emptyList() }
    /** Phase 545 — the parameters of the closure literal {@code ce}, passed as argument {@code at} of {@code call}
     *  (a {@code MethodCallExpression} or {@code StaticMethodCallExpression}, type-checked), that this pack knows its
     *  library never calls it with as {@code null} (e.g. a Pekko {@code Behaviors.receiveMessage} handler's message,
     *  measured in {@code PekkoSemanticsTest}). Each is assumed non-null where the closure runs, unless the closure
     *  assigns it, and recorded in the trust ledger as a {@code pack fact}. The literal is the library's alone: nothing
     *  else can call it. Static context. */
    default List<String> nonNullClosureParams(Expression call, int at, ClosureExpression ce) { Collections.<String> emptyList() }
    /** Phase 540 — true iff, on the exit of {@code m} that returns {@code returned}, the class invariant is not owed:
     *  this pack knows its library lets no code observe the object's state after that exit (e.g. a Pekko handler
     *  returning {@code Behaviors.stopped()}, measured to get no further message). The entry assumption stands;
     *  each use is recorded in the trust ledger as a {@code pack fact}. */
    default boolean releasesInvariantAt(MethodNode m, Expression returned) { false }
    /** Phase 542 — true iff {@code m} may run on a state where the class invariant no longer holds, and nothing
     *  observes the object after it (e.g. a Pekko {@code PostStop} handler: it runs once after a handler returned
     *  {@code Behaviors.stopped()}, measured). The invariant is then neither assumed on entry nor owed on exit; the
     *  release of the exit obligation is recorded in the trust ledger as a {@code pack fact}. */
    default boolean runsOutsideInvariant(MethodNode m) { false }
    /** Phase 541 — what every normal exit of {@code m} owes by this pack's knowledge of its library, beyond the
     *  method's contracts, in words for the diagnostic (e.g. {@code "a reply on message.replyTo"}: a Pekko handler
     *  given an {@code ask}'s reply ref); null when nothing. The checker then asks {@link #meetsExitObligation} of
     *  each exit path, and reports one that doesn't meet it where the path is feasible, with its counterexample. */
    default String exitObligation(MethodNode m) { null }
    /** Phase 541 — true iff the exit path made of {@code steps} (the body walk's {@code Guard} / {@code Assign} /
     *  {@code LemmaCall} … steps) and returning {@code returned} meets {@link #exitObligation}. */
    default boolean meetsExitObligation(MethodNode m, List<Object> steps, Expression returned) { true }

    /**
     * A per-method <b>checker pass</b> — pure AST analysis with diagnostics, no SMT (e.g. UnitsPack's C₀
     * kind-vector check of {@code as Quantity<K>} casts: compile-time exponent arithmetic over the
     * declared generics). Runs after the method's encoder-backed checks, best-effort: an exception is
     * contained per-pack (the pass silently contributes nothing, matching the engine's own posture for
     * this pass class). Program against {@link CheckerApi} only.
     */
    default void checkMethod(CheckerApi api, MethodNode node) { }
}
