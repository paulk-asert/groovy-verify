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
 * Formats {@link CheckResult}s into compiler messages. The format is
 * deliberately close to OpenJML's "The prover cannot establish ..."
 * style, with one extension: Dafny-style counterexamples appended
 * inline when the solver returns a refuting model.
 *
 * Example:
 *   "Cannot prove precondition of isqrt at this call site:
 *      required: x >= 0
 *      counterexample: n = -1"
 */
@CompileStatic
class Reporter {

    /** {@code VERIFY_REFUTATION} — transient tooling, like {@code VERIFY_VERBOSE}: when set to {@code assert} /
     *  {@code junit} / {@code spock}, a refuted obligation additionally emits a runnable repro test in that style
     *  (the counterexample as a failing test). {@code null} ⇒ default text output, unchanged. */
    static final String REFUTATION_FORMAT = System.getenv('VERIFY_REFUTATION')

    /** {@code VERIFY_SUGGEST} — transient tooling: when set to {@code contract}, a refuted *implicit* obligation
     *  (bounds / divide-by-zero / null / overflow) additionally suggests the {@code @Requires} that would discharge
     *  it (the Clousot/abduction angle). A human-reviewed hint, never auto-applied. {@code null} ⇒ off. */
    static final String SUGGEST_FORMAT = System.getenv('VERIFY_SUGGEST')

    /** Render the suggested precondition (VERIFY_SUGGEST). */
    static String formatSuggestion(String requiresText) {
        "    suggested fix: @Requires({ ${requiresText} })".toString()
    }

    /** {@code VERIFY_EXPLAIN} — transient tooling for interactive proof: when set, a *verified* implicit obligation
     *  additionally prints which authored {@code @Requires} clauses the proof actually leaned on (ablation read-out).
     *  Pure downstream read-out — never changes a verify/refute. {@code null} ⇒ off. */
    static final boolean EXPLAIN = System.getenv('VERIFY_EXPLAIN') != null

    /** {@code VERIFY_DUMP_SMT} — when set, every solver query is printed as a self-contained SMT-LIB2 benchmark you
     *  can pipe to any solver (cvc5 / z3 / yices) or inspect to debug the encoding. Pure output; no behaviour change. */
    static final boolean DUMP_SMT = System.getenv('VERIFY_DUMP_SMT') != null

    /** Print the load-bearing read-out for a discharged obligation (VERIFY_EXPLAIN). Each {@code facts} key is a
     *  pre-formatted label carrying its own kind ({@code @Requires …} authored clause, {@code @Invariant …} or
     *  {@code JVM bound …} structural fact); the value is whether dropping it breaks the proof. Authored clauses
     *  show both verdicts (the not-load-bearing ones are the hygiene signal); structural facts appear only when
     *  load-bearing (a *hidden dependency* worth surfacing — a non-load-bearing JVM bound is just noise you can't
     *  act on, so the map already omits it). A {@code null} / empty map means nothing was attributable. */
    static void emitExplain(String obligation, Map<String, Boolean> facts, boolean hadGap) {
        if (facts == null || facts.isEmpty()) {
            println(hadGap
                ? "  explain ✓ ${obligation} — no explanation (a precondition clause is outside the captured fragment)"
                : "  explain ✓ ${obligation} — discharged without an authored @Requires (an inline guard / invariant / path fact carries it)")
            return
        }
        println "  explain ✓ ${obligation}"
        facts.each { String label, Boolean lb ->
            if (!lb) println "      not load-bearing: ${label}"             // only authored clauses reach here
            else if (label.startsWith('@Requires')) println "      load-bearing:     ${label}"
            else println "      also leaned on:   ${label}"                 // a structural fact (invariant / JVM bound)
        }
        if (hadGap) println "      (note: a precondition clause is outside the captured fragment — not attributed)"
    }

    /** Render a reconstructed failing {@code invocation} as a repro test in the requested style. {@code exception}
     *  is the runtime exception the call throws, or {@code null} for a verify-only obligation (e.g. integer
     *  overflow, which wraps silently and throws nothing — so the repro is documentary, not a failing test). */
    static String formatRepro(String invocation, String exception, String name) {
        if (exception == null) {
            return "    repro: ${invocation}   // verify-only — wraps at runtime, throws no exception".toString()
        }
        switch (REFUTATION_FORMAT) {
            case 'junit':
                return "    repro (JUnit):\n        @Test void ${name}() { assertThrows(${exception}.class, () -> ${invocation}); }".toString()
            case 'spock':
                return "    repro (Spock):\n        def '${name}'() { when: ${invocation}; then: thrown(${exception}) }".toString()
            default:   // 'assert' (and any other value) — the smallest runnable form
                return "    repro (assert): groovy.test.GroovyAssert.shouldFail(${exception}) { ${invocation} }".toString()
        }
    }

    static String formatPreconditionFailure(String calleeName,
                                            String contractText,
                                            CheckResult result) {
        StringBuilder sb = new StringBuilder()
        switch (result.status) {
            case CheckResult.Status.REFUTED:
                sb.append("Cannot prove precondition of ").append(calleeName)
                  .append(" at this call site")
                if (contractText) {
                    sb.append("\n    required: ").append(contractText)
                }
                appendModel(sb, result)
                break

            case CheckResult.Status.UNKNOWN:
                sb.append("Could not decide precondition of ").append(calleeName)
                  .append(" at this call site (solver: ").append(result.reason).append(")")
                if (contractText) {
                    sb.append("\n    required: ").append(contractText)
                }
                break

            default:
                // VERIFIED isn't a failure; this method shouldn't be called.
                sb.append("Precondition verified — no error to report")
        }
        sb.toString()
    }

    static String formatPostconditionFailure(String methodName,
                                             String contractText,
                                             CheckResult result) {
        StringBuilder sb = new StringBuilder()
        switch (result.status) {
            case CheckResult.Status.REFUTED:
                sb.append("Cannot prove postcondition of ").append(methodName)
                  .append(" holds on this return path")
                if (contractText) {
                    sb.append("\n    ensured: ").append(contractText)
                }
                appendModel(sb, result)
                break

            case CheckResult.Status.UNKNOWN:
                sb.append("Could not decide postcondition of ").append(methodName)
                  .append(" (solver: ").append(result.reason).append(")")
                if (contractText) {
                    sb.append("\n    ensured: ").append(contractText)
                }
                break

            default:
                sb.append("Postcondition verified — no error to report")
        }
        sb.toString()
    }

    /**
     * Phase 130 — a monoid/semigroup law a {@code @Reducer}/{@code @Associative} combiner *asserts* but that
     * groovy-verify could not prove. Derived automatically from the annotation + the combiner's equation, so the
     * wording names the law and the combiner rather than a synthetic method.
     */
    static String formatReducerLawFailure(String combinerName, String law, String lawText, CheckResult result) {
        StringBuilder sb = new StringBuilder()
        switch (result.status) {
            case CheckResult.Status.REFUTED:
                sb.append("Cannot prove @Reducer ").append(law).append(" for combiner ").append(combinerName)
                if (lawText) sb.append("\n    law: ").append(lawText)
                appendModel(sb, result)
                break
            case CheckResult.Status.UNKNOWN:
                sb.append("Could not decide @Reducer ").append(law).append(" for combiner ").append(combinerName)
                  .append(" (solver: ").append(result.reason).append(")")
                if (lawText) sb.append("\n    law: ").append(lawText)
                break
            default:
                sb.append("@Reducer ").append(law).append(" verified — no error to report")
        }
        sb.toString()
    }

    /**
     * Phase 136 — a monad/functor law a {@code @Monadic} carrier *asserts* but that groovy-verify could not
     * prove, derived automatically from the annotation. Names the law and the carrier.
     */
    static String formatMonadicLawFailure(String carrierName, String law, String lawText, CheckResult result) {
        StringBuilder sb = new StringBuilder()
        switch (result.status) {
            case CheckResult.Status.REFUTED:
                sb.append("Cannot prove @Monadic ").append(law).append(" for carrier ").append(carrierName)
                if (lawText) sb.append("\n    law: ").append(lawText)
                appendModel(sb, result)
                break
            case CheckResult.Status.UNKNOWN:
                sb.append("Could not decide @Monadic ").append(law).append(" for carrier ").append(carrierName)
                  .append(" (solver: ").append(result.reason).append(")")
                if (lawText) sb.append("\n    law: ").append(lawText)
                break
            default:
                sb.append("@Monadic ").append(law).append(" verified — no error to report")
        }
        sb.toString()
    }

    /** Phase 71 — a self-contradictory @Requires: it can never hold, so the contract is never checked. */
    static String formatVacuousPrecondition(String methodName, String requiresText) {
        StringBuilder sb = new StringBuilder()
        sb.append("Vacuous precondition of ").append(methodName)
          .append(" — its @Requires can never be satisfied, so the method's contract is never actually checked")
        if (requiresText) sb.append("\n    requires: ").append(requiresText)
        sb.toString()
    }

    /**
     * Phase 62 — the solver couldn't decide the postcondition, but bounded property-based testing of
     * the executable contract found a concrete input on which it fails. Reported as a genuine
     * refutation (with a runnable repro), distinguished from a proof by the "by testing" wording.
     */
    static String formatPostconditionRefutedByTesting(String methodName, String contractText, String failingCall) {
        StringBuilder sb = new StringBuilder()
        sb.append("Postcondition of ").append(methodName)
          .append(" fails (solver could not decide; counterexample found by bounded testing)")
        if (contractText) sb.append("\n    ensured: ").append(contractText)
        sb.append("\n    fails on: ").append(failingCall)
        sb.toString()
    }

    static String formatClassInvariantViolation(String methodName,
                                                String invariantText,
                                                CheckResult result) {
        StringBuilder sb = new StringBuilder()
        switch (result.status) {
            case CheckResult.Status.REFUTED:
                sb.append("Cannot prove class invariant of ").append(methodName)
                  .append(" holds at method exit")
                if (invariantText) {
                    sb.append("\n    invariant: ").append(invariantText)
                }
                appendModel(sb, result)
                break

            case CheckResult.Status.UNKNOWN:
                sb.append("Could not decide class invariant of ").append(methodName)
                  .append(" (solver: ").append(result.reason).append(")")
                if (invariantText) {
                    sb.append("\n    invariant: ").append(invariantText)
                }
                break

            default:
                sb.append("Class invariant verified — no error to report")
        }
        sb.toString()
    }

    static String formatClassInvariantSkipped(String methodName, String invariantText) {
        "Skipped class invariant for ${methodName} (invariant '${invariantText}' is outside fragment). " +
        "The clause is not assumed at entry nor proved at exit; other obligations on the method " +
        "still apply."
    }

    /** Phase 120 — a behavioral-subtyping (Liskov) violation: an override's contract is not substitutable for
     *  the method it overrides (a strengthened precondition or a weakened postcondition). */
    static String formatLspViolation(String methodName, String kind, String detail, CheckResult result) {
        StringBuilder sb = new StringBuilder()
        sb.append("Liskov substitution violation in override '").append(methodName)
          .append("': its ").append(kind).append(" is not behaviourally compatible with the overridden method")
        if (detail) sb.append("\n    rule: ").append(detail)
        appendModel(sb, result)
        sb.toString()
    }

    static String formatModifiesViolation(String methodName, String location, Collection<String> declared) {
        "Method '${methodName}' writes '${location}', which is not in its @Modifies clause ${new TreeSet<>(declared)}. " +
        "A method may modify only the locations it declares (an empty @Modifies({}) means none)."
    }

    // ---- Dimensional analysis (Phase 131) ----

    /** Phase 213 — an @ThrowsIf direction refuted, with the concrete witness input. */
    static String formatThrowsIfRefuted(String methodName, String detail, String cex) {
        "Cannot prove @ThrowsIf contract of ${methodName}: ${detail}" +
            (cex ? "\n    counterexample: ${cex}" : '')
    }

    /** Phase 213 — an @ThrowsIf contract outside the checkable fragment: loud skip. */
    static String formatThrowsIfSkipped(String methodName, String reason) {
        "Skipped @ThrowsIf verification for ${methodName} (${reason}). The contract is outside the " +
        "checked fragment (a condition over unmodified parameters; a body of guards, throws, and " +
        "returns). The method is allowed to proceed unchecked."
    }

    /** Phase 212 — a {@code shouldFail} claim refuted: the block provably does NOT behave as claimed. */
    static String formatShouldFailRefuted(String detail) {
        "Cannot prove shouldFail claim: ${detail}"
    }

    /** Phase 212 — a {@code shouldFail} block outside the closed-witness fragment: loud skip. */
    static String formatShouldFailSkipped(String reason) {
        "Skipped shouldFail claim (${reason}). The block is outside the closed-witness fragment " +
        "(a same-class call with constant arguments, or direct if/throw/return statements over " +
        "constants). The claim is allowed to proceed unchecked — groovy-test still checks it at runtime."
    }

    static String formatPostconditionSkipped(String methodName, String reason) {
        "Skipped verification of postcondition for ${methodName} (${reason}). " +
        "The body uses a construct or value outside the spike's supported " +
        "fragment (straight-line code, if/else, single-assignment locals, " +
        "linear int arithmetic). The method is allowed to proceed unchecked."
    }

    // ---- Parallel interference (Phase 240) ----

    /**
     * Phase 240 — the PAR disjointness side condition refuted: an async task and a concurrent
     * accessor touch the same captured state inside the task's fork-to-join window, so the value
     * the task computes is not sequentially determined. This is a genuine race in the code (the
     * RacyGather shape), not a modelling limit — which is why it is an error, not a skip: without
     * the check the safe-value model would resolve the task's reads against whichever binding is
     * in scope at the read-out site and *prove* a scheduler-dependent value.
     */
    static String formatParInterference(String methodName, String var, String detail) {
        "Parallel interference in '${methodName}': ${detail}. Between its fork and its join an " +
        "async task runs concurrently with the enclosing body, so '${var}' may be observed in " +
        "either state and the task's value is not sequentially determined. Keep the captured " +
        "state disjoint (move the conflicting access before the fork or after the join), or " +
        "declare the interference discipline with @Rely/@Guarantee/@UnderRely."
    }

    // ---- Channel linearity (Phase 241) ----

    /**
     * Phase 241 — the point-to-point channel discipline refuted: two concurrent processes on the
     * same channel end (send/send or receive/receive), a send into a pipeline-derived channel, or
     * a subscriber joining a broadcast while a sender is live. An error, not a skip: the conflict
     * is a race in the code — without the check, the one-element scalar model proved a
     * scheduler-dependent value (flatten-order for racing senders, duplicate delivery for racing
     * receivers).
     */
    static String formatChannelLinearity(String methodName, String chan, String detail) {
        "Channel linearity violation in '${methodName}': ${detail}. A point-to-point channel has " +
        "one live process per end — one sender, one receiver (FIFO per-element reasoning depends " +
        "on it). Make the conflicting uses sequential, give each producer its own channel, or use " +
        "a BroadcastChannel (subscribing before any sender starts) for one-to-many delivery."
    }

    /** Phase 241/247 — a channel used beyond the bounded-FIFO model: a loud skip, with the channel
     *  and the reason named (the rewrite would otherwise prove an order- or count-dependent value). */
    static String formatChannelModelSkipped(String methodName, String chan, String reason) {
        "Skipped channel verification for ${methodName} (channel '${chan}' ${reason}). The channel " +
        "model carries a bounded FIFO per channel — a statically known sequence of one-shot sends " +
        "from one process, matched in order by one-shot receives (or one drain / pipeline stage) " +
        "from one process. The method is allowed to proceed unchecked."
    }

    // ---- Selection starvation (Phase 256) ----

    /** Phase 256 — under ChannelSelect's priority (the lowest ready index wins), a branch behind an always-ready
     *  one may never be taken: a liveness hazard, named. */
    static String formatSelectionStarvation(String methodName, String starved, String ahead, int altLine, int producerLine) {
        formatSelectionStarvation(methodName, starved, ahead, altLine, producerLine, false)
    }

    /** Phase 257 — {@code freshFair}: the ALT is `fair()` but on a fresh instance each iteration, so the rotation
     *  state is lost and the policy is priority in effect. */
    static String formatSelectionStarvation(String methodName, String starved, String ahead, int altLine, int producerLine, boolean freshFair) {
        "Selection starvation hazard in '${methodName}': branch '${starved}' of the ALT at line ${altLine} may starve — " +
        "branch '${ahead}' precedes it and its producer (the while (true) at line ${producerLine}) never blocks, so it is " +
        "always ready, and " + (freshFair ?
            "fair() on a fresh ChannelSelect instance each iteration keeps no rotation state, so the lowest ready index is taken every time. Hoist the instance before the loop (val alt = ChannelSelect.from(…).fair()) and reuse it." :
            "ChannelSelect takes the lowest ready index. Put the branch that must not starve first, bound the producer, or select with a held fair() instance (Groovy 6.0.0-beta-4+, GROOVY-12320) for a rotating priority.")
    }

    // ---- Channel contracts (Phase 242) ----

    /** Phase 242 — a channel element constraint outside the checkable vocabulary: loud skip, so the
     *  author knows it is neither checked at sends nor assumed at receives. */
    static String formatChannelConstraintSkipped(String methodName, String chan, String annotation) {
        "Skipped channel-contract constraint ${annotation} on '${chan}' in ${methodName}. The channel " +
        "contract fragment is numeric bounds on an int/long element (@Positive, @PositiveOrZero, " +
        "@Negative, @NegativeOrZero, @Min, @Max; @NotNull is a no-op there). This constraint is " +
        "neither checked at sends nor assumed at receives."
    }

    // ---- Network well-formedness (Phase 243) ----

    /**
     * Phase 243 — the wait-for order of a one-shot channel network is not well-founded: a circular
     * wait among receives, sends, and joins (a guaranteed deadlock at this action grain), or a
     * receive no send can ever satisfy. The same well-foundedness argument as @Decreases and the
     * dining-philosophers resource hierarchy, applied to the network's blocking structure.
     */
    static String formatNetworkDeadlock(String methodName, String detail) {
        "Process-network deadlock in '${methodName}': ${detail}. A one-shot channel network is " +
        "deadlock-free exactly when its wait-for order is well-founded; this one blocks forever. " +
        "Move the send before the blocking receive, fork the producer before awaiting its " +
        "consumer, or let a concurrent task serve the channel."
    }

    /** Phase 243 — the network is outside the certificate's scope: loud skip, no claim either way. */
    /** Phase 259 — a verification ghost (`c.taken`) used where it names nothing. */
    static String formatGhostMisuse(String ghost, String reason) {
        "Verification ghost '${ghost}' names nothing here: ${reason}. `c.taken` is the list of elements the " +
        "enclosing loop has taken from channel c so far — a stream it receives from a cycle partner, or a " +
        "branch of its ALT — and `c.sent` the list its process has sent on a stream it produces, for that " +
        "loop's @Invariant."
    }

    static String formatNetworkSkipped(String methodName, String reason) {
        "Skipped network well-formedness check for ${methodName} (${reason}). The deadlock-freedom " +
        "certificate covers one-shot networks of unconditional sends and receives on local " +
        "channels; outside that the network is neither certified nor refuted."
    }

    // ---- Information flow (Phase L1) ----

    /**
     * A noninterference (no-leak) refutation: the security level of a returned value exceeds the result's
     * declared classification, so high information could flow to a low observer. The obligation is the lattice
     * order {@code leq(ΓE(return), L(result))}.
     */
    static String formatInformationLeak(String methodName, String returnText, String outLevel,
                                        CheckResult result) {
        implicit("Possible information leak: '${returnText}' may carry data above the result's '${outLevel}' classification",
            "leq(level(${returnText}), ${outLevel})",
            "Could not decide information-flow obligation for ${methodName}", result)
    }

    /**
     * An interprocedural noninterference refutation: an argument's security level exceeds the classification of
     * the sink parameter it flows into. The "a secret reaches a public sink (a query/log/response argument)" shape.
     */
    static String formatSinkLeak(String methodName, String argText, String callee, String paramName,
                                 String paramLevel, CheckResult result) {
        implicit("Possible information leak: '${argText}' may carry data above the '${paramLevel}' classification of parameter '${paramName}' of ${callee}",
            "leq(level(${argText}), ${paramLevel})",
            "Could not decide information-flow obligation for ${methodName}", result)
    }

    /**
     * A §III-A secure-update refutation: assigning a control variable would leave a variable it controls holding
     * data above its new, lower classification — "flip the flag public while it still holds a secret".
     */
    static String formatSecureUpdate(String methodName, String controlVar, String controlled, CheckResult result) {
        implicit("Possible information leak: updating control variable '${controlVar}' would leave '${controlled}' holding data above its new classification",
            "leq(level(${controlled}), L(${controlled})[${controlVar} := …])",
            "Could not decide secure-update obligation for ${methodName}", result)
    }

    /**
     * A rely/guarantee compatibility lemma that does not hold — the {@code @Rely}/{@code @Guarantee} conditions
     * are not well-formed or not compatible (so the per-thread proofs would not compose, Smith §IV).
     */
    static String formatRelyGuaranteeFailure(String law, CheckResult result) {
        implicit("Rely/guarantee compatibility does not hold: ${law}",
            law,
            "Could not decide rely/guarantee compatibility: ${law}", result)
    }

    // ---- Guarantee conformance (Phase 244) ----

    /**
     * Phase 244 — a body method does not honour the guarantee it declares: the method's own-step
     * transition (env step excluded) violates the {@code @Guarantee(role)} predicate. This is the
     * obligation that makes the peers' rely assumptions justified — the §VII lemma chain closes
     * only if each thread actually does what its guarantee says.
     */
    static String formatGuaranteeConformanceFailure(String methodName, String predName, String role,
                                                    CheckResult result) {
        implicit("Guarantee conformance does not hold: '${methodName}' violates its declared " +
                 "guarantee '${predName}' (${role})",
            "${predName}(old-state, new-state) at every exit of ${methodName}",
            "Could not decide guarantee conformance of '${methodName}' against '${predName}' (${role})",
            result)
    }

    /** Phase 244 — a conformance declaration outside the checkable shape: loud skip. */
    static String formatGuaranteeConformanceSkipped(String methodName, String reason) {
        "Skipped guarantee-conformance check for ${methodName} (${reason}). A checkable declaration " +
        "is @Guarantee('Role') on an instance method of a class whose @Guarantee('Role') predicate's " +
        "post-state parameters name its fields. The declaration is neither checked nor assumed."
    }

    /** Phase 244 — a rely assumed via @UnderRely with no peer @Guarantee predicate to justify it. */
    static String formatUnbackedRely(String className, String relyName, String role, String methodName) {
        "Unbacked rely in '${className}': '${methodName}' assumes the rely '${relyName}' (${role}) " +
        "via @UnderRely, but no other role declares a @Guarantee predicate — nothing in the class " +
        "justifies the assumption. Declare the peer's @Guarantee: the existing lemmas then check it " +
        "implies this rely, and @Guarantee-annotated methods are checked to honour it."
    }

    /** An information-flow obligation the verifier cannot model (unlabelled source, no lattice, …) — skipped loudly. */
    static String formatLeakSkipped(String methodName, String reason) {
        "Skipped information-flow check for ${methodName} (${reason}). " +
        "The source draws on a value or construct outside the supported fragment " +
        "(labelled parameters, straight-line returns over a same-class security lattice). " +
        "The method is allowed to proceed unchecked."
    }

    static String formatSkipped(String calleeName, String reason) {
        "Skipped verification of precondition for ${calleeName} (${reason}). " +
        "The contract or one of the actual arguments is outside the spike's " +
        "supported fragment (linear int arithmetic, comparisons, boolean ops). " +
        "The call is allowed to proceed unchecked."
    }

    // ---- User assertions (Dafny-style compile-time `assert`) ----

    /** A user {@code assert P} the verifier could not prove holds at that point (or refuted with a counterexample). */
    static String formatAssertion(String assertText, CheckResult result) {
        formatAssertion(assertText, result, false)
    }

    /**
     * As above; when {@code suggestRequires} (the assertion is over a method parameter — usually a caller
     * precondition written as a runtime check), append a hint to lift it to {@code @Requires}, which documents
     * it and is discharged at every call site.
     */
    static String formatAssertion(String assertText, CheckResult result, boolean suggestRequires) {
        StringBuilder sb = new StringBuilder()
        switch (result.status) {
            case CheckResult.Status.REFUTED:
                sb.append("Assertion may not hold: ").append(assertText)
                appendModel(sb, result)               // the head already names the predicate — no redundant obligation line
                break
            case CheckResult.Status.UNKNOWN:
                sb.append("Could not decide assertion: ").append(assertText)
                  .append(" (solver: ").append(result.reason).append(")")
                break
            default:
                return "Verified — no error to report"
        }
        if (suggestRequires) {
            sb.append("\n    hint: if this is a caller precondition, declare it as ")
              .append("@Requires({ ").append(assertText).append(" }) — it is then documented and checked at every call site.")
        }
        sb.toString()
    }

    // ---- Implicit safety obligations (array bounds, division, null deref) ----

    static String formatIndexBounds(String indexText, String sizeTerm, CheckResult result) {
        // Refuted heads mirror the exception a developer would actually hit (Phase 9). The general
        // IndexOutOfBoundsException covers both arrays (AIOOBE) and lists without inferring which.
        implicit("Possible IndexOutOfBoundsException: index may be out of bounds",
            "0 <= ${indexText} && ${indexText} < ${sizeTerm}",
            "Could not decide array index bounds", result)
    }

    static String formatDivisionByZero(String divisorText, CheckResult result) {
        implicit("Possible ArithmeticException: Division by zero",
            "(${divisorText}) != 0",
            "Could not decide divisor non-zero", result)
    }

    static String formatModulusNotPositive(String divisorText, CheckResult result) {
        // Groovy's a.mod(b) delegates to BigInteger.mod, which requires a positive modulus.
        implicit("Possible ArithmeticException: BigInteger: modulus not positive",
            "(${divisorText}) > 0",
            "Could not decide modulus positive", result)
    }

    static String formatNumberFormat(String argText, CheckResult result) {
        // Integer.parseInt(s) throws NumberFormatException unless s is a valid integer numeral.
        implicit("Possible NumberFormatException: not a valid integer",
            "${argText} is a valid integer numeral",
            "Could not decide parse-input well-formed", result)
    }

    static String formatNullDereference(String receiver, String method, CheckResult result) {
        // Groovy's own NPE message for a null receiver: "Cannot invoke method size() on null object".
        String invoked = method ? "method ${method}()" : "a method"
        implicit("Possible NullPointerException: Cannot invoke ${invoked} on null object",
            "${receiver} != null",
            "Could not decide receiver non-null", result)
    }

    /**
     * Phase 44 — refuted-overflow head mirrors the Java exception a developer would see if they
     * had a runtime overflow check (e.g. via {@code Math.addExact}/{@code multiplyExact}). The
     * obligation echoes the {@code INT_MIN..INT_MAX} range the result must satisfy.
     */
    static String formatOverflow(String exprText, String op, int width, CheckResult result) {
        String kindWord =
            (op == '+')   ? "addition" :
            (op == '-')   ? "subtraction" :
            (op == '*')   ? "multiplication" :
            (op == 'neg') ? "negation" :
            (op == 'div') ? "division" :
                            "arithmetic"
        // Phase 44c — the bound follows the operation's promoted width (32-bit int, 64-bit long).
        String typeName = width == 64 ? 'Long' : 'Integer'
        // Division's failure case is the specific pair MIN_VALUE / -1, not a general result-out-of-range —
        // phrase the obligation accordingly so the diagnostic reads true.
        String obligation = (op == 'div') ?
            "!((${exprText}) is ${typeName}.MIN_VALUE / -1)" :
            "${typeName}.MIN_VALUE <= (${exprText}) && (${exprText}) <= ${typeName}.MAX_VALUE"
        implicit("Possible ArithmeticException: ${kindWord} overflows ${width}-bit signed range",
            obligation,
            "Could not decide ${kindWord} stays in ${width}-bit range", result)
    }

    static String formatImplicitSkipped(String kind, String reason) {
        "Skipped ${kind} safety check (${reason}). The expression is outside the " +
        "spike's supported fragment (linear int arithmetic, comparisons, " +
        ".size()/.length, nullity). The access is allowed to proceed unchecked."
    }

    private static String implicit(String refutedHead, String obligation,
                                   String unknownHead, CheckResult result) {
        StringBuilder sb = new StringBuilder()
        switch (result.status) {
            case CheckResult.Status.REFUTED:
                sb.append(refutedHead)
                sb.append("\n    obligation: ").append(obligation)
                appendModel(sb, result)
                break
            case CheckResult.Status.UNKNOWN:
                sb.append(unknownHead).append(" (solver: ").append(result.reason).append(")")
                sb.append("\n    obligation: ").append(obligation)
                break
            default:
                sb.append("Verified — no error to report")
        }
        sb.toString()
    }

    static String formatLoopEstablishment(String methodName, String invariantText, CheckResult result) {
        formatLoopEstablishment(methodName, invariantText, result, false)
    }

    /** Phase 88 — a do-while establishes its invariant *after* the mandatory first iteration, not at
     *  loop entry, so the diagnostic says so (the invariant may well hold on entry yet fail post-body). */
    static String formatLoopEstablishment(String methodName, String invariantText, CheckResult result, boolean doWhile) {
        String where = doWhile ? "holds after the do-while's first iteration" : "holds on entry"
        loopFailure("Cannot prove loop invariant ${where} in ${methodName}",
            "invariant", invariantText,
            "Could not decide loop-invariant establishment in ${methodName}", result)
    }

    static String formatLoopPreservation(String methodName, String invariantText, CheckResult result) {
        loopFailure("Cannot prove loop invariant is preserved by the loop body in ${methodName}",
            "invariant", invariantText,
            "Could not decide loop-invariant preservation in ${methodName}", result)
    }

    /** Phase 65 — a for-in invariant clause over the loop variable that fails for some element. */
    static String formatLoopPerElement(String methodName, String invariantText, CheckResult result) {
        loopFailure("Cannot prove loop invariant holds for every element in ${methodName}",
            "invariant", invariantText,
            "Could not decide per-element loop invariant in ${methodName}", result)
    }

    static String formatLoopProgress(String methodName, String variantText, CheckResult result) {
        loopFailure("Cannot prove loop variant decreases and stays >= 0 in ${methodName}",
            "variant", variantText,
            "Could not decide loop termination in ${methodName}", result)
    }

    static String formatTerminationFailure(String methodName, String measureText, CheckResult result) {
        loopFailure("Cannot prove recursion measure decreases and stays >= 0 at this recursive call in ${methodName}",
            "measure", measureText,
            "Could not decide recursion termination in ${methodName}", result)
    }

    static String formatTerminationSkipped(String methodName, String measureText) {
        "Skipped recursion termination for ${methodName}: measure (${measureText}) is outside the " +
        "spike's supported fragment, so the inductive hypothesis at this recursive call is not justified."
    }

    static String formatLoopSkipped(String methodName, String reason) {
        "Skipped loop verification for ${methodName} (${reason}). " +
        "The loop or its surrounding code uses a construct outside the spike's " +
        "supported fragment (a while-loop carrying @Invariant, straight-line " +
        "prefix/body/suffix, linear int arithmetic). The method proceeds unchecked."
    }

    private static String loopFailure(String refutedHead, String label, String contractText,
                                      String unknownHead, CheckResult result) {
        StringBuilder sb = new StringBuilder()
        switch (result.status) {
            case CheckResult.Status.REFUTED:
                sb.append(refutedHead)
                if (contractText) sb.append("\n    ").append(label).append(": ").append(contractText)
                appendModel(sb, result)
                break
            case CheckResult.Status.UNKNOWN:
                sb.append(unknownHead).append(" (solver: ").append(result.reason).append(")")
                if (contractText) sb.append("\n    ").append(label).append(": ").append(contractText)
                break
            default:
                sb.append("Verified — no error to report")
        }
        sb.toString()
    }

    /** Append the counterexample and, when reconstructed, the runnable failing call (Phase 9). */
    private static void appendModel(StringBuilder sb, CheckResult result) {
        if (result.counterexample) {
            sb.append("\n    counterexample: ").append(formatModel(result.counterexample))
        }
        // Phase 126 — model-derived element notes (e.g. the offending array slot) on their own lines.
        if (result.notes) {
            for (String note : result.notes) sb.append("\n    ").append(note)
        }
        // The bare `fails on:` call IS the default ("message") repro. When a richer repro format is selected
        // (assert/junit/spock), the checker's withRepro renders the call inside that form instead — so suppress
        // this line then, rather than printing the call twice.
        boolean richFormat = REFUTATION_FORMAT != null && REFUTATION_FORMAT != 'message'
        if (result.failingCall && !richFormat) {
            sb.append("\n    fails on: ").append(result.failingCall)
        }
    }

    private static String formatModel(Map<String, Long> ce) {
        if (ce.isEmpty()) return "(solver gave no values)"
        ce.entrySet()
          .collect { "${it.key} = ${it.value}" }
          .sort()
          .join(", ")
    }
}
