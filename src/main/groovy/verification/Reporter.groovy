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

    static String formatPostconditionSkipped(String methodName, String reason) {
        "Skipped verification of postcondition for ${methodName} (${reason}). " +
        "The body uses a construct or value outside the spike's supported " +
        "fragment (straight-line code, if/else, single-assignment locals, " +
        "linear int arithmetic). The method is allowed to proceed unchecked."
    }

    static String formatSkipped(String calleeName, String reason) {
        "Skipped verification of precondition for ${calleeName} (${reason}). " +
        "The contract or one of the actual arguments is outside the spike's " +
        "supported fragment (linear int arithmetic, comparisons, boolean ops). " +
        "The call is allowed to proceed unchecked."
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
        if (result.failingCall) {
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
