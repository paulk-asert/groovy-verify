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
                if (result.counterexample) {
                    sb.append("\n    counterexample: ")
                      .append(formatModel(result.counterexample))
                }
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
                if (result.counterexample) {
                    sb.append("\n    counterexample: ")
                      .append(formatModel(result.counterexample))
                }
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

    private static String formatModel(Map<String, Long> ce) {
        if (ce.isEmpty()) return "(solver gave no values)"
        ce.entrySet()
          .collect { "${it.key} = ${it.value}" }
          .sort()
          .join(", ")
    }
}
