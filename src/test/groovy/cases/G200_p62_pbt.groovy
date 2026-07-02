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
package cases

import static cases.CaseDsl.*

/** 'P62 pbt' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G200_p62_pbt {

    static final List<Map> CASES = [

        // ---------- Phase 62: bounded property-based refutation when the solver says UNKNOWN ----------
        // `result == Fib.of(n)` is the weak refutation direction (recurrence-axiom timeout → UNKNOWN);
        // bounded testing of the executable contract finds the concrete failing input f(2): the body
        // returns 2 but Fib.of(2) is 1. UNKNOWN becomes a runnable repro.
        [group: 'P62 pbt', name: 'Fib UNKNOWN refuted by testing (fails on f(2))',
         expect: 'fails on: f(2)',
         src: tc('class C { @Requires({ n >= 0 }) @Ensures({ result == Fib.of(n) }) static int f(int n) { n } }')],
        // The diagnostic is explicit that the counterexample came from testing, not a proof.
        [group: 'P62 pbt', name: 'Fib off-by-const UNKNOWN refuted by testing',
         expect: 'counterexample found by bounded testing',
         src: tc('class C { @Requires({ n >= 2 }) @Ensures({ result == Fib.of(n) + 1 }) static int f(int n) { n } }')],
        // Honest bail: an array-`sum()` postcondition is UNKNOWN (aggregation-axiom timeout), but the
        // concrete tester can't evaluate array contents, so it finds nothing and the diagnostic stays an
        // honest "could not decide" — bounded testing never fabricates a false refutation outside its
        // (integer-only) fragment.
        [group: 'P62 pbt', name: 'array-sum UNKNOWN stays could-not-decide (testing bails)',
         expect: 'Could not decide postcondition',
         src: tc('class C { @Requires({ a != null && a.length > 0 }) @Ensures({ result == a.sum() }) static int f(int[] a) { 0 } }')],
    ]
}
