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

/** 'P73 floating point' — 12 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G196_p73_floating_point {

    static final List<Map> CASES = [

        // ---------- Phase 73: IEEE-754 floating point (double/float via Z3's FP theory) ----------
        // The flagship pairing — the same expression, two number models, both proven:
        //   BigDecimal is exact decimal, so 0.1 + 0.2 IS 0.3;
        //   double is IEEE-754, so 0.1d + 0.2d is NOT 0.3d (it is 0.30000000000000004).
        [group: 'P73 floating point', name: 'BigDecimal: 0.1 + 0.2 == 0.3 (exact)', ok: true,
         src: tc('class C { @Ensures({ result == 0.3 }) static BigDecimal f() { 0.1 + 0.2 } }')],
        [group: 'P73 floating point', name: 'double: 0.1d + 0.2d != 0.3d (IEEE-754)', ok: true,
         src: tc('class C { @Ensures({ result != 0.3d }) static double f() { 0.1d + 0.2d } }')],
        // Soundness anchor: claiming the double sum IS 0.3 is refuted (it genuinely is not).
        [group: 'P73 floating point', name: 'double: claiming == 0.3d refutes', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ result == 0.3d }) static double f() { 0.1d + 0.2d } }')],
        // FP exact cases still prove (powers of two are representable).
        [group: 'P73 floating point', name: 'double: 0.5d * 2.0d == 1.0d (exact)', ok: true,
         src: tc('class C { @Ensures({ result == 1.0d }) static double f() { 0.5d * 2.0d } }')],
        // No-NaN / finiteness — the highest-value FP safety class: a finite input stays non-NaN.
        [group: 'P73 floating point', name: 'double: finite input ⇒ result not NaN', ok: true,
         src: tc('class C { @Requires({ Double.isFinite(x) }) @Ensures({ !Double.isNaN(result) }) static double g(double x) { x + x } }')],
        // ...and an unconstrained input can be NaN, so the no-NaN claim refutes without the guard.
        [group: 'P73 floating point', name: 'double: no-NaN needs the finite guard', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ !Double.isNaN(result) }) static double g(double x) { x + x } }')],
        // IEEE equality: NaN != NaN. `x == x` is false for a NaN, so claiming it holds for any x refutes.
        [group: 'P73 floating point', name: 'double: x == x not universal (NaN)', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ x == x }) static double g(double x) { x } }')],
        // Math.sqrt / Math.abs (Z3 fp.sqrt / fp.abs): sqrt of a non-negative is non-negative and not NaN.
        [group: 'P73 floating point', name: 'Math.sqrt of non-negative is non-negative', ok: true,
         src: tc('class C { @Requires({ x >= 0.0d }) @Ensures({ result >= 0.0d }) static double f(double x) { Math.sqrt(x) } }')],
        [group: 'P73 floating point', name: 'Math.sqrt of non-negative is not NaN', ok: true,
         src: tc('class C { @Requires({ x >= 0.0d }) @Ensures({ !Double.isNaN(result) }) static double f(double x) { Math.sqrt(x) } }')],
        // ...but sqrt of a possibly-negative input CAN be NaN — the no-NaN claim refutes without the guard.
        [group: 'P73 floating point', name: 'Math.sqrt without guard can be NaN', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ !Double.isNaN(result) }) static double f(double x) { Math.sqrt(x) } }')],
        // Math.abs is non-negative for any non-NaN input, and never negative (soundness anchor).
        [group: 'P73 floating point', name: 'Math.abs of non-NaN is non-negative', ok: true,
         src: tc('class C { @Requires({ !Double.isNaN(x) }) @Ensures({ result >= 0.0d }) static double f(double x) { Math.abs(x) } }')],
        [group: 'P73 floating point', name: 'Math.abs claiming negative refutes', expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ !Double.isNaN(x) }) @Ensures({ result < 0.0d }) static double f(double x) { Math.abs(x) } }')],
    ]
}
