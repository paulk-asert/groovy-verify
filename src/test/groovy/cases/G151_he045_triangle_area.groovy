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

/** 'HE045 triangle_area' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G151_he045_triangle_area {

    static final List<Map> CASES = [

        // ---------- HumanEval 045 (triangle_area): scalar IEEE-754 FP (Phase 73) ----------
        // triangle_area(a, h) = a * h / 2. With `double` inputs this is the FP fragment: the formula
        // proves, the doctest value 7.5 is exact, and `result >= 0` for positive sides is real FP sign
        // reasoning (a*h/2 is positive-or-+0, never NaN) — not just the formula restated.
        [group: 'HE045 triangle_area', name: 'doctest: area(5,3) == 7.5 (exact in FP)', ok: true,
         src: tc('class C { @Ensures({ result == 7.5d }) static double area() { 5.0d * 3.0d / 2.0d } }')],
        // The formula `result == a*h/2` is NOT trivially true in IEEE-754: if an input is NaN/∞ the result
        // is NaN, and NaN != NaN — so even `x == x` fails. With a finiteness guard it holds and proves.
        [group: 'HE045 triangle_area', name: 'formula: finite sides ⇒ result == a * h / 2', ok: true,
         src: tc('class C { @Requires({ Double.isFinite(a) && Double.isFinite(h) }) @Ensures({ result == a * h / 2.0d }) static double area(double a, double h) { a * h / 2.0d } }')],
        [group: 'HE045 triangle_area', name: 'positive sides ⇒ area >= 0 (FP sign reasoning)', ok: true,
         src: tc('class C { @Requires({ a > 0.0d && h > 0.0d }) @Ensures({ result >= 0.0d }) static double area(double a, double h) { a * h / 2.0d } }')],
        // Honest FP subtlety: area is NOT provably *strictly* positive — tiny positive sides underflow
        // a*h to +0.0, so `result > 0` refutes. A real IEEE-754 fact, false in exact arithmetic.
        [group: 'HE045 triangle_area', name: 'positive sides do NOT guarantee area > 0 (FP underflow)', expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ a > 0.0d && h > 0.0d }) @Ensures({ result > 0.0d }) static double area(double a, double h) { a * h / 2.0d } }')],
    ]
}
