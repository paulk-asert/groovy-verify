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

/** 'P74 range bounds' — 18 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G197_p74_range_bounds {

    static final List<Map> CASES = [

        // ---------- Phase 74: Range.containsWithinBounds — bounds-only interval predicate ----------
        // The bounds-only test (ignores the step) lowers to min(lo,hi) <= v <= max(lo,hi) in v's sort.
        // Decimal bounds ride the exact-Real comparison path; the step is irrelevant (4 ∉ {1,3,5} as a
        // stepped member, but it IS within the [1,5] bounds — exactly what separates this from contains).
        [group: 'P74 range bounds', name: 'decimal range: 1.5..4 within-bounds 2', ok: true,
         src: tc('class C { @Ensures({ (1.5..4).containsWithinBounds(2) }) static void m() { } }')],
        [group: 'P74 range bounds', name: 'NumberRange(1,5,2) within-bounds 4 (step ignored)', ok: true,
         src: tc('class C { @Ensures({ new NumberRange(1, 5, 2).containsWithinBounds(4) }) static void m() { } }')],
        // Outside the interval refutes (7 > 5).
        [group: 'P74 range bounds', name: 'NumberRange(1,5,2) within-bounds 7 refutes', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ new NumberRange(1, 5, 2).containsWithinBounds(7) }) static void m() { } }')],
        // Symbolic — not constant folding: a param constrained into [1,5] is provably within bounds.
        [group: 'P74 range bounds', name: 'symbolic: x in [1,5] ⇒ (1..5) within-bounds x', ok: true,
         src: tc('class C { @Requires({ x >= 1 && x <= 5 }) @Ensures({ (1..5).containsWithinBounds(x) }) static void m(int x) { } }')],
        // ...and only the lower guard is not enough — x could exceed 5, so it refutes.
        [group: 'P74 range bounds', name: 'symbolic: x >= 1 alone does not prove within-bounds', expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ x >= 1 }) @Ensures({ (1..5).containsWithinBounds(x) }) static void m(int x) { } }')],
        // A character range needs String ordering (not modelled) — honest loud skip, not a crash.
        [group: 'P74 range bounds', name: 'char range within-bounds skips loudly', expect: 'outside fragment',
         src: tc("class C { @Ensures({ ('a'..'c').containsWithinBounds('b') }) static void m() { } }")],
        // --- All four delimited-range forms, with per-endpoint inclusivity (Groovy 4+ `<..` / `..<`). ---
        // The forms below all denote {2,3,4}, so each contains 2 within bounds; the endpoint forms differ
        // only at the boundary, which the discriminating cases pin down.
        [group: 'P74 range bounds', name: 'left-open 1<..4 within-bounds 2', ok: true,
         src: tc('class C { @Ensures({ (1<..4).containsWithinBounds(2) }) static void m() { } }')],
        [group: 'P74 range bounds', name: 'open 1<..<5 within-bounds 3', ok: true,
         src: tc('class C { @Ensures({ (1<..<5).containsWithinBounds(3) }) static void m() { } }')],
        [group: 'P74 range bounds', name: 'right-open 2..<5 includes left endpoint 2', ok: true,
         src: tc('class C { @Ensures({ (2..<5).containsWithinBounds(2) }) static void m() { } }')],
        // Boundary discrimination: left-exclusivity EXCLUDES the left endpoint, so this refutes...
        [group: 'P74 range bounds', name: 'left-open 1<..4 excludes 1 (refutes)', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ (1<..4).containsWithinBounds(1) }) static void m() { } }')],
        // ...and right-exclusivity excludes the right endpoint.
        [group: 'P74 range bounds', name: 'right-open 2..<5 excludes 5 (refutes)', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ (2..<5).containsWithinBounds(5) }) static void m() { } }')],
        [group: 'P74 range bounds', name: 'open 1<..<5 excludes both ends (refutes at 5)', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ (1<..<5).containsWithinBounds(5) }) static void m() { } }')],
        // Symbolic + exclusivity: the strict lower guard `x > 1` is exactly what a left-open range needs.
        [group: 'P74 range bounds', name: 'symbolic: x in (1,4] ⇒ (1<..4) within-bounds x', ok: true,
         src: tc('class C { @Requires({ x > 1 && x <= 4 }) @Ensures({ (1<..4).containsWithinBounds(x) }) static void m(int x) { } }')],
        // ...and a non-strict `x >= 1` is NOT enough — x == 1 is excluded by the open left, so it refutes.
        [group: 'P74 range bounds', name: 'symbolic: x >= 1 does not prove left-open membership', expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ x >= 1 && x <= 4 }) @Ensures({ (1<..4).containsWithinBounds(x) }) static void m(int x) { } }')],
        // Open decimal range (NumberRange) is pure-bounds, so any real value is exact.
        [group: 'P74 range bounds', name: 'decimal open 1.5<..<4.5 within-bounds 2', ok: true,
         src: tc('class C { @Ensures({ (1.5<..<4.5).containsWithinBounds(2) }) static void m() { } }')],
        // Pure bounds for every range kind (the documented `Range` contract): a non-integer value is
        // within the integer range's bounds, so it proves. (Stock IntRange.containsWithinBounds currently
        // delegates to `contains` and returns false here — a Groovy bug raised upstream; the verifier
        // models the documented pure-bounds semantics, consistent with NumberRange and the coming fix.)
        [group: 'P74 range bounds', name: 'int range within-bounds 2.5 (pure bounds, per contract)', ok: true,
         src: tc('class C { @Ensures({ (2..4).containsWithinBounds(2.5) }) static void m() { } }')],
        // The decimal-typed equivalent already agrees today — same interval, same answer (no type dependence).
        [group: 'P74 range bounds', name: 'decimal range within-bounds 2.5 agrees', ok: true,
         src: tc('class C { @Ensures({ (2.0..4.0).containsWithinBounds(2.5) }) static void m() { } }')],
        // Out of bounds still refutes regardless of integrality.
        [group: 'P74 range bounds', name: 'int range within-bounds 4.5 refutes', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ (2..4).containsWithinBounds(4.5) }) static void m() { } }')],
    ]
}
