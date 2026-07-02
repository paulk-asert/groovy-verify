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

/** 'P9 any' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G027_p9_any {

    static final List<Map> CASES = [

        // ---------- Phase 9: existential quantifier (`any`) + precise membership ----------
        // An assumed `any` (∃) carries across to the same claim (a positive ∃ goal from a ∃ premise).
        [group: 'P9 any', name: 'element any assumed entails', ok: true,
         src: tc('class C { @Requires({ a.any { it < 0 } }) @Ensures({ a.any { it < 0 } }) static int f(int[] a) { 0 } }')],
        // Existential GOAL with a witness: the element at a valid index is in the array.
        [group: 'P9 any', name: 'any proves membership at a valid index', ok: true,
         src: tc('class C { @Requires({ 0 <= k && k < a.length }) @Ensures({ a.any { it == a[k] } }) static int f(int[] a, int k) { 0 } }')],
        // Range form: `(0..<n).any { … }` is the same existential over indices.
        [group: 'P9 any', name: 'range.any entails element any', ok: true,
         src: tc('class C { @Requires({ (0..<a.length).any { a[it] < 0 } }) @Ensures({ a.any { it < 0 } }) static int f(int[] a) { 0 } }')],
        // Not vacuous: with nothing assumed, an existential claim cannot be proved.
        [group: 'P9 any', name: 'unproven any refuted', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ a.any { it < 0 } }) static int f(int[] a) { 0 } }')],
        // `contains` is now precise (relates to actual contents): a[k] is contained for a valid k —
        // the old opaque uninterpreted predicate could not prove this.
        [group: 'P9 any', name: 'precise contains at a valid index', ok: true,
         src: tc('class C { @Requires({ 0 <= k && k < a.length }) @Ensures({ a.contains(a[k]) }) static int f(int[] a, int k) { 0 } }')],
    ]
}
