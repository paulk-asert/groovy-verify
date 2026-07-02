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

/** 'P51b sum-empty' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G108_p51b_sum_empty {

    static final List<Map> CASES = [

        // The `.sum()` empty edge, by receiver kind (Groovy duck-types the no-arg fold). A primitive *array*'s
        // `[].sum()` is 0, so a whole-array `a.sum()` is empty-safe and verifies. A *List* / sublist's `[].sum()`
        // is null — `a[0..<k]` is `getAt(Range)`, which returns a List — so the bare `a[0..<k].sum()` refuses at
        // the empty edge (see the matrix-sum case above); the seeded `.sum(0)` supplies the zero and is empty-safe.
        // (`Arrays.copyOf(a, n)` is also empty-safe at runtime — it returns an int[] — but a method-call receiver
        // is outside the modelled list/array forms, so the verifier skips it; `.sum(0)` is the verified workaround.)
        [group: 'P51b sum-empty', name: 'whole int[] .sum() is empty-safe (array → 0)', ok: true,
         src: tc('class C { @Requires({ a != null && a.length == 0 }) @Ensures({ a.sum() == 0 }) static void f(int[] a) {} }')],
        [group: 'P51b sum-empty', name: 'sublist .sum(0) is empty-safe (seeded → 0)', ok: true,
         src: tc('class C { @Requires({ a != null && a.length >= 0 }) @Ensures({ a[0..<0].sum(0) == 0 }) static void f(int[] a) {} }')],
        // A *statically* empty sublist `.sum()` is provably null — a crisp refutation (no sum$ axioms, no timeout).
        [group: 'P51b sum-empty', name: 'statically-empty sublist .sum() refuses (crisp)', expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ a != null }) @Ensures({ a[0..<0].sum() == 0 }) static void f(int[] a) {} }')],
        // Arrays.copyOf(a, len) is a fresh int[] → array semantics (empty .sum() is 0), so it's empty-safe.
        [group: 'P51b sum-empty', name: 'Arrays.copyOf(a, 0).sum() is empty-safe (array → 0)', ok: true,
         src: HDR + 'import java.util.Arrays\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Requires({ a != null && a.length == 0 }) @Ensures({ Arrays.copyOf(a, 0).sum() == 0 }) static void f(int[] a) {} }'],
    ]
}
