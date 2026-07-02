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

/** 'P-range as-list' — 8 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G109_p_range_as_list {

    static final List<Map> CASES = [

        // ---------- Range as a list: contents modelled, immutability enforced (Groovy `[].sum()`-style honesty) ----------
        // A Groovy Range `lo..hi` is an immutable List of `lo, lo+1, …, hi`. The verifier models the contents
        // (so `r[k]` reads `lo + k`) and pins the size, but keeps the range *immutable*: an element write throws
        // UnsupportedOperationException at runtime, so the store is refused. The mutable copies — `[*lo..hi]`
        // (spread) and `(lo..hi).toList()` — bind the same contents into a writable array, so a store threads
        // through and other elements stay intact. Constant bounds; `..` inclusive and `..<` exclusive.
        [group: 'P-range as-list', name: 'toList copy: write threads, other elements intact', ok: true,
         src: tc('class C { @Ensures({ result == -1 }) static int f() { def r = (4..8).toList(); r[2] = -1; r[2] } }')],
        [group: 'P-range as-list', name: 'toList copy: untouched element keeps range value', ok: true,
         src: tc('class C { @Ensures({ result == 4 }) static int f() { def r = (4..8).toList(); r[2] = -1; r[0] } }')],
        [group: 'P-range as-list', name: 'spread copy [*4..8]: write threads', ok: true,
         src: tc('class C { @Ensures({ result == -1 }) static int f() { def r = [*4..8]; r[2] = -1; r[2] } }')],
        [group: 'P-range as-list', name: 'bare range read is the range element', ok: true,
         src: tc('class C { @Ensures({ result == 6 }) static int f() { def r = 4..8; r[2] } }')],
        [group: 'P-range as-list', name: 'exclusive range ..< drops the upper bound', ok: true,
         src: tc('class C { @Ensures({ result == 7 }) static int f() { def r = (4..<8).toList(); r[3] } }')],
        // Whole-list equality against a list literal: `result == [4, 5, -1, 7, 8]` folds to size-equality ∧
        // element-wise equality, so returning the mutated copy and comparing to the literal verifies.
        [group: 'P-range as-list', name: 'whole-list == literal on a returned copy verifies', ok: true,
         src: tc('class C { @Ensures({ result == [4, 5, -1, 7, 8] }) static List<Integer> f() { def r = (4..8).toList(); r[2] = -1; r } }')],
        // Soundness control: a wrong element in the claimed list must refute.
        [group: 'P-range as-list', name: 'whole-list == with a wrong element refutes', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ result == [4, 5, 99, 7, 8] }) static List<Integer> f() { def r = (4..8).toList(); r[2] = -1; r } }')],
        // Immutability: a bare range write throws UnsupportedOperationException, so the verifier refuses it.
        [group: 'P-range as-list', name: 'bare range element write is refused (immutable)', expect: 'ranges are immutable',
         src: tc('class C { @Ensures({ result == -1 }) static int f() { def r = 4..8; r[2] = -1; r[2] } }')],
    ]
}
