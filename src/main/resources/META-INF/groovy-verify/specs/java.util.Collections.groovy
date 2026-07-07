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

// External-specification skeleton: trusted contracts for java.util.Collections — the static
// factory/query surface plus the size-preserving mutators (Phase 229: @Modifies-shaped consumption —
// the caller's list content is havoced and re-constrained by the post-state ensures; size is not
// havoced, which is itself the size-preservation fact). The instance List/Map interfaces gate on
// further receiver-oracle wiring (recorded); shuffle stays unspecced (its only honest post-state
// fact is the permutation, which needs the quantified count the fragment reserves for loop proofs).
package java.util

import groovy.contracts.Ensures
import groovy.contracts.Modifies
import groovy.contracts.Requires
import groovy.contracts.ThrowsIf
import groovy.transform.Pure

class Collections {

    // The List twin of java.util.Arrays#binarySearch: the JDK's rarest contract kind, a TRUE
    // precondition — the javadoc's "the result is undefined" unless sorted.
    @Requires({ list != null && list.indices.every { it == 0 || list[it - 1] <= list[it] } })
    static int binarySearch(List list, Object key) {}

    @Pure
    @Ensures({ result != null && result.size() == 0 })
    static List emptyList() {}

    @Pure
    @Ensures({ result != null && result.size() == 1 })
    static List singletonList(Object o) {}

    // Throws exactly on a negative count — a true iff — and the size fact callers actually use.
    @Pure
    @ThrowsIf(value = { n < 0 }, exception = IllegalArgumentException, woven = false, direct = false)
    @Ensures({ result != null && (n >= 0 ==> result.size() == n) })
    static List nCopies(int n, Object o) {}

    // Throws exactly on an empty collection (a true iff); the ensures is the dominance fact
    // comparable-element proofs lean on (stated over the elements — translates for int-like ones).
    @Pure
    @ThrowsIf(value = { coll.isEmpty() }, exception = NoSuchElementException, woven = false, direct = false)
    @Ensures({ coll.every { result >= it } })
    static Object max(Collection coll) {}

    @Pure
    @ThrowsIf(value = { coll.isEmpty() }, exception = NoSuchElementException, woven = false, direct = false)
    @Ensures({ coll.every { result <= it } })
    static Object min(Collection coll) {}

    @Pure
    @Ensures({ result >= 0 && result <= c.size() && result == c.count(o) })
    static int frequency(Collection c, Object o) {}

    // ── the size-preserving mutators (Phase 229) ──

    @Modifies({ list })
    @Ensures({ list.indices.every { it == 0 || list[it - 1] <= list[it] } })
    static void sort(List list) {}

    @Modifies({ list })
    @Ensures({ list.every { it == obj } })
    static void fill(List list, Object obj) {}

    // Content havoced, size preserved — stated post-state facts limited to what is honestly true
    // for every element type (the elementwise reversal over old.list is the recorded refinement).
    @Modifies({ list })
    static void reverse(List list) {}
}
