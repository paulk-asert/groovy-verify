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

/** 'P149 null-return' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G012_p149_null_return {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A reference-typed method that returns null on a path (e.g. a bounded queue\'s Integer poll() → null when empty) still verifies its @Invariant / @Ensures over other state: result binds as null, so result == null proves and result != null refutes. This lets the exact SpscBuffer.groovy source verify under groovy-verify (SpscBufferVerifyTest).'

    static final List<Map> CASES = [

        // ---------- Phase 149: `return null` from a reference-typed method ----------
        // A method may return null on a path (e.g. a bounded queue's `Integer poll()` → null when empty). The value
        // isn't an Int, but the method's @Invariant / @Ensures over OTHER state is still checkable: `result` binds as
        // null. This is what lets the *exact* SpscBuffer.groovy source (Integer poll) verify — see SpscBufferVerifyTest.
        [group: 'P149 null-return', name: 'Integer poll returns null on empty, invariant preserved', ok: true,
         src: tc('''@Invariant({ capacity > 0 && items.length == capacity && 0 <= head && head <= tail && tail - head <= capacity })
                    class Ring {
                        int[] items
                        int capacity
                        int head
                        int tail
                        Integer poll() {
                            int h = head
                            if (tail - h == 0) return null
                            int v = items[h % capacity]
                            head = h + 1
                            return v
                        }
                    }''')],
        // Nullity is tracked: `return null` proves `result == null`…
        [group: 'P149 null-return', name: 'return null proves result == null', ok: true,
         src: tc('''class C { @Ensures({ result == null }) static Integer f() { return null } }''')],
        // …and refutes a non-null postcondition (sound — it doesn't silently skip).
        [group: 'P149 null-return', name: 'return null refutes result != null', expect: 'Cannot prove postcondition',
         src: tc('''class C { @Ensures({ result != null }) static Integer f() { return null } }''')],
    ]
}
