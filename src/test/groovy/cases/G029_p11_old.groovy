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

/** 'P11 old' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G029_p11_old {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'old(...) snapshots pre-state field and array contents, so a mutator\'s post/pre delta is checked; a wrong delta refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 11: old(...) pre-state — relate the result to the method's entry state ----------
        // Scalar field delta: the exit count is the entry count plus one.
        [group: 'P11 old', name: 'field delta vs old', ok: true,
         src: tc('''class C {
                       int count
                       @Ensures({ count == old.count + 1 })
                       void inc() { count = count + 1 }
                   }''')],
        // Soundness: a body that doesn't match the old-delta is refuted.
        [group: 'P11 old', name: 'wrong old delta refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       int count
                       @Ensures({ count == old.count + 1 })
                       void inc() { count = count + 2 }
                   }''')],
        // Array element FRAME (the @Modifies enabler): a setter changes only a[j]; every other
        // element equals its old value. `old.a[it]` is the entry snapshot of the array's contents.
        [group: 'P11 old', name: 'array element frame via old', ok: true,
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= j && j < a.length })
                       @Ensures({ (0..<a.length).every { it == j || a[it] == old.a[it] } })
                       void set(int j, int v) { a[j] = v }
                   }''')],
    ]
}
