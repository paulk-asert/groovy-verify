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

/** 'P59 for-loop' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G182_p59_for_loop {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A classic for(init;cond;update) loop with @Invariant/@Decreases verifies bounds + postcondition; a missing precondition refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 59: classic for-loops (desugared to while-shape) ----------
        // The headline win: an array-bounds obligation `a[i]` inside a for-loop body is
        // discharged from the loop @Invariant, exactly as for a while loop.
        [group: 'P59 for-loop', name: 'for-loop bounds verified from invariant', ok: true,
         src: tc('''class C {
                       @Requires({ 0 <= n && n <= a.length })
                       static int sumFor(int[] a, int n) {
                           int s = 0, i = 0
                           @Invariant({ 0 <= i && i <= n })
                           for (i = 0; i < n; i++) { s = s + a[i] }
                           return s
                       }
                   }''')],
        // Drop `n <= a.length` and the in-loop `a[i]` is refuted out of bounds — the for-loop
        // body's obligations are checked under the invariant, which no longer bounds the index.
        [group: 'P59 for-loop', name: 'for-loop bounds refuted (missing precondition)',
         expect: 'IndexOutOfBoundsException',
         src: tc('''class C {
                       @Requires({ 0 <= n })
                       static int sumFor(int[] a, int n) {
                           int s = 0, i = 0
                           @Invariant({ 0 <= i && i <= n })
                           for (i = 0; i < n; i++) { s = s + a[i] }
                           return s
                       }
                   }''')],
        // Postcondition + termination over a for-loop: all four loop VCs discharge, the
        // i++ update normalised to i = i + 1, the init `i = 0` threaded into the prefix.
        [group: 'P59 for-loop', name: 'for-loop postcondition + decreases verified', ok: true,
         src: tc('''class C {
                       @Requires({ n >= 0 })
                       @Ensures({ result == n })
                       static int countUp(int n) {
                           int i = 0
                           @Invariant({ 0 <= i && i <= n })
                           @Decreases({ n - i })
                           for (i = 0; i < n; i++) { }
                           return i
                       }
                   }''')],
        // A broken invariant (`i == 0`, falsified by the i++ update) fails preservation — a
        // loud refutation, not a silent pass: the for-loop rides the same inductive machinery.
        [group: 'P59 for-loop', name: 'for-loop broken invariant refuted',
         expect: 'invariant is preserved',
         src: tc('''class C {
                       @Requires({ n >= 0 })
                       @Ensures({ result == n })
                       static int countUp(int n) {
                           int i = 0
                           @Invariant({ i == 0 })
                           @Decreases({ n - i })
                           for (i = 0; i < n; i++) { }
                           return i
                       }
                   }''')],
        // The compound-assignment update form `i += 1` normalises the same way.
        [group: 'P59 for-loop', name: 'for-loop compound update (i += 1) verified', ok: true,
         src: tc('''class C {
                       @Requires({ n >= 0 })
                       @Ensures({ result == n })
                       static int countUp(int n) {
                           int i = 0
                           @Invariant({ 0 <= i && i <= n })
                           @Decreases({ n - i })
                           for (i = 0; i < n; i += 1) { }
                           return i
                       }
                   }''')],
    ]
}
