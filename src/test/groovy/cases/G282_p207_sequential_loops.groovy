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

/** 'P207 sequential loops' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G282_p207_sequential_loops {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'SEQUENTIAL annotated loops in one method (the OpenJML two-loop leftpad shape, and the three-loop merge shape): each loop gets its own establishment/preservation/@Decreases with earlier loops SUMMARISED in its prefix replay (havoc writes, assume inv AND NOT guard), region obligations run per segment under the preceding loop\'s exit state, and the @Ensures walk anchors on the last loop. A later loop must RESTATE any earlier-segment fact it needs (its writes havoc the shared state) — exactly the OpenJML maintaining discipline. Teeth: a dropped carried fact fails the postcondition; a second invariant not established from the first\'s exit state refutes at entry.'

    static final List<Map> CASES = [
        // The OpenJML-shaped two-loop leftpad: fill the pad, then copy the suffix. The second loop's
        // invariant re-states the first segment's fact (exactly as the OpenJML entry's `maintaining`).
        [group: 'P207 sequential loops', name: 'two-loop leftpad (the OpenJML shape)', ok: true,
         src: tc('''class C {
                       @Requires({ s != null && n >= 0 })
                       @Ensures({ result.length == (n > s.length ? n : s.length) &&
                                  (0..<(n > s.length ? n - s.length : 0)).every { int i -> result[i] == c } &&
                                  (0..<s.length).every { int i -> result[(n > s.length ? n - s.length : 0) + i] == s[i] } })
                       static int[] leftpad(int c, int n, int[] s) {
                           int pad = n > s.length ? n - s.length : 0
                           int[] r = new int[pad + s.length]
                           int i = 0
                           @Invariant({ 0 <= i && i <= pad &&
                                        pad == (n > s.length ? n - s.length : 0) &&
                                        r.length == pad + s.length &&
                                        (0..<i).every { int q -> r[q] == c } })
                           @Decreases({ pad - i })
                           while (i < pad) {
                               r[i] = c
                               i = i + 1
                           }
                           int j = 0
                           @Invariant({ 0 <= j && j <= s.length &&
                                        pad == (n > s.length ? n - s.length : 0) &&
                                        r.length == pad + s.length &&
                                        (0..<pad).every { int q -> r[q] == c } &&
                                        (0..<j).every { int q -> r[pad + q] == s[q] } })
                           @Decreases({ s.length - j })
                           while (j < s.length) {
                               r[pad + j] = s[j]
                               j = j + 1
                           }
                           return r
                       }
                   }''')],
        // Two simple scalar loops — the minimal sequential shape (count up, then count down).
        [group: 'P207 sequential loops', name: 'two sequential scalar loops', ok: true,
         src: tc('''class C {
                       @Requires({ n >= 0 })
                       @Ensures({ result == 0 })
                       static int f(int n) {
                           int x = 0
                           int i = 0
                           @Invariant({ 0 <= i && i <= n && x == i })
                           @Decreases({ n - i })
                           while (i < n) {
                               x = x + 1
                               i = i + 1
                           }
                           int j = 0
                           @Invariant({ 0 <= j && j <= n && x == n - j })
                           @Decreases({ n - j })
                           while (j < n) {
                               x = x - 1
                               j = j + 1
                           }
                           return x
                       }
                   }''')],
        // TEETH: the second loop's invariant DROPS the carried first-segment fact — the postcondition's
        // pad-prefix clause must not prove (loop 2 havocs r; the fact needs restating).
        [group: 'P207 sequential loops', name: 'dropped carried fact fails the postcondition', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ s != null && n >= 0 })
                       @Ensures({ (0..<(n > s.length ? n - s.length : 0)).every { int i -> result[i] == c } })
                       static int[] leftpad(int c, int n, int[] s) {
                           int pad = n > s.length ? n - s.length : 0
                           int[] r = new int[pad + s.length]
                           int i = 0
                           @Invariant({ 0 <= i && i <= pad &&
                                        pad == (n > s.length ? n - s.length : 0) &&
                                        r.length == pad + s.length &&
                                        (0..<i).every { int q -> r[q] == c } })
                           @Decreases({ pad - i })
                           while (i < pad) {
                               r[i] = c
                               i = i + 1
                           }
                           int j = 0
                           @Invariant({ 0 <= j && j <= s.length &&
                                        pad == (n > s.length ? n - s.length : 0) &&
                                        r.length == pad + s.length &&
                                        (0..<j).every { int q -> r[pad + q] == s[q] } })
                           @Decreases({ s.length - j })
                           while (j < s.length) {
                               r[pad + j] = s[j]
                               j = j + 1
                           }
                           return r
                       }
                   }''')],
        // TEETH: the second loop's invariant is not ESTABLISHED from the first's exit state.
        [group: 'P207 sequential loops', name: 'unestablished second invariant refutes at entry', expect: 'Cannot prove loop invariant holds on entry',
         src: tc('''class C {
                       @Requires({ n >= 0 })
                       @Ensures({ result == 0 })
                       static int f(int n) {
                           int x = 0
                           int i = 0
                           @Invariant({ 0 <= i && i <= n && x == i })
                           @Decreases({ n - i })
                           while (i < n) {
                               x = x + 1
                               i = i + 1
                           }
                           int j = 0
                           @Invariant({ 0 <= j && j <= n && x == n + 1 - j })
                           @Decreases({ n - j })
                           while (j < n) {
                               x = x - 1
                               j = j + 1
                           }
                           return x
                       }
                   }''')],
        // THREE sequential loops (the merge shape): up, down, up again.
        [group: 'P207 sequential loops', name: 'three sequential scalar loops (the merge shape)', ok: true,
         src: tc('''class C {
                       @Requires({ n >= 0 })
                       @Ensures({ result == n })
                       static int f(int n) {
                           int x = 0
                           int i = 0
                           @Invariant({ 0 <= i && i <= n && x == i })
                           @Decreases({ n - i })
                           while (i < n) { x = x + 1; i = i + 1 }
                           int j = 0
                           @Invariant({ 0 <= j && j <= n && x == n - j })
                           @Decreases({ n - j })
                           while (j < n) { x = x - 1; j = j + 1 }
                           int k = 0
                           @Invariant({ 0 <= k && k <= n && x == k })
                           @Decreases({ n - k })
                           while (k < n) { x = x + 1; k = k + 1 }
                           return x
                       }
                   }''')],
    ]
}
