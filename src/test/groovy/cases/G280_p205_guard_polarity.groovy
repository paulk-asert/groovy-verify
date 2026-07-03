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

/** 'P205 guard polarity' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G280_p205_guard_polarity {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The NotExpression-IS-A-BooleanExpression trap, fixed and pinned: Groovy\'s NotExpression subclasses BooleanExpression, so a naive BooleanExpression unwrap silently DROPS the negation — an else-branch obligation was discharged under the POSITIVE guard (splitConjuncts), and closed evaluation computed !x as x (PureEvaluator/ContractTester). Verifies: else-branch array stores in annotated loops (both constant- and symbolic-split shapes), a boolean local havocked across an inner loop in its own sort (no more Int/Bool cast crash), and a pure helper with negation evaluating correctly. Teeth: a genuinely out-of-range else store still refutes; the negated helper claim refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 205: else-guard polarity + sort-aware havoc ----------
        // The else fact !(cond) now survives splitConjuncts (NotExpression must not be unwrapped as a
        // plain BooleanExpression): the else-branch store discharges under k >= 2.
        [group: 'P205 guard polarity', name: 'else-branch store in a loop discharges under the negated guard', ok: true,
         src: tc('''class C {
                       @Requires({ a != null && b != null && a.length == 5 && b.length == 5 })
                       static void f(int[] a, int[] b) {
                           int k = 0
                           @Invariant({ 0 <= k && k <= 5 })
                           @Decreases({ 5 - k })
                           while (k < 5) {
                               if (k < 2) { a[k] = 1 } else { b[k - 2] = 2 }
                               k = k + 1
                           }
                       }
                   }''')],
        // The symbolic-split (leftpad) shape: definitions carried by the invariant, else store in range.
        [group: 'P205 guard polarity', name: 'symbolic-split else store discharges', ok: true,
         src: tc('''class C {
                       @Requires({ s != null && n >= 0 })
                       static void f(int c, int n, int[] s) {
                           int pad = n > s.length ? n - s.length : 0
                           int[] r = new int[pad + s.length]
                           int k = 0
                           @Invariant({ 0 <= k && k <= pad + s.length &&
                                        pad == (n > s.length ? n - s.length : 0) &&
                                        r.length == pad + s.length })
                           @Decreases({ pad + s.length - k })
                           while (k < pad + s.length) {
                               if (k < pad) { r[k] = c } else { r[k] = s[k - pad] }
                               k = k + 1
                           }
                       }
                   }''')],
        // Teeth: an else store that is genuinely out of range refutes — the fix did not suppress checks.
        [group: 'P205 guard polarity', name: 'genuinely out-of-range else store still refutes', expect: 'IndexOutOfBounds',
         src: tc('''class C {
                       @Requires({ a != null && b != null && a.length == 5 && b.length == 2 })
                       static void f(int[] a, int[] b) {
                           int k = 0
                           @Invariant({ 0 <= k && k <= 5 })
                           @Decreases({ 5 - k })
                           while (k < 5) {
                               if (k < 2) { a[k] = 1 } else { b[k - 3] = 2 }
                               k = k + 1
                           }
                       }
                   }''')],
        // A boolean local written by an inner loop is havocked in its OWN sort at the outer level —
        // previously an internal Int-to-Bool cast crash (loud skip); now the method verifies.
        [group: 'P205 guard polarity', name: 'boolean local havocs across an inner loop in its own sort', ok: true,
         src: tc('''class C {
                       @Requires({ a != null && r != null && r.length == a.length })
                       @Ensures({ 0 <= result && result <= a.length })
                       static int f(int[] a, int[] r) {
                           int m = 0
                           int i = 0
                           @Invariant({ 0 <= i && i <= a.length && 0 <= m && m <= i })
                           @Decreases({ a.length - i })
                           while (i < a.length) {
                               boolean found = false
                               int j = 0
                               @Invariant({ 0 <= j && j <= m && m <= i && i < a.length && 0 <= i })
                               @Decreases({ m - j })
                               while (j < m) {
                                   if (r[j] == a[i]) { found = true }
                                   j = j + 1
                               }
                               if (found) { r[m] = a[i]; m = m + 1 }
                               i = i + 1
                           }
                           return m
                       }
                   }''')],
        // Closed evaluation of a pure helper containing a negation: !(4 % 2 == 0) is false — pre-fix the
        // BooleanExpression unwrap evaluated !x as x and this pair inverted.
        [group: 'P205 guard polarity', name: 'pure-helper negation evaluates correctly', ok: true,
         src: tc('''class C {
                       static boolean isOdd(int n) { !(n % 2 == 0) }
                       @Ensures({ result })
                       static boolean f() { isOdd(3) }
                   }''')],
        [group: 'P205 guard polarity', name: 'negated helper claim refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       static boolean isOdd(int n) { !(n % 2 == 0) }
                       @Ensures({ result })
                       static boolean f() { isOdd(4) }
                   }''')],
    ]
}
