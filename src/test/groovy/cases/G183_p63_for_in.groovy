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

/** 'P63 for-in' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G183_p63_for_in {

    static final List<Map> CASES = [
        // ---------- Phase 63: for-in loops (synthesized hidden index, loop var retained) ----------
        // `for (x in xs)` desugars to an indexed while: a hidden index drives iteration, the loop
        // variable `x` is bound to xs[idx] each pass. Element reasoning comes from the body's
        // structure (preservation doesn't assume @Requires): |x| is provably >= 0, so a running
        // sum of absolute values stays >= 0 — verified, with auto-injected index bounds + termination.
        [group: 'P63 for-in', name: 'for-in sum-of-abs stays non-negative', ok: true,
         src: tc('''class C {
                       @Ensures({ result >= 0 })
                       static int sumAbs(List<Integer> xs) {
                           int s = 0
                           @Invariant({ s >= 0 })
                           for (x in xs) { s = s + (x < 0 ? -x : x) }
                           return s
                       }
                   }''')],
        // The Java-style colon syntax `for (T x : xs)` parses to the same ForStatement and verifies
        // identically to the `in` form.
        [group: 'P63 for-in', name: 'for-colon (Java-style) verified', ok: true,
         src: tc('''class C {
                       @Ensures({ result >= 0 })
                       static int sumAbs(List<Integer> xs) {
                           int s = 0
                           @Invariant({ s >= 0 })
                           for (int x : xs) { s = s + (x < 0 ? -x : x) }
                           return s
                       }
                   }''')],
        // Conditional accumulation over the loop variable: a count only ever grows, so c >= 0 holds.
        [group: 'P63 for-in', name: 'for-in conditional count stays non-negative', ok: true,
         src: tc('''class C {
                       @Ensures({ result >= 0 })
                       static int countEvens(List<Integer> xs) {
                           int c = 0
                           @Invariant({ c >= 0 })
                           for (x in xs) { if (x % 2 == 0) c = c + 1 }
                           return c
                       }
                   }''')],
        // Loud refutation, not a silent pass: `s == 0` isn't preserved by `s = s + x` (x may be
        // non-zero). The counterexample names the loop variable `x`, not the hidden index.
        [group: 'P63 for-in', name: 'for-in broken invariant refuted (preservation)',
         expect: 'invariant is preserved',
         src: tc('''class C {
                       @Ensures({ result == 0 })
                       static int sumIn(List<Integer> xs) {
                           int s = 0
                           @Invariant({ s == 0 })
                           for (x in xs) { s = s + x }
                           return s
                       }
                   }''')],
        // The synthetic index is hidden — the counterexample reads in terms of the loop variable,
        // never `__gvForInIdx`.
        [group: 'P63 for-in', name: 'for-in counterexample hides synthetic index',
         expect: 'invariant is preserved', refute: '__gvForInIdx',
         src: tc('''class C {
                       @Ensures({ result >= 0 })
                       static int sumIn(List<Integer> xs) {
                           int s = 0
                           @Invariant({ s >= 0 })
                           for (x in xs) { s = s + x }
                           return s
                       }
                   }''')],
        // A for-in over a literal (not a named collection) has no size oracle to index — skips loudly.
        [group: 'P63 for-in', name: 'for-in over a list literal skips', expect: 'Skipped',
         src: tc('''class C {
                       @Ensures({ result >= 0 })
                       static int f() {
                           int s = 0
                           @Invariant({ s >= 0 })
                           for (x in [1, 2, 3]) { s = s + x }
                           return s
                       }
                   }''')],
    ]
}
