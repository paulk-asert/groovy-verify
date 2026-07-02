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

/** 'P64 loop-stable req' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G184_p64_loop_stable_req {

    static final List<Map> CASES = [

        // ---------- Phase 64: loop-stable @Requires (element reasoning from a precondition) ----------
        // The unlock: preservation may assume @Requires conjuncts the loop can't invalidate. The body
        // only reads xs, so `xs.every { it >= 0 }` is stable and instantiates at the current element —
        // a running total of non-negative elements is provably non-negative. (Previously refuted:
        // preservation had no way to know x >= 0.)
        [group: 'P64 loop-stable req', name: 'for-in total over non-negative verified', ok: true,
         src: tc('''class C {
                       @Requires({ xs.every { it >= 0 } })
                       @Ensures({ result >= 0 })
                       static int total(List<Integer> xs) {
                           int s = 0
                           @Invariant({ s >= 0 })
                           for (x in xs) { s = s + x }
                           return s
                       }
                   }''')],
        // The precondition is load-bearing: drop it and preservation refutes (x may be negative) —
        // confirming the verification above rests on the assumed element fact, not a vacuity.
        [group: 'P64 loop-stable req', name: 'for-in total without precondition refuted',
         expect: 'invariant is preserved',
         src: tc('''class C {
                       @Ensures({ result >= 0 })
                       static int total(List<Integer> xs) {
                           int s = 0
                           @Invariant({ s >= 0 })
                           for (x in xs) { s = s + x }
                           return s
                       }
                   }''')],
        // Soundness anchor: a precondition over state the loop *modifies* must NOT be assumed. Here the
        // loop decrements `cap`, so `@Requires({ cap >= 1000 })` is dropped — preservation of
        // `cap >= 0` correctly refutes (cap reaches -5). If the stale fact were assumed, this would
        // wrongly verify.
        [group: 'P64 loop-stable req', name: 'precondition over modified state dropped (sound)',
         expect: 'invariant is preserved',
         src: tc('''class C {
                       @Requires({ cap >= 1000 })
                       @Ensures({ result <= 0 })
                       static int drain(int cap) {
                           @Invariant({ cap >= 0 })
                           @Decreases({ cap + 5 })
                           while (cap > -5) { cap = cap - 1 }
                           return cap
                       }
                   }''')],
        // A precondition over an *unmodified* parameter is assumed in a plain while loop too: the
        // lower bound `lo` is never written, so `s >= lo` is preserved by `s = s + 1` given `lo <= 0`.
        [group: 'P64 loop-stable req', name: 'while-loop stable precondition assumed', ok: true,
         src: tc('''class C {
                       @Requires({ lo <= 0 && n >= 0 })
                       @Ensures({ result >= lo })
                       static int countFrom(int lo, int n) {
                           int s = lo
                           int i = 0
                           @Invariant({ 0 <= i && i <= n && s >= lo })
                           @Decreases({ n - i })
                           while (i < n) { s = s + 1; i = i + 1 }
                           return s
                       }
                   }''')],
    ]
}
