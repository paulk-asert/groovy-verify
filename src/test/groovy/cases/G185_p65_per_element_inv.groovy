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

/** 'P65 per-element inv' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G185_p65_per_element_inv {

    static final List<Map> CASES = [

        // ---------- Phase 65: for-in invariants over the loop variable (per-element checks) ----------
        // groovy-contracts checks a loop invariant at body-entry (x bound to the current element), so a
        // clause referencing the loop variable is a per-element check — not a loop-head invariant. With
        // a precondition over the elements, it verifies (was a false positive before: the loop-head
        // check havoced x and "failed" on the empty list, which the runtime never even reaches).
        [group: 'P65 per-element inv', name: 'for-in invariant over x verified from every', ok: true,
         src: tc('''class C {
                       @Requires({ xs.every { it >= 0 } })
                       static void m(List<Integer> xs) {
                           @groovy.contracts.Invariant({ x >= 0 })
                           for (x in xs) { }
                       }
                   }''')],
        // Without a precondition bounding the elements, the per-element invariant refutes — the
        // counterexample names the offending element value (and a non-empty collection), not the
        // spurious empty-list case the loop-head check used to report.
        [group: 'P65 per-element inv', name: 'for-in invariant over x refuted (no element bound)',
         expect: 'holds for every element', refute: 'xs.size() = 0',
         src: tc('''class C {
                       static void m(List<Integer> xs) {
                           @groovy.contracts.Invariant({ x < 5 })
                           for (x in xs) { }
                       }
                   }''')],
        // A mixed invariant: the accumulator clause `s >= 0` is inductive (loop-head), the element
        // clause `x >= 0` is per-element — both discharge, and together prove a non-negative total.
        [group: 'P65 per-element inv', name: 'for-in mixed accumulator + per-element invariant', ok: true,
         src: tc('''class C {
                       @Requires({ xs.every { it >= 0 } })
                       @Ensures({ result >= 0 })
                       static int total(List<Integer> xs) {
                           int s = 0
                           @Invariant({ s >= 0 && x >= 0 })
                           for (x in xs) { s += x }
                           s
                       }
                   }''')],
        // Empty-collection vacuity: a per-element invariant that would be unprovable on an arbitrary
        // element still verifies when the precondition forces the collection empty (the body, and so
        // the per-element check, is never reached).
        [group: 'P65 per-element inv', name: 'for-in per-element vacuous on empty collection', ok: true,
         src: tc('''class C {
                       @Requires({ xs.size() == 0 })
                       static void m(List<Integer> xs) {
                           @groovy.contracts.Invariant({ x > 999 })
                           for (x in xs) { }
                       }
                   }''')],
    ]
}
