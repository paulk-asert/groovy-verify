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

/** 'P77 fp arrays' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G194_p77_fp_arrays {

    static final List<Map> CASES = [

        // ---------- Phase 77: FP-element arrays (double[]) — element reads + predicates ----------
        // A `double[]`'s contents are now an `Array Int FP` (sortFor double → IEEE sort), so `xs[i]` reads
        // are FP and comparisons route to the FP theory. A bounded ∀ over the elements instantiates. (We use
        // `double[]` not `List<Double>` so the contract closures don't hit @TypeChecked generics erasure.)
        [group: 'P77 fp arrays', name: 'double[]: every >= 0 ⇒ xs[0] >= 0', ok: true,
         src: tc('''class C {
                       @Requires({ xs.length > 0 && (0..<xs.length).every { xs[it] >= 0.0d } })
                       @Ensures({ xs[0] >= 0.0d })
                       static void check(double[] xs) { }
                   }''')],
        [group: 'P77 fp arrays', name: 'double[]: every > 0 does not prove >= 1 (FP)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ xs.length > 0 && (0..<xs.length).every { xs[it] > 0.0d } })
                       @Ensures({ xs[0] >= 1.0d })
                       static void check(double[] xs) { }
                   }''')],
        // FP element comparison composes across two indices (no scalar literal needed).
        [group: 'P77 fp arrays', name: 'double[]: sorted-adjacent ⇒ xs[0] <= xs[1]', ok: true,
         src: tc('''class C {
                       @Requires({ xs.length >= 2 && xs[0] <= xs[1] })
                       @Ensures({ xs[1] >= xs[0] })
                       static void check(double[] xs) { }
                   }''')],
        // FP max/min: the witnessed extremum over double[] — but FP is not totally ordered, so the bound
        // holds only under a no-NaN guard. Under `!Double.isNaN`, max bounds every element and max >= min.
        [group: 'P77 fp arrays', name: 'double[] max bounds every element (no-NaN)', ok: true,
         src: tc('''class C {
                       @Requires({ xs.length > 0 && (0..<xs.length).every { !Double.isNaN(xs[it]) } })
                       @Ensures({ (0..<xs.length).every { xs[it] <= xs.max() } })
                       static void check(double[] xs) { }
                   }''')],
        [group: 'P77 fp arrays', name: 'double[] max >= min (no-NaN)', ok: true,
         src: tc('''class C {
                       @Requires({ xs.length > 0 && (0..<xs.length).every { !Double.isNaN(xs[it]) } })
                       @Ensures({ xs.max() >= xs.min() })
                       static void check(double[] xs) { }
                   }''')],
        // Soundness: WITHOUT the no-NaN guard, max does NOT bound every element — a NaN element refutes
        // (NaN <= max is false in IEEE). The verifier refuses it rather than assume well-orderedness.
        [group: 'P77 fp arrays', name: 'double[] max bound needs no-NaN (else refutes)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ xs.length > 0 })
                       @Ensures({ (0..<xs.length).every { xs[it] <= xs.max() } })
                       static void check(double[] xs) { }
                   }''')],
    ]
}
