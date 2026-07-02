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

/** 'PL-infer' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G243_pl_infer {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Loop-invariant inference for a bare counter loop (opt-in VerifyChecker(inferLoops: true)) proves array bounds with no @Invariant.'

    static final List<Map> CASES = [

        // ----- Loop-invariant INFERENCE for a bare counting loop -----
        // Opt-in via the parameterised extension syntax `@TypeChecked(extensions='verification.VerifyChecker(inferLoops: true)')`
        // (the `tci` helper) — the same mechanism NullChecker uses for `strict`. A `for (int i = 0; i < a.length; i++)`
        // array walk verifies its bounds with NO hand-written @Invariant: the engine infers the lower-bound invariant
        // `0 <= i` (sound by construction); the upper bound `i < a.length` comes from the guard.
        [group: 'PL-infer', name: 'counter loop over array bounds — inferred, no @Invariant', ok: true,
         src: tci('''class C {
                       static int sum(int[] a) {
                           int s = 0
                           for (int i = 0; i < a.length; i++) { s = s + a[i] }   // array bounds PROVEN — no @Invariant written
                           return s
                       }
                   }''')],
        // Inference also discharges a `@Requires`-bounded walk: guard `i < n` + `n <= a.length` + inferred `0 <= i`.
        [group: 'PL-infer', name: 'counter loop to n under @Requires — inferred', ok: true,
         src: tci('''class C {
                       @Requires({ n <= a.length })
                       static int sumN(int[] a, int n) {
                           int s = 0
                           for (int i = 0; i < n; i++) { s = s + a[i] }
                           return s
                       }
                   }''')],
        // Negative control — WITHOUT inference (default), the bare loop has no invariant, so the per-method havoc
        // pass can't see `i` is bounded and reports a *possible* OOB. Inference (above) supplies `0 <= i` and the
        // report disappears — so this slice actually REMOVES a false positive, and is genuinely opt-in (default off).
        [group: 'PL-infer', name: 'same loop without inference reports possible OOB (default off)',
         expect: 'IndexOutOfBoundsException',
         src: tc('''class C {
                       static int sum(int[] a) {
                           int s = 0
                           for (int i = 0; i < a.length; i++) { s = s + a[i] }
                           return s
                       }
                   }''')],
    ]
}
