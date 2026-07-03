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

/** 'nonnull param' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G004_nonnull_param {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A @NonNull-style annotation (NullChecker / Checker Framework / JSR-305 vocabulary) on a reference parameter is read as a non-null precondition, discharging a deref or apply the unannotated form could not.'

    static final List<Map> CASES = [

        // ---------- @NonNull parameter read as a non-null precondition (NullChecker / Checker Framework vocabulary) ----------
        [group: 'nonnull param', name: '@NonNull param discharges a deref', ok: true,
         src: HDR + NONNULL_ANN + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { static int len(@NonNull String s) { s.length() } }'],
        // The unannotated twin (`static int n(String s) { s.length() }`) refutes — see P1 null / P9 repro.
        [group: 'nonnull param', name: '@NonNull function param discharges apply (the Maybe shape)', rung: 'C — abstract-carrier laws: higher-order/monadic shapes beyond the grid', ok: true,
         src: HDR + NONNULL_ANN + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { static Object call(@NonNull java.util.function.Function g, Object x) { g.apply(x) } }'],
    ]
}
