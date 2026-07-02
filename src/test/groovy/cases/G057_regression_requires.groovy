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

/** 'regression @Requires' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G057_regression_requires {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Regression anchors for @Requires (good literal call verifies, bad refutes).'

    static final List<Map> CASES = [

        // ---------- Regression: call-site preconditions ----------
        [group: 'regression @Requires', name: 'bad literal call refuted', expect: 'Cannot prove precondition',
         src: HDR + PRODUCER + tc('class C { static int go() { P.sq(-1) } }')],
        [group: 'regression @Requires', name: 'good literal call verified', ok: true,
         src: HDR + PRODUCER + tc('class C { static int go() { P.sq(5) } }')],
    ]
}
