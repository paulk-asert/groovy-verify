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

/** 'regression @Ensures' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G058_regression_ensures {

    static final List<Map> CASES = [

        // ---------- Regression: postconditions ----------
        [group: 'regression @Ensures', name: 'max verified', ok: true,
         src: tc('class C { @Ensures({ result >= a && result >= b }) static int max(int a, int b) { if (a > b) a else b } }')],
        [group: 'regression @Ensures', name: 'maxBuggy refuted', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ result >= a && result >= b }) static int max(int a, int b) { if (a > b) b else a } }')],
    ]
}
