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

/** 'P decl forms' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G116_p_decl_forms {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Local declaration forms def / var / val are interchangeable in the fragment.'

    static final List<Map> CASES = [

        // Placeholder / inferred-type local declarations all lower to the same DeclarationExpression
        // (the verifier binds the local to the RHS in its inferred sort), so `def` (dynamic), `var`
        // (Java-style inference) and `val` (final, Groovy 5+) are interchangeable in the fragment.
        [group: 'P decl forms', name: 'def x = 1', ok: true,
         src: tc('class C { @Ensures({ result == 1 }) static int f() { def x = 1; x } }')],
        [group: 'P decl forms', name: 'var y = 2', ok: true,
         src: tc('class C { @Ensures({ result == 2 }) static int f() { var y = 2; y } }')],
        [group: 'P decl forms', name: 'val z = 3 (final local)', ok: true,
         src: tc('class C { @Ensures({ result == 3 }) static int f() { val z = 3; z } }')],
        // `var` stays mutable — reassignment threads through value-flow.
        [group: 'P decl forms', name: 'var reassignment threads', ok: true,
         src: tc('class C { @Ensures({ result == 5 }) static int f() { var y = 2; y = 5; y } }')],
    ]
}
