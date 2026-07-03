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

/** 'P-hof' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G216_p_hof {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A java.util.function.Function\'s apply is an uninterpreted congruent function: f(a)==f(a) proves, f(a)==f(b) refutes.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — abstract-carrier laws: higher-order/monadic shapes beyond the grid'

    static final List<Map> CASES = [
        // Phase A (higher-order foundation) — a `java.util.function.Function` parameter's `f.apply(x)` is modelled
        // as an uninterpreted function. Congruence (same arg → same result) is provable; distinctness is not.
        [group: 'P-hof', name: 'apply is congruent: f(a) == f(a) proves', ok: true,
         src: tc('''class C {
                        @Ensures({ f.apply(a) == f.apply(a) })
                        static void refl(java.util.function.Function f, Object a) { } }''')],
        [group: 'P-hof', name: 'apply on distinct args not forced equal: f(a) == f(b) refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ f.apply(a) == f.apply(b) })
                        static void distinct(java.util.function.Function f, Object a, Object b) { } }''')],
        [group: 'P-hof', name: 'apply congruence under an equal-args premise proves', ok: true,
         src: tc('''class C {
                        @Requires({ a == b })
                        @Ensures({ f.apply(a) == f.apply(b) })
                        static void congruent(java.util.function.Function f, Object a, Object b) { } }''')],
        [group: 'P-hof', name: 'CONTROL a==b must not prove f(a)==f(c)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ a == b })
                        @Ensures({ f.apply(a) == f.apply(c) })
                        static void control(java.util.function.Function f, Object a, Object b, Object c) { } }''')],
    ]
}
