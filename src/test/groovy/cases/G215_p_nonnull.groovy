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

/** 'P-nonnull' — 7 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G215_p_nonnull {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'An explicit result != null postcondition proven from a non-null parameter/literal; an unconstrained param refutes.'

    static final List<Map> CASES = [

        // Phase 131 — value-flow nullity: a method can now *prove* it returns non-null (literal / new / concat /
        // known-non-null param), so explicit @Ensures({ result != null }) and the implicit @NonNull form both work.
        [group: 'P-nonnull', name: 'explicit result!=null from non-null param proves', ok: true,
         src: tc('''class C {
                        @Requires({ x != null })
                        @Ensures({ result != null })
                        static String foo(String x) { return x } }''')],
        [group: 'P-nonnull', name: 'explicit result!=null from literal proves', ok: true,
         src: tc('''class C {
                        @Ensures({ result != null })
                        static String foo() { return 'hi' } }''')],
        [group: 'P-nonnull', name: 'explicit result!=null unconstrained param refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result != null })
                        static String foo(String x) { return x } }''')],
        [group: 'P-nonnull', name: '@NonNull return: implicit obligation proves (concat)', ok: true,
         src: HDR + NONNULL_ANN + tc('''class C {
                        @NonNull static String foo(String x, String y) { return x + y } }''')],
        [group: 'P-nonnull', name: '@NonNull return: implicit obligation refutes on nullable param', expect: 'Cannot prove postcondition',
         src: HDR + NONNULL_ANN + tc('''class C {
                        @NonNull static String foo(String x) { return x } }''')],
        [group: 'P-nonnull', name: '@NonNull return composes with an explicit @Ensures', ok: true,
         src: HDR + NONNULL_ANN + tc('''class C {
                        @Requires({ x != null })
                        @Ensures({ result == x })
                        @NonNull static String foo(String x) { return x } }''')],
        // Complementary to NullChecker: alongside it, groovy-verify still catches the nullable-param return its
        // flow analysis passes (NullChecker stays silent here; no double-report). Documents the integration.
        [group: 'P-nonnull', name: '@NonNull caught alongside NullChecker (no double-report)', expect: 'Cannot prove postcondition',
         src: HDR + NONNULL_ANN + tcExt(['groovy.typecheckers.NullChecker', 'verification.VerifyChecker'], '''class C {
                        @NonNull static String foo(String x) { return x } }''')],
    ]
}
