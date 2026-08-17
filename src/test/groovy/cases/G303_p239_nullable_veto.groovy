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

/** 'P239 nullable veto' — 8 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G303_p239_nullable_veto {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'An explicit @Nullable/@CheckForNull defeats any @NonNull effect at the same position (nullable wins): the param/field non-null assumption, the implicit field invariant, the element-obligation suppression, and the Phase 131 return obligation.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — annotation-as-contract: the claim is an assumption about the caller, with no groovy-contracts runtime arm'

    static final List<Map> CASES = [

        // ===== Phase 239 — NULLABLE_ANNOTATION_NAMES stops being a declared no-op. In the default mode
        // the unannotated case already carries the implicit obligation, so @Nullable ALONE changes
        // nothing (first case pins that). Its force is precedence: on a contradictory declaration the
        // author's disclaimer wins over every @NonNull-derived effect — the assumption sites and,
        // uniformly, the return obligation. (Non-null-by-default strict mode — full GROOVY-12252
        // parity — is a future phase; this is the matcher wiring it will key off.)
        [group: 'P239 nullable veto', name: 'List<@Nullable String>: the element obligation stays', ok: false, expect: 'Possible NullPointerException',
         src: HDR + NULLABLE_TYPEUSE_ANN + tc('''class C {
                        @Requires({ xs.size() > 0 })
                        static int f(List<@Nullable String> xs) { xs[0].length() } }''')],
        // The both-annotations element: @Nullable defeats the Phase 234 suppression (the @NonNull-only
        // twin in G300 proves).
        [group: 'P239 nullable veto', name: 'List<@NonNull @Nullable String>: nullable wins, still refutes', ok: false, expect: 'Possible NullPointerException',
         src: HDR + NONNULL_TYPEUSE_ANN + NULLABLE_TYPEUSE_ANN + tc('''class C {
                        @Requires({ xs.size() > 0 })
                        static int f(List<@NonNull @Nullable String> xs) { xs[0].length() } }''')],
        // Param assumption: @NonNull alone is assumed in the body (the @Requires posture) …
        [group: 'P239 nullable veto', name: '@NonNull param: the assumption discharges the deref', ok: true,
         src: HDR + NONNULL_TYPEUSE_ANN + tc('''class C {
                        static int m(@NonNull String s) { s.length() } }''')],
        // … and the both-annotations param loses it — assuming non-null over the author's own
        // disclaimer would be the unsound direction.
        [group: 'P239 nullable veto', name: '@NonNull @Nullable param: the assumption is vetoed', ok: false, expect: 'Possible NullPointerException',
         src: HDR + NONNULL_TYPEUSE_ANN + NULLABLE_TYPEUSE_ANN + tc('''class C {
                        static int m(@NonNull @Nullable String s) { s.length() } }''')],
        // Return obligation: the both-annotations return drops the Phase 131 obligation (the
        // @NonNull-only twin in G300 refutes on the same body) — nullable wins uniformly, obligations
        // included: a dropped check is sound, and enforcing a claim the author disclaimed is noise.
        [group: 'P239 nullable veto', name: '@NonNull @Nullable return: the obligation is dropped', ok: true,
         src: HDR + NONNULL_TYPEUSE_ANN + NULLABLE_TYPEUSE_ANN + tc('''class C {
                        static @NonNull @Nullable String f(String x) { return x } }''')],
        // Field invariant: @NonNull alone raises the implicit `name != null` invariant — established
        // at the constructor exit by the Phase 237 requireNonNull survival fact, then assumed in m().
        [group: 'P239 nullable veto', name: '@NonNull field: invariant established and consumed', ok: true,
         src: HDR + NONNULL_TYPEUSE_ANN + tc('''class C {
                        @NonNull String name
                        C(String n) { Objects.requireNonNull(n); name = n }
                        int m() { name.length() } }''')],
        // The invariant's teeth (the control for the veto below): storing an UNCHECKED param must
        // refute the implicit invariant at the constructor exit — witness `new C(null)`.
        [group: 'P239 nullable veto', name: '@NonNull field: an unchecked store refutes the invariant', ok: false, expect: 'Cannot prove class invariant',
         src: HDR + NONNULL_TYPEUSE_ANN + tc('''class C {
                        @NonNull String name
                        C(String n) { name = n } }''')],
        // The both-annotations field loses the invariant entirely — the same unchecked store now
        // compiles clean: nothing to establish (and, dually, nothing assumable in readers).
        [group: 'P239 nullable veto', name: '@NonNull @Nullable field: the invariant is vetoed', ok: true,
         src: HDR + NONNULL_TYPEUSE_ANN + NULLABLE_TYPEUSE_ANN + tc('''class C {
                        @NonNull @Nullable String name
                        C(String n) { name = n } }''')],
    ]
}
