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

/** 'P234 typeuse nonnull' — 7 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G300_p234_typeuse_nonnull {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'TYPE_USE @NonNull (the JSpecify spelling) is now read: `List<@NonNull String>` suppresses the per-element NPE obligation and a TYPE_USE @NonNull return raises the Phase 131 obligation, both via ClassNode.getTypeAnnotations().'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — annotation-as-contract: the claim is an assumption about the caller, with no groovy-contracts runtime arm'

    static final List<Map> CASES = [

        // ===== Phase 234 — the annotation-plumbing gap was an ACCESSOR bug, not a Groovy limitation. A
        // TYPE_USE-targeted annotation never lands in ClassNode.getAnnotations(); Groovy keeps it in the
        // separate getTypeAnnotations() list. The matchers read only the former, which is why the Phase 37
        // suppression path was dead — the data was there all along (source-declared, since at least 5.0.8),
        // and GROOVY-12206 (6.0.0-beta-1) extends it to types read off COMPILED classes, so a
        // JSpecify-annotated Java dependency matches too.
        [group: 'P234 typeuse nonnull', name: 'List<@NonNull String>: the per-element obligation is suppressed', ok: true,
         src: HDR + NONNULL_TYPEUSE_ANN + tc('''class C {
                        @Requires({ xs.size() > 0 })
                        static int f(List<@NonNull String> xs) { xs[0].length() } }''')],
        // The unannotated twin is the teeth: without the declaration the element may be null and the
        // Phase 37 per-element oracle refutes with its witness.
        [group: 'P234 typeuse nonnull', name: 'teeth: the unannotated List<String> twin still refutes', ok: false, expect: 'Possible NullPointerException',
         src: HDR + NONNULL_TYPEUSE_ANN + tc('''class C {
                        @Requires({ xs.size() > 0 })
                        static int f(List<String> xs) { xs[0].length() } }''')],

        // ----- The two ARRAY spellings mean different things, and Groovy source places them differently
        // from javac. Neither is a *component* annotation in Groovy source, so neither suppresses the
        // per-element obligation here — the contract form stays the working source-level interface for
        // arrays. (Against a javac-compiled signature the JLS places `@NonNull String[]` on the component,
        // and the same matcher then fires.)
        [group: 'P234 typeuse nonnull', name: 'teeth: `String @NonNull []` is array-nullity, not element-nullity', ok: false, expect: 'Possible NullPointerException',
         src: HDR + NONNULL_TYPEUSE_ANN + tc('''class C {
                        @Requires({ xs != null && xs.length > 0 })
                        static int f(String @NonNull [] xs) { xs[0].length() } }''')],
        [group: 'P234 typeuse nonnull', name: 'teeth: Groovy-source `@NonNull String[]` binds the parameter, not the element', ok: false, expect: 'Possible NullPointerException',
         src: HDR + NONNULL_TYPEUSE_ANN + tc('''class C {
                        @Requires({ xs != null && xs.length > 0 })
                        static int f(@NonNull String[] xs) { xs[0].length() } }''')],
        // The contract form remains available and discharges the same obligation, whatever the spelling.
        [group: 'P234 typeuse nonnull', name: 'the @Requires form discharges the element obligation for arrays', ok: true,
         src: HDR + NONNULL_TYPEUSE_ANN + tc('''class C {
                        @Requires({ xs != null && xs.length > 0 && xs[0] != null })
                        static int f(@NonNull String[] xs) { xs[0].length() } }''')],

        // ----- The Phase 131 @NonNull RETURN obligation, written TYPE_USE. Here reading the type
        // annotations makes the checker STRICTER: the obligation is now raised where it was silently
        // skipped, so a nullable-param return refutes and a concat proves.
        [group: 'P234 typeuse nonnull', name: 'TYPE_USE @NonNull return: refutes on a nullable param', ok: false, expect: 'Cannot prove postcondition',
         src: HDR + NONNULL_TYPEUSE_ANN + tc('''class C {
                        static @NonNull String f(String x) { return x } }''')],
        [group: 'P234 typeuse nonnull', name: 'TYPE_USE @NonNull return: proven from a concatenation', ok: true,
         src: HDR + NONNULL_TYPEUSE_ANN + tc('''class C {
                        static @NonNull String f(String x, String y) { return x + y } }''')],
    ]
}
