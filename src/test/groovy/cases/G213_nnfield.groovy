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

/** 'NNFIELD' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G213_nnfield {

    static final List<Map> CASES = [

        [group: 'NNFIELD', name: 'N0 explicit class invariant name!=null establishes via ctor', ok: true,
         src: tc('''@groovy.contracts.Invariant({ name != null })
                    class C {
                        String name
                        @Requires({ n != null })
                        C(String n) { name = n } }''')],
        [group: 'NNFIELD', name: 'N0b ctor without guard may leave field null refutes', expect: 'Cannot prove class invariant',
         src: tc('''@groovy.contracts.Invariant({ name != null })
                    class C {
                        String name
                        C(String n) { name = n } }''')],
        [group: 'NNFIELD', name: 'N0c method nulls field refutes preservation', expect: 'class invariant',
         src: tc('''@groovy.contracts.Invariant({ name != null })
                    class C {
                        String name
                        @Requires({ n != null })
                        C(String n) { name = n }
                        void clear() { name = null } }''')],
        // @NonNull field → implicit `field != null` invariant (no spelled-out @Invariant needed).
        [group: 'NNFIELD', name: 'N1 @NonNull field established by guarded ctor', ok: true,
         src: HDR + NONNULL_ANN + tc('''class C {
                        @NonNull String name
                        @Requires({ n != null })
                        C(String n) { name = n } }''')],
        [group: 'NNFIELD', name: 'N2 @NonNull field unguarded ctor refutes', expect: 'class invariant',
         src: HDR + NONNULL_ANN + tc('''class C {
                        @NonNull String name
                        C(String n) { name = n } }''')],
        [group: 'NNFIELD', name: 'N3 @NonNull field nulled by method refutes', expect: 'class invariant',
         src: HDR + NONNULL_ANN + tc('''class C {
                        @NonNull String name
                        @Requires({ n != null })
                        C(String n) { name = n }
                        void clear() { name = null } }''')],
    ]
}
