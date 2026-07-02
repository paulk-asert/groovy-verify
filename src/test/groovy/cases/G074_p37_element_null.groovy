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

/** 'P37 element null' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G074_p37_element_null {

    static final List<Map> CASES = [

        // ---------- Phase 37: element nullability ----------
        // Refute: xs[0].method() without a per-element non-null guarantee. The bounds @Requires lets
        // the index check pass; the nullity obligation still fires because xs[0] is unconstrained.
        [group: 'P37 element null', name: 'unguarded xs[i].method() refutes',
         expect: 'Possible NullPointerException: Cannot invoke method length()',
         src: tc('''class C {
                        @Requires({ xs.size() > 0 })
                        static int f(List<String> xs) { xs[0].length() }
                    }''')],
        // Verify: @Requires({ xs[i] != null }) constrains the per-element nullity oracle, which
        // discharges the implicit obligation at the .length() deref.
        [group: 'P37 element null', name: 'guarded by @Requires xs[i] != null verifies', ok: true,
         src: tc('''class C {
                        @Requires({ xs.size() > 0 && xs[0] != null })
                        static int f(List<String> xs) { xs[0].length() }
                    }''')],
        // Verify: in-body if-guard discharges via the path-fact mechanism — same oracle.
        [group: 'P37 element null', name: 'in-body if (xs[i] != null) guard verifies', ok: true,
         src: tc('''class C {
                        @Requires({ xs.size() > 0 })
                        static int f(List<String> xs) {
                            if (xs[0] != null) return xs[0].length()
                            return 0
                        }
                    }''')],
        // Refute soundness: a guard on xs[0] doesn't license a deref on xs[1].
        [group: 'P37 element null', name: 'guard on wrong index refutes',
         expect: 'Possible NullPointerException: Cannot invoke method length()',
         src: tc('''class C {
                        @Requires({ xs.size() > 1 && xs[0] != null })
                        static int f(List<String> xs) { xs[1].length() }
                    }''')],
        // xs.get(i) shape: same lowering through translateBinary's null path; same DerefSite.
        [group: 'P37 element null', name: 'xs.get(i).method() shape: refute',
         expect: 'Possible NullPointerException: Cannot invoke method length()',
         src: tc('''class C {
                        @Requires({ xs.size() > 0 })
                        static int f(List<String> xs) { xs.get(0).length() }
                    }''')],
        // The scalar deref on xs itself fires (xs.get(0) is a method call), so xs != null also needed.
        [group: 'P37 element null', name: 'xs.get(i).method() shape: verify with @Requires xs.get(i) != null', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 && xs.get(0) != null })
                        static int f(List<String> xs) { xs.get(0).length() }
                    }''')],
    ]
}
