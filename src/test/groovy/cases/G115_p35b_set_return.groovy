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

/** 'P35b set return' — 7 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G115_p35b_set_return {

    static final List<Map> CASES = [

        // ===== set-return probes (Phase 35b: result bound to a set binop) =====
        [group: 'P35b set return', name: 'common via a & b return', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && b != null })
                        @Ensures({ (3 in result) == (3 in a && 3 in b) })
                        static Set<Integer> common(Set<Integer> a, Set<Integer> b) { a & b }
                    }''')],
        [group: 'P35b set return', name: 'union via a | b return', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && b != null })
                        @Ensures({ (3 in result) == (3 in a || 3 in b) })
                        static Set<Integer> merge(Set<Integer> a, Set<Integer> b) { a | b }
                    }''')],
        [group: 'P35b set return', name: 'union via a.or(b) return', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && b != null })
                        @Ensures({ (3 in result) == (3 in a || 3 in b) })
                        static Set<Integer> merge(Set<Integer> a, Set<Integer> b) { a.or(b) }
                    }''')],
        [group: 'P35b set return', name: 'intersect via a.and(b) return', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && b != null })
                        @Ensures({ (3 in result) == (3 in a && 3 in b) })
                        static Set<Integer> common(Set<Integer> a, Set<Integer> b) { a.and(b) }
                    }''')],
        [group: 'P35b set return', name: 'common via materialised local return', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && b != null })
                        @Ensures({ (3 in result) == (3 in a && 3 in b) })
                        static Set<Integer> common(Set<Integer> a, Set<Integer> b) {
                            Set<Integer> r = a & b
                            r
                        }
                    }''')],
        // SOUNDNESS: a wrong relation (returns the UNION but claims the INTERSECTION) must refute.
        [group: 'P35b set return', name: 'wrong set-return relation refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ a != null && b != null })
                        @Ensures({ (3 in result) == (3 in a && 3 in b) })
                        static Set<Integer> merge(Set<Integer> a, Set<Integer> b) { a | b }
                    }''')],

        // README set-return example (verbatim): result IS the union, characterised at an arbitrary element p.
        [group: 'P35b set return', name: 'README union: result == granted | extra', ok: true,
         src: tc('''class C {
                        @Requires({ granted != null && extra != null })
                        @Ensures({ (p in result) == (p in granted || p in extra) })   // result == granted ∪ extra
                        static Set<Integer> merge(Set<Integer> granted, Set<Integer> extra, int p) { granted | extra }
                    }''')],
    ]
}
