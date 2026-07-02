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

/** 'P43 field bounds' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G164_p43_field_bounds {

    static final List<Map> CASES = [

        // ---------- Phase 43: field-receiver bounds synthesis for runtime-throwing list shapes ----------
        // Soundness anchor: an unguarded removeLast on an instance FIELD refutes the same way
        // it does on a parameter. Pre-Phase-43 the synth only fired on parameter receivers, so
        // a field's pop-on-empty silently passed the implicit pass.
        [group: 'P43 field bounds', name: 'field removeLast without size guard refutes',
         expect: 'IndexOutOfBoundsException',
         src: tc('''class C {
                        List<Integer> xs
                        void popOne() { xs.removeLast() }
                    }''')],
        // Verify with size guard — the synthesised IndexSite discharges via the @Requires.
        [group: 'P43 field bounds', name: 'field removeLast with size guard verifies', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() > 0 })
                        @Modifies({ this.xs })
                        void popOne() { xs.removeLast() }
                    }''')],
        // Field xs.first() / xs.head() / xs.get(i) shapes also synthesise IndexSites — same
        // bounds check fires for the field as for a parameter.
        [group: 'P43 field bounds', name: 'field xs.first() without size guard refutes',
         expect: 'IndexOutOfBoundsException',
         src: tc('''class C {
                        List<Integer> xs
                        int headEl() { xs.first() }
                    }''')],
        [group: 'P43 field bounds', name: 'field xs.get(i) without bounds guard refutes',
         expect: 'IndexOutOfBoundsException',
         src: tc('''class C {
                        List<Integer> xs
                        int at(int i) { xs.get(i) }
                    }''')],
        // Soundness preserved: pop a known non-empty field, then read xs[0] — the IndexSite
        // fires at the read but discharges via the (post-pop) size oracle from Phase 42's replay.
        [group: 'P43 field bounds', name: 'field pop preserves implicit check downstream', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() > 1 })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == old.xs.size() - 1 })
                        int popThenRead() { xs.removeLast(); xs[0] }
                    }''')],
        // Regression anchor: existing field-mutation calls that don't synthesise IndexSites
        // (xs.add, s.add, m.put) still verify without an explicit nullity guard.
        [group: 'P43 field bounds', name: 'field xs.add(v) unchanged (regression anchor)', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == old.xs.size() + 1 })
                        void push(int v) { xs.add(v) }
                    }''')],
    ]
}
