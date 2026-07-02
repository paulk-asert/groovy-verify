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

/** 'P32 containsValue/equals' — 7 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G070_p32_containsvalue_equals {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Map.containsValue for enum-keyed maps (key-pinned value), and map equality.'

    static final List<Map> CASES = [

        // ---------- Phase 32a: m.containsValue(v) over enum-keyed maps ----------
        // A value the map has under some enum key is "containsValue"-true. Lowered to a finite
        // disjunction over the enum's key constants.
        [group: 'P32 containsValue/equals', name: 'containsValue: key-pinned value verifies', ok: true,
         src: tc('''class C {
                        enum State { IDLE, RUNNING, DONE }
                        @Requires({ m[State.RUNNING] == 42 })
                        @Ensures({ m.containsValue(42) })
                        static int f(Map<State,Integer> m) { 0 }
                    }''')],
        // Soundness: without a key fixed to the value, containsValue cannot be proved.
        [group: 'P32 containsValue/equals', name: 'containsValue: no key fixes the value, refuted',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum State { IDLE, RUNNING, DONE }
                        @Ensures({ m.containsValue(42) })
                        static int f(Map<State,Integer> m) { 0 }
                    }''')],
        // Works for String-valued maps too (any value sort).
        [group: 'P32 containsValue/equals', name: 'containsValue: String-valued map', ok: true,
         src: tc('''class C {
                        enum State { IDLE, RUNNING, DONE }
                        @Requires({ m[State.DONE] == "ok" })
                        @Ensures({ m.containsValue("ok") })
                        static int f(Map<State,String> m) { 0 }
                    }''')],
        // Int-keyed maps skip honestly (no finite key domain to enumerate).
        [group: 'P32 containsValue/equals', name: 'containsValue: Int-keyed map skipped',
         expect: 'outside fragment',
         src: tc('''class C {
                        @Requires({ m[5] == 42 })
                        @Ensures({ m.containsValue(42) })
                        static int f(Map<Integer,Integer> m) { 0 }
                    }''')],

        // ---------- Phase 32b: s.equals(t) for sets via containsAll composition ----------
        // Set equality via mutual subset — both directions composed from the Phase-30/31 subset
        // lowering. Verifies when mutual subset assumptions are made.
        [group: 'P32 containsValue/equals', name: 'set equals: mutual subset entails equals', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ a.containsAll(b) && b.containsAll(a) })
                        @Ensures({ a.equals(b) })
                        static int f(Set<Role> a, Set<Role> b) { 0 }
                    }''')],
        // Soundness: without mutual subset, equals refutes.
        [group: 'P32 containsValue/equals', name: 'set equals: one-way subset insufficient',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ a.containsAll(b) })
                        @Ensures({ a.equals(b) })
                        static int f(Set<Role> a, Set<Role> b) { 0 }
                    }''')],
        // Reflexivity — s.equals(s) is trivially true (forward and backward subset both reflexive).
        [group: 'P32 containsValue/equals', name: 'set equals: reflexivity', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Ensures({ s.equals(s) })
                        static int f(Set<Role> s) { 0 }
                    }''')],
    ]
}
