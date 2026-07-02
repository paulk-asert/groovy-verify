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

/** 'P-carrier' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G222_p_carrier {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A single-value @Monadic wrapper carrier round-trips (new Res(m.v) == m); distinct carriers are not forced equal.'

    static final List<Map> CASES = [

        // Phase B (carrier model) — a single-field @Monadic wrapper carrier is modelled as a one-constructor
        // datatype; the unit/content round-trips hold by datatype theory (`unit(content(m))==m`, `content(unit(x))==x`).
        [group: 'P-carrier', name: 'wrapper round-trip: new Res(m.v) == m proves', ok: true,
         src: tc('''@groovy.transform.Monadic(bind = 'chain', map = 'transform')
                    class Res {
                        final Object v
                        Res(Object v) { this.v = v }
                        @Ensures({ new Res(m.v) == m })
                        static void unitOfContent(Res m) { } }''')],
        [group: 'P-carrier', name: 'wrapper round-trip: new Res(m.v).v == m.v proves', ok: true,
         src: tc('''@groovy.transform.Monadic(bind = 'chain', map = 'transform')
                    class Res {
                        final Object v
                        Res(Object v) { this.v = v }
                        @Ensures({ new Res(m.v).v == m.v })
                        static void contentOfUnit(Res m) { } }''')],
        [group: 'P-carrier', name: 'CONTROL distinct carriers not forced equal refutes', expect: 'Cannot prove postcondition',
         src: tc('''@groovy.transform.Monadic(bind = 'chain', map = 'transform')
                    class Res {
                        final Object v
                        Res(Object v) { this.v = v }
                        @Ensures({ m == n })
                        static void bogus(Res m, Res n) { } }''')],
    ]
}
