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

/** 'P114 records' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G231_p114_records {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A record\'s components read like final fields in contracts, and a record may carry its own contracts; a wrong component refutes.'

    static final List<Map> CASES = [
        // ---------- P114 records (no engine change — a record is a class with component fields) ----------
        // A Groovy `record` is modelled by the existing Phase-45 object-field machinery: its components are
        // final fields, so component reads in contracts and bodies resolve, and a record may carry its own
        // @Requires/@Ensures. No record-specific support was added — it falls out of the class handling.
        [group: 'P114 records', name: 'record param: component read', ok: true,
         src: tc('''class C {
                        @Requires({ p != null && p.x >= 0 })
                        @Ensures({ result == p.x })
                        static int f(Point p) { return p.x }
                    }
                    record Point(int x, int y) { }''')],
        // Refute control: the body returns p.x, so claiming result == p.y must refute.
        [group: 'P114 records', name: 'record param: wrong component refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ p != null && p.x >= 0 })
                        @Ensures({ result == p.y })
                        static int f(Point p) { return p.x }
                    }
                    record Point(int x, int y) { }''')],
        // A record with its own contract method reading its components.
        [group: 'P114 records', name: 'record with its own contract', ok: true,
         src: tc('''record Box(int lo, int hi) {
                        @Requires({ lo <= hi })
                        @Ensures({ result >= 0 })
                        int width() { return hi - lo }
                    }''')],
        // Refute control: width is 0 when lo == hi, so a strict result > 0 must refute.
        [group: 'P114 records', name: 'record strict claim refuted', expect: 'Cannot prove postcondition',
         src: tc('''record Box(int lo, int hi) {
                        @Requires({ lo <= hi })
                        @Ensures({ result > 0 })
                        int width() { return hi - lo }
                    }''')],
    ]
}
