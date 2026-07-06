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

/** 'P220 instance specs' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G292_p220_instance_specs {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Instance-method spec consumption (Phase 220): the registry now answers for INSTANCE calls — the receiver\'s STC-inferred type threads into the same resolution chain (instanceReceiverType alongside the carrier/static-owner cases). v1 soundness scope: consumed instance contracts must be RECEIVER-INDEPENDENT — they may reference only result and the formals (receiver-state names like length() would translate as unrelated caller variables), enforced by a uniform guard on all spec callees. The debut skeletons are java.time value getters: LocalDate (getMonthValue 1..12, getDayOfMonth 1..31, getDayOfYear 1..366) and LocalTime (getHour 0..23, getMinute/getSecond 0..59) — immutable, @Pure, pure range facts. The existing nullity discipline composes for free: an unguarded d.getMonthValue() first demands the d != null obligation, THEN the range fact flows. Showpiece: minuteOfDay(t) = t.getHour() * 60 + t.getMinute() proves 0 <= result < 1440 from two instance facts. Receiver-STATE contracts (String.charAt bounds via length()) and contract-position instance admission are the recorded next steps.'

    static final List<Map> CASES = [

        // ---------- Phase 220: instance-method spec consumption (java.time debut) ----------
        [group: 'P220 instance specs', name: 'LocalDate.getMonthValue: instance range fact (return position)', ok: true,
         src: tc('''class C {
                        @Requires({ d != null })
                        @Ensures({ 1 <= result && result <= 12 })
                        static int m(java.time.LocalDate d) {
                            return d.getMonthValue()
                        }
                    }''')],
        [group: 'P220 instance specs', name: 'zero-based month arithmetic through the assign path', ok: true,
         src: tc('''class C {
                        @Requires({ d != null })
                        @Ensures({ 0 <= result && result < 12 })
                        static int zeroBased(java.time.LocalDate d) {
                            int m = d.getMonthValue()
                            return m - 1
                        }
                    }''')],
        [group: 'P220 instance specs', name: 'minute-of-day: two instance facts compose arithmetically', ok: true,
         src: tc('''class C {
                        @Requires({ t != null })
                        @Ensures({ 0 <= result && result < 1440 })
                        static int minuteOfDay(java.time.LocalTime t) {
                            int h = t.getHour()
                            int m = t.getMinute()
                            return h * 60 + m
                        }
                    }''')],
        [group: 'P220 instance specs', name: 'over-claim refutes through the range fact (January)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ d != null })
                        @Ensures({ result >= 2 })
                        static int m(java.time.LocalDate d) {
                            return d.getMonthValue()
                        }
                    }''')],
    ]
}
