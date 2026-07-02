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

/** 'P44c width overflow' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G135_p44c_width_overflow {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Width-aware overflow: long n+1 verifies under a 64-bit bound (no spurious 32-bit refute) but refutes at the 64-bit boundary.'

    static final List<Map> CASES = [
        // Phase 44c — width-aware @CheckOverflow: the bound follows the operation's promoted width.
        [group: 'P44c width overflow', name: 'long n+1 verifies under a 64-bit bound (was a spurious 32-bit refute)', ok: true,
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ n < Long.MAX_VALUE })
                        static long f(long n) { n + 1 }
                    }''')],
        [group: 'P44c width overflow', name: 'long n+1 refutes at the 64-bit boundary', ok: false, expect: '64-bit',
         src: tc('''class C {
                        @CheckOverflow
                        static long f(long n) { n + 1 }
                    }''')],
        [group: 'P44c width overflow', name: 'int n+1 still refutes at 32-bit (unchanged)', ok: false, expect: '32-bit',
         src: tc('''class C {
                        @CheckOverflow
                        static int f(int n) { n + 1 }
                    }''')],
        [group: 'P44c width overflow', name: 'long a*b refutes at the 64-bit boundary', ok: false, expect: '64-bit',
         src: tc('''class C {
                        @CheckOverflow
                        static long f(long a, long b) { a * b }
                    }''')],
    ]
}
