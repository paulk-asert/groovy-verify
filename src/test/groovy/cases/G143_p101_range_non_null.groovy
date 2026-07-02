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

/** 'P101 range non-null' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G143_p101_range_non_null {

    static final List<Map> CASES = [
        // Phase 101 — a top-level `v in lo..hi` precondition implies `v != null` (a range never contains null),
        // so an unguarded deref in the body discharges its null check. The `||` control confirms soundness.
        [group: 'P101 range non-null', name: 'range membership implies non-null (deref ok, no guard)', ok: true,
         src: tc('''class C {
                        @Requires({ s in 'A'..'Z' })
                        @Ensures({ result >= 0 })
                        static int len(String s) { s.length() }
                    }''')],
        [group: 'P101 range non-null', name: 'range under || does NOT imply non-null (still flags NPE)', ok: false, expect: 'NullPointer',
         src: tc('''class C {
                        @Requires({ s in 'A'..'Z' || s == null })
                        @Ensures({ result >= 0 })
                        static int len(String s) { s.length() }
                    }''')],
    ]
}
