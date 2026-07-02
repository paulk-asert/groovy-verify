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

/** 'P97 safe-nav non-null' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G139_p97_safe_nav_non_null {

    static final List<Map> CASES = [
        // Phase 97 — a top-level `recv?.foo()` precondition conjunct implies `recv != null` (a null receiver
        // makes safe-navigation falsy), so the body's unguarded `recv.bar()` discharges its null-deref check
        // with no explicit `recv != null`. The `||` control confirms soundness: under a disjunction the
        // safe-nav carries no non-null implication, so the NPE obligation is still (correctly) flagged.
        [group: 'P97 safe-nav non-null', name: 'titleLen via safe-nav ?. precondition proves', ok: true,
         src: tc('''class C {
                        @Requires({ name?.startsWith("Dr. ") })   // ?. ⟹ name != null
                        @Ensures({ result >= 4 })
                        static int titleLen(String name) { name.length() }   // ✓ no NPE obligation left open
                    }''')],
        [group: 'P97 safe-nav non-null', name: 'safe-nav under || does NOT imply non-null (still flags)', ok: false, expect: 'NullPointer',
         src: tc('''class C {
                        @Requires({ name?.startsWith("Dr. ") || name == null })
                        @Ensures({ result >= 4 })
                        static int titleLen(String name) { name.length() }
                    }''')],
    ]
}
