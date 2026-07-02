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

/** 'P13 frame' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G044_p13_frame {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A @Modifies frame is checked: an honest frame verifies, an undeclared write refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 13 (frame-check): a method writes only what its @Modifies declares ----------
        // Honest: inc declares it modifies count and writes only count → frame-check passes.
        [group: 'P13 frame', name: 'honest modifies verified', ok: true,
         src: tc('''class C {
                       int count, other
                       @Modifies({ this.count })
                       void inc() { count = count + 1 }
                   }''')],
        // Array modifies: a setter declares it modifies a, and writes only a.
        [group: 'P13 frame', name: 'array modifies verified', ok: true,
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= j && j < a.length })
                       @Modifies({ this.a })
                       void set(int j, int v) { a[j] = v }
                   }''')],
        // Violation: writes an undeclared field → loud frame error.
        [group: 'P13 frame', name: 'undeclared write refuted', expect: 'not in its @Modifies',
         src: tc('''class C {
                       int count, other
                       @Modifies({ this.count })
                       void bad() { count = count + 1; other = 7 }
                   }''')],
        // @Modifies({ [] }) means pure: any field write violates it.
        [group: 'P13 frame', name: 'pure method that writes refuted', expect: 'not in its @Modifies',
         src: tc('''class C {
                       int count
                       @Modifies({ [] })
                       void touch() { count = 1 }
                   }''')],
        // Caller-side framing: clobber() may change a (declared, @Ensures says nothing), so the caller
        // can NO LONGER assume a[0] is unchanged across the call → refuted. (Pre-framing this passed
        // unsoundly — the call left `a` untouched.)
        [group: 'P13 frame', name: 'callee may clobber shared array', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       int[] a
                       @Requires({ a.length > 0 })
                       @Modifies({ this.a })
                       void clobber() { a[0] = 999 }
                       @Requires({ a.length > 0 && a[0] == 5 })
                       @Modifies({ this.a })
                       @Ensures({ a[0] == 5 })
                       void caller() { clobber() }
                   }''')],
    ]
}
