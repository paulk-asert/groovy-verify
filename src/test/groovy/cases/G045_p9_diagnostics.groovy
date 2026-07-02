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

/** 'P9 diagnostics' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G045_p9_diagnostics {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Diagnostics echo the developer\'s spelling — .size() vs .length — rather than a normalised form.'

    static final List<Map> CASES = [

        // ---------- Phase 9: diagnostics echo the accessor the developer wrote (not the internal a.size) ----------
        // No size accessor written (just a[i]) → the universal Groovy idiom .size(), valid for arrays too.
        [group: 'P9 diagnostics', name: 'implicit access defaults to .size()', expect: 'a.size()',
         src: tc('class C { static int g(int[] a, int i) { a[i] } }')],
        // The developer wrote a.length, so the obligation and counterexample echo .length.
        [group: 'P9 diagnostics', name: 'written .length is echoed', expect: 'a.length',
         src: tc('''class C {
                       @Requires({ i < a.length })
                       static int g(int[] a, int i) { a[i] }
                   }''')],
        // A collection's size, written as xs.size(), is echoed verbatim.
        [group: 'P9 diagnostics', name: 'written .size() is echoed', expect: 'xs.size()',
         src: tc('''class C {
                       @Requires({ xs.size() > 5 })
                       @Ensures({ result < 0 })
                       static int f(List xs) { xs.size() }
                   }''')],
    ]
}
