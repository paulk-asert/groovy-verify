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

/** 'P-arrayelem' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G128_p_arrayelem {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'int[] element values appear in counterexamples, and an element-wise refutation names the offending slot.'

    static final List<Map> CASES = [
        // Phase 125 — an Int-valued *parameter* array's element values are rendered in the counterexample
        // (`xs[1] = 8` makes plain why `xs[1] == 7` fails). A *local* array's elements stay suppressed: in a
        // loop-preservation check the model picks an arbitrary entry array, so its element value would mislead.
        [group: 'P-arrayelem', name: 'parameter int[] element values shown in counterexample', ok: false, expect: 'xs[1] = 8',
         src: tc('''class T {
                        @Requires({ xs != null && xs.length >= 2 })
                        @Ensures({ xs[1] == 7 })
                        static void check(int[] xs) { }
                    }''')],
        // Phase 126 — an element-wise refutation surfaces the offending array slot's post-store value vs the
        // per-element spec (`a[0] = 1 — the spec requires 0`), evaluated in the model by bounded enumeration.
        [group: 'P-arrayelem', name: 'element-wise refutation names the offending int[] slot', ok: false, expect: 'a[0] = 1 — the spec requires 0',
         src: tc('''class T {
                        @Requires({ n >= 1 })
                        @Ensures({ (0..<n).every { int k -> result[k] == k } })
                        static int[] fill(int n) {
                            int[] a = new int[n]
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && a.length == n && (0..<i).every { int k -> a[k] == k } })
                            @Decreases({ n - i })
                            while (i < n) { a[i] = i + 1; i = i + 1 }
                            return a
                        }
                    }''')],
    ]
}
