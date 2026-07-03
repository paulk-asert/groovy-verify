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

/** 'P194 alias demote' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G271_p194_alias_demote {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The no-aliasing boundary demotes to loud skips where it was load-bearing: a store through one array parameter with a same-element-type sibling read on the path, and a mutating call through one of two same-class receivers, both previously VERIFIED under the separate-objects model — unsound for aliased actuals f(x, x), which the runtime rung can never generate. Sound shapes survive: reads of the stored array itself, and two-array methods that never store.'

    static final List<Map> CASES = [

        // ---------- Phase 194: demote-to-skip where the no-aliasing assumption was load-bearing ----------
        // Previously VERIFIED: under f(x, x) the store through `a` changes b[0] to 5, the method returns 5,
        // and the "proved" postcondition is false at runtime. Now a loud skip naming both parameters.
        [group: 'P194 alias demote', name: 'store through one array, read through the other: skips', expect: 'may alias',
         src: tc('''class C {
             @Requires({ b.length > 0 && a.length > 0 && b[0] == 7 })
             @Ensures({ result == 7 })
             static int f(int[] a, int[] b) {
                 a[0] = 5
                 return b[0]
             }
         }''')],
        // Previously VERIFIED: the per-name havoc of b's fields misses c when b.is(c) — under f(x, x)
        // the incr() bumps c.count too and the method returns 4, not 3. Now a loud skip.
        [group: 'P194 alias demote', name: 'mutating call with a same-class sibling receiver: skips', expect: 'may alias',
         src: tc('''@Invariant({ count >= 0 })
         class Counter {
             int count
             @Ensures({ count == old.count + 1 })
             void incr() { count = count + 1 }
         }
         @TypeChecked(extensions = 'verification.VerifyChecker')
         class C {
             @Requires({ b != null && c != null && c.count == 3 })
             @Ensures({ result == 3 })
             static int f(Counter b, Counter c) {
                 b.incr()
                 return c.count
             }
         }''')],
        // Survival teeth: reading the STORED array itself is exact under aliasing (same name, same
        // store) — the sibling `b` is never read, so nothing demotes.
        [group: 'P194 alias demote', name: 'reading the stored array itself still verifies', ok: true,
         src: tc('''class C {
             @Requires({ a.length > 0 })
             @Ensures({ result == 5 })
             static int f(int[] a, int[] b) {
                 a[0] = 5
                 return a[0]
             }
         }''')],
        // Survival teeth: two same-type arrays WITHOUT a store — pure reads are alias-consistent
        // (an aliased actual simply satisfies both preconditions or neither), so no demotion.
        [group: 'P194 alias demote', name: 'two arrays without a store still verify', ok: true,
         src: tc('''class C {
             @Requires({ a.length > 0 && b.length > 0 && a[0] == 1 && b[0] == 2 })
             @Ensures({ result == 3 })
             static int f(int[] a, int[] b) {
                 return a[0] + b[0]
             }
         }''')],
    ]
}
