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

/** 'P-counter' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G030_p_counter {

    static final List<Map> CASES = [
        // PROBE-counter (Step 1 — a second R/G example, a different shape: one shared scalar with a *monotonicity*
        // rely, not array pointers). Two symmetric threads only ever increment `count`; each relies on the other to
        // do the same (oldCount <= count). So a value I've observed below the count stays below it despite
        // concurrent increments — `count >= k` is preserved by the environment.
        [group: 'P-counter', name: 'monotonic counter: observed bound persists', ok: true,
         src: tc('''@Invariant({ count >= 0 })
                    class Counter {
                       int count
                       @Rely('Other')   static boolean rOther(int oldCount, int count) { oldCount <= count }   // others only increment
                       @Guarantee('Me') static boolean gMe(int oldCount, int count)    { oldCount <= count }   // I only increment
                       @Requires({ k <= count })
                       @UnderRely('Other')
                       void atLeast(int k) {
                           assert count >= k                        // ← STILL holds across concurrent increments
                       }
                   }''')],
        // The rely is load-bearing: a weak rely that lets count *decrease* no longer keeps the observed bound.
        [group: 'P-counter', name: 'weak (non-monotonic) rely drops the bound', expect: 'Assertion may not hold',
         src: tc('''@Invariant({ count >= 0 })
                    class Counter {
                       int count
                       @Rely('Other')   static boolean rOther(int oldCount, int count) { count >= 0 }
                       @Guarantee('Me') static boolean gMe(int oldCount, int count)    { count >= 0 }
                       @Requires({ k <= count })
                       @UnderRely('Other')
                       void atLeast(int k) {
                           assert count >= k
                       }
                   }''')],
        // Loop form: the loop invariant `k <= count` is rely-stable (count only grows), so it survives the
        // environment running each iteration — the rely-step is framed per iteration inside the loop body.
        [group: 'P-counter', name: 'monotonic counter loop verifies', ok: true,
         src: tc('''@Invariant({ count >= 0 })
                    class Counter {
                       int count
                       @Rely('Other')   static boolean rOther(int oldCount, int count) { oldCount <= count }
                       @Guarantee('Me') static boolean gMe(int oldCount, int count)    { oldCount <= count }
                       @Requires({ 0 <= k && k <= count })
                       @UnderRely('Other')
                       int observe(int k) {
                           int seen = 0
                           int i = 0
                           @Invariant({ 0 <= i && i <= k && k <= count })
                           @Decreases({ k - i })
                           while (i < k) {
                               int c = count        // read the shared count → rely-step framed per iteration
                               seen = seen + 1
                               i = i + 1
                           }
                           return seen
                       }
                   }''')],
        // Loop soundness: a non-monotonic rely makes `k <= count` not rely-stable, so the per-iteration rely-step's
        // havoc breaks it and preservation fails — exactly as the buffer's non-rely-stable loop test.
        [group: 'P-counter', name: 'non-monotonic rely breaks the loop invariant', expect: 'invariant',
         src: tc('''@Invariant({ count >= 0 })
                    class Counter {
                       int count
                       @Rely('Other')   static boolean rOther(int oldCount, int count) { count >= 0 }
                       @Guarantee('Me') static boolean gMe(int oldCount, int count)    { count >= 0 }
                       @Requires({ 0 <= k && k <= count })
                       @UnderRely('Other')
                       int observe(int k) {
                           int seen = 0
                           int i = 0
                           @Invariant({ 0 <= i && i <= k && k <= count })
                           @Decreases({ k - i })
                           while (i < k) {
                               int c = count
                               seen = seen + 1
                               i = i + 1
                           }
                           return seen
                       }
                   }''')],
    ]
}
