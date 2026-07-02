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

/** 'P-philosophers' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G113_p_philosophers {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Dining philosophers, the thread-local half of the deadlock-freedom story (the structural half is the Fray rung). Deadlock-free by *resource hierarchy*: if every philosopher acquires its two forks in increasing global index order, the wait-for graph is acyclic so no deadlock. groovy-verify proves that LOCAL ordering discipline as pure int arithmetic (min-first over the circle verifies for every philosopher; the discipline holds for any two distinct forks) and REFUTES the naive left-then-right scheme — the counterexample i=n-1 pinpointing the wrap-around philosopher whose acquisition closes the cycle.'

    static final List<Map> CASES = [
        [group: 'P-philosophers', name: 'naive left-then-right deadlocks: order violated at the wrap-around philosopher', expect: 'postcondition',
         src: tc("class C { @Requires({ n >= 2 && i >= 0 && i < n }) @Ensures({ result }) static boolean naive(int i, int n) { i < (i + 1) % n } }")],
        [group: 'P-philosophers', name: 'resource hierarchy (lower fork first) is deadlock-free', ok: true,
         src: tc('''class C {
             @Requires({ n >= 2 && i >= 0 && i < n })
             @Ensures({ result })
             static boolean hierarchy(int i, int n) {
                 int left = i
                 int right = (i + 1) % n
                 int first = left < right ? left : right
                 int second = left < right ? right : left
                 return first < second
             }
         }''')],
        [group: 'P-philosophers', name: 'the ordering discipline holds for any two distinct forks', ok: true,
         src: tc('''class C {
             @Requires({ a != b })
             @Ensures({ result })
             static boolean lowFirst(int a, int b) {
                 int first = a < b ? a : b
                 int second = a < b ? b : a
                 return first < second
             }
         }''')],
    ]
}
