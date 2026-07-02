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

/** 'P-string-contract' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G114_p_string_contract {

    static final List<Map> CASES = [
        [group: 'P-string-contract', name: 'recursive count verifies from String contracts', ok: true,
         src: tcStr('''class C {
             @Requires('n >= 0')
             @Ensures('result == n')
             @Decreases('n')
             static int count(int n) {
                 if (n == 0) return 0;
                 return 1 + count(n - 1);
             }
         }''')],
        [group: 'P-string-contract', name: 'recursive count wrong String @Ensures refutes', expect: 'postcondition',
         src: tcStr('''class C {
             @Requires('n >= 0')
             @Ensures('result == n + 1')
             @Decreases('n')
             static int count(int n) {
                 if (n == 0) return 0
                 return 1 + count(n - 1)
             }
         }''')],
        [group: 'P-string-contract', name: 'straight-line square verifies from String contracts', ok: true,
         src: tcStr("class C { @Requires('x >= 0 && x < 1000') @Ensures('result == x * x') static int sq(int x) { x * x } }")],
        [group: 'P-string-contract', name: 'String @Requires discharges a division-by-zero obligation', ok: true,
         src: tcStr("class C { @Requires('y != 0') static int div(int x, int y) { x.intdiv(y) } }")],
    ]
}
