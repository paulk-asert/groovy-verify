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

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The Java-friendly String-contract prototype: this project\'s own verification.@Requires/@Ensures/@Decreases(\'…\') take the condition as a String (a legal Java annotation value, unlike a closure) and capture it into the SAME reparse→encode→prove pipeline as a groovy-contracts closure. A recursive method verifies inductively (method-level @Decreases assumes the @Ensures at the recursive call) and a wrong @Ensures refutes on the base case; a straight-line method verifies; and a String @Requires discharges an implicit obligation (division-by-zero). Loop invariants stay out of reach — Java forbids statement annotations.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — String-form contracts: verify-only, no groovy-contracts runtime arm to cross-validate'

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
