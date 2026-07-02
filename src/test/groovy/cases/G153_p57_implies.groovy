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

/** 'P57 implies' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G153_p57_implies {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Logical implication ==> / .implies(): modus ponens proves, an implication without its antecedent refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 57: logical implication — `==>` operator and `.implies()` method ----------
        // The `==>` operator (Groovy 5) is a BinaryExpression lowered to `implies(a, b) = !a || b`.
        // Modus ponens: from `(a>=0) ==> (b>=0)` and `a>=0`, derive `b>=0`.
        // The two premises read naturally as two @Requires (conjoined automatically since Phase 66 —
        // this once needed a single combined @Requires, before repeated annotations were captured).
        [group: 'P57 implies', name: 'modus ponens via ==> operator', ok: true,
         src: tc('''class C {
                        @Requires({ (a >= 0) ==> (b >= 0) })
                        @Requires({ a >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int a, int b) { b }
                    }''')],
        // The `.implies()` method form (DGM Boolean.implies) lowers the same way.
        [group: 'P57 implies', name: 'modus ponens via .implies() method', ok: true,
         src: tc('''class C {
                        @Requires({ (a >= 0).implies(b >= 0) && a >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int a, int b) { b }
                    }''')],
        // Soundness: the implication alone (without the antecedent) doesn't give the consequent.
        [group: 'P57 implies', name: 'implication without antecedent refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ (a >= 0) ==> (b >= 0) })
                        @Ensures({ result >= 0 })
                        static int f(int a, int b) { b }
                    }''')],
        // Simplification showcase: the array-element frame reads as an implication — every index
        // OTHER than j is unchanged — `it != j ==> a[it] == old.a[it]` (vs `it == j || …`).
        [group: 'P57 implies', name: 'array frame via ==> implication', ok: true,
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= j && j < a.length })
                       @Ensures({ (0..<a.length).every { it != j ==> a[it] == old.a[it] } })
                       void set(int j, int v) { a[j] = v }
                   }''')],
    ]
}
