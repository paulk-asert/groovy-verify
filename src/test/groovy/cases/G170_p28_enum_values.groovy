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

/** 'P28 enum.values' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G170_p28_enum_values {

    static final List<Map> CASES = [

        // ---------- Phase 28: enum.values().length folds to a ground int ----------
        // Body context (post-resolution ClassExpression): the method returns the count, the
        // @Ensures matches the folded literal.
        [group: 'P28 enum.values', name: 'body returns Color.values().length, verifies', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Ensures({ result == 3 })
                        static int numColors() { Color.values().length }
                    }''')],
        // Soundness: wrong expected count refutes.
        [group: 'P28 enum.values', name: 'wrong count refuted',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Ensures({ result == 4 })
                        static int numColors() { Color.values().length }
                    }''')],
        // .size() form folds the same way as .length — in both body and contract positions.
        [group: 'P28 enum.values', name: 'size() form folds in body', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Ensures({ result == 3 })
                        static int numColors() { Color.values().size() }
                    }''')],
        [group: 'P28 enum.values', name: 'size() form folds in contract', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Requires({ k < Color.values().size() })
                        @Ensures({ k <= 2 })
                        static int safe(int k) { k }
                    }''')],
        // Contract-side use (re-parsed VariableExpression receiver). Looks the enum up by name in
        // the enumDomainSizes map populated by VerifyChecker, folds to 3.
        [group: 'P28 enum.values', name: '@Requires uses folded count', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Requires({ k < Color.values().length })
                        @Ensures({ k <= 2 })
                        static int safe(int k) { k }
                    }''')],
        // Bounded iteration over the enum domain: the upper bound folds to a literal, so the
        // every-quantifier's range is concrete.
        [group: 'P28 enum.values', name: 'bounded iteration over enum domain', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Requires({ (0..<Color.values().length).every { it >= 0 } })
                        @Ensures({ result == 3 })
                        static int numColors() { Color.values().length }
                    }''')],
    ]
}
