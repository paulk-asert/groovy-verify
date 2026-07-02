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

/** 'P98 elvis' — 9 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G140_p98_elvis {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The Elvis operator n ?: 5 takes n when truthy else the default; a false claim refutes.'

    static final List<Map> CASES = [
        // Phase 98 — Elvis `a ?: b` is `groovyTruth(a) ? a : b`, NOT a plain ternary: the condition is Groovy
        // truth on the first operand. The integral case is modelled soundly (truth is `a != 0`); reference /
        // String / collection operands skip loudly (their truth also turns on non-emptiness) rather than
        // crash, as the old plain-ternary path did (an Int term cast to a Bool condition).
        [group: 'P98 elvis', name: 'int elvis: def x = n ?: 5, n>0 gives n', ok: true,
         src: tc('''class C {
                        @Requires({ n > 0 })
                        @Ensures({ result == n })
                        static int f(int n) { def x = n ?: 5; x }
                    }''')],
        [group: 'P98 elvis', name: 'int elvis: n==0 gives 5', ok: true,
         src: tc('''class C {
                        @Requires({ n == 0 })
                        @Ensures({ result == 5 })
                        static int f(int n) { n ?: 5 }
                    }''')],
        [group: 'P98 elvis', name: 'int elvis false claim refutes', ok: false, expect: 'postcondition',
         src: tc('''class C {
                        @Ensures({ result >= 5 })
                        static int f(int n) { n ?: 5 }
                    }''')],
        // Phase 98b — reference/String Groovy truth: String non-null ∧ non-empty; a plain object reference
        // non-null. The empty-string and null cases route to the default (soundness controls C/E refute the
        // unguarded `result == operand`). Collections/Maps have no single-term SMT value, so they skip loudly.
        [group: 'P98 elvis', name: 'string non-empty operand gives s', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.length() > 1 })
                        @Ensures({ result == s })
                        static String f(String s) { s ?: "d" }
                    }''')],
        [group: 'P98 elvis', name: 'string empty operand gives default', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.length() == 0 })
                        @Ensures({ result == "d" })
                        static String f(String s) { s ?: "d" }
                    }''')],
        [group: 'P98 elvis', name: 'string unguarded result==s refutes', ok: false, expect: 'postcondition',
         src: tc('''class C {
                        @Ensures({ result == s })
                        static String f(String s) { s ?: "d" }
                    }''')],
        [group: 'P98 elvis', name: 'object a?:b with a!=null gives a', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == a })
                        static Object orB(Object a, Object b) { a ?: b }
                    }''')],
        [group: 'P98 elvis', name: 'object unguarded result==a refutes', ok: false, expect: 'postcondition',
         src: tc('''class C {
                        @Ensures({ result == a })
                        static Object orB(Object a, Object b) { a ?: b }
                    }''')],
        [group: 'P98 elvis', name: 'list elvis skips cleanly (no single-term value)', ok: false, expect: 'outside fragment',
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result == xs })
                        static List orEmpty(List xs) { xs ?: [] }
                    }''')],
    ]
}
