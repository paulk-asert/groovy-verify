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

/**
 * 'P443 String element witness' — a String list or array is an Int->String array in the solver, and the model walk
 * read back only Int->Int ones: a refutation over an element passed `f([null])` or `f(new String[1])`, a call whose
 * element satisfies the clause (`null != 'q'`). The elements the model fixed are read back now: the call passes them,
 * and an array's show in the counterexample as an int array's do.
 */
class G485_p443_string_element_witness {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 443: a String list or array's elements the model fixed are passed in the failing call (`f([\"q\"])`, `f([\"q\"] as String[])`) and an array's shown in the counterexample (`xs[0] = \"q\"`), where the call passed `[null]` or `new String[1]`."

    static final List<Map> CASES = [

        // It read `fails on: f([null])`, and `null != 'q'` holds
        [group: "P443 String element witness", name: "a for-in clause over a list's element",
         expect: ["Cannot prove loop invariant holds for every element in f", 'fails on: f(["q"])'],
         src: tc('''class A {
                        static void f(List<String> xs) {
                            @Invariant({ x != 'q' })
                            for (String x : xs) { }
                        }
                    }''')],

        // It read `fails on: f(new String[1])`
        [group: "P443 String element witness", name: "… over an array's, shown as an int array's is",
         expect: ['counterexample: xs.size() = 1, xs[0] = "q"', 'fails on: f(["q"] as String[])'],
         src: tc('''class A {
                        static void f(String[] xs) {
                            @Invariant({ x != 'q' })
                            for (String x : xs) { }
                        }
                    }''')],

        [group: "P443 String element witness", name: "a postcondition over a list's element",
         expect: ["Cannot prove postcondition of f", 'fails on: f(["q"])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result != 'q' })
                        static String f(List<String> xs) { xs[0] }
                    }''')],

        [group: "P443 String element witness", name: "… and over an array's second",
         expect: ["Cannot prove postcondition of f", 'xs[1] = "q"', '"q"] as String[])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.length == 2 })
                        @Ensures({ result != "q" })
                        static String f(String[] xs) { xs[1] }
                    }''')],

        // The @Requires fixes the first element, the postcondition the second: each in its place
        [group: "P443 String element witness", name: "each element in its place",
         expect: 'fails on: f(["a", "q"])',
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == 'a' })
                        @Ensures({ result != 'q' })
                        static String f(List<String> xs) { xs[1] }
                    }''')],
    ]
}
