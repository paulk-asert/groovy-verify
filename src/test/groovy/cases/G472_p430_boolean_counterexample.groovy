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
 * 'P430 boolean counterexample' — a boolean's model value is 0 or 1, and the counterexample printed it so: `counterexample:
 * b = 0` above `fails on: f(false)`. A boolean name (a parameter, a local, a field, the result) is
 * shown as the `false`/`true` the source spells.
 */
class G472_p430_boolean_counterexample {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 430: a boolean in a counterexample shows as `false`/`true`, matching the failing call, where it showed its 0/1 model value."

    static final List<Map> CASES = [

        // It read `counterexample: b = 0`
        [group: "P430 boolean counterexample", name: "a boolean parameter shows as false",
         expect: ["Cannot prove postcondition of f", "counterexample: b = false", "fails on: f(false)"],
         refute: "b = 0",
         src: tc('''class A {
                        @Ensures({ result > 0 })
                        static int f(boolean b) { int n = 0; if (b) { n = 1 }; return n }
                    }''')],

        [group: "P430 boolean counterexample", name: "… and true, beside an int",
         expect: ["Cannot prove postcondition of f", "b = true", "fails on: f(true, 0)"],
         refute: "b = 1",
         src: tc('''class A {
                        @Requires({ p >= 0 })
                        @Ensures({ result > 0 })
                        static int f(boolean b, int p) { return b ? p : 1 }
                    }''')],

        [group: "P430 boolean counterexample", name: "the instance's own boolean field",
         expect: ["Cannot prove postcondition of f", "on = false"],
         refute: "on = 0",
         src: tc('''class A {
                        boolean on
                        @Ensures({ result > 0 })
                        int f() { return on ? 1 : 0 }
                    }''')],
    ]
}
