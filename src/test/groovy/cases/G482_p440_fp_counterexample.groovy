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
 * 'P440 floating-point counterexample' — an FP refutation showed no values: Z3's FP variables weren't read back from the
 * model, so `d2(double p)` refuted with neither `counterexample:` nor `fails on:`. A double or float parameter or local
 * now shows its model value as the Groovy literal that builds it — `1.5d`, `-1.6777216E7f`, `-0.0d`, `Double.NaN`,
 * `Double.POSITIVE_INFINITY` — read exactly (through `fp.to_real`, a dyadic rational) and built into the failing call.
 */
class G482_p440_fp_counterexample {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 440: a double or float in a counterexample shows its exact model value as the Groovy literal that builds it (`p = 1.5d`, `Double.NaN`, `-0.0d`), and the failing call passes it (`d3(1.5d)`), where an FP refutation showed no values and no call."

    static final List<Map> CASES = [

        // It showed `ensured: (result > 0.0)` and nothing more
        [group: "P440 floating-point counterexample", name: "a double parameter's value and call",
         expect: ["Cannot prove postcondition of d3", "counterexample: p = 1.5d", "fails on: d3(1.5d)"],
         src: tc('''class A {
                        @Requires({ p > 1.0d })
                        @Ensures({ result > 2.0d })
                        static double d3(double p) { return p * 2.0d - 1.0d }
                    }''')],

        [group: "P440 floating-point counterexample", name: "a float beside an int",
         expect: ["Cannot prove postcondition of f1", "k = 0, p = -", "fails on: f1(-", "f, 0)"],
         src: tc('''class A {
                        @Ensures({ result > 0.0f })
                        static float f1(float p, int k) { return p + 1.0f }
                    }''')],

        // The value through a local: zero is a literal too
        [group: "P440 floating-point counterexample", name: "a zero through a local",
         expect: ["Cannot prove postcondition of d2", "counterexample: p = ", "fails on: d2("],
         refute: "(solver gave no values)",
         src: tc('''class A {
                        @Ensures({ result > 0.0d })
                        static double d2(double p) { double d = p; return d }
                    }''')],
    ]
}
