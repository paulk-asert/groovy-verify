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
 * 'P424 boxed nullity' — a written name's nullity was bound on the postcondition path for reference types only (Phase
 * 132), and a boxed integer counted as an int: `Integer n = p; return n != null` read a free `n?null`, so it refuted
 * even under `@Requires({ p != null })`, and showed `fails on: f(-2147483648)` where the run that fails is `f(null)`.
 * The value-flow and loop paths already bound it for every type.
 *
 * A boxed integer's nullity flows through its writes now, and a failing call renders a null boxed parameter (an
 * Integer's or a Boolean's) as `null`, its value left off the counterexample.
 */
class G466_p424_boxed_local_nullity {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 424: a boxed integer local (`Integer n = p`) carries its value's nullity on the postcondition path, so `n != null` proves under `p != null` and refutes on `f(null)`, and a null boxed parameter renders as `null` in the failing call."

    static final List<Map> CASES = [

        // It refuted with `fails on: f(-2147483648)`: n's null flag was free
        [group: "P424 boxed nullity", name: "a boxed local is null when its value is",
         expect: ["Cannot prove postcondition of f", "ensured: result", "fails on: f(null)"],
         refute: "2147483648",
         src: tc('''class A {
                        @Ensures({ result })
                        static boolean f(Integer p) { Integer n = p; return n != null }
                    }''')],

        // A false positive before: the precondition didn't reach n
        [group: "P424 boxed nullity", name: "… and non-null when its value is",
         ok: true,
         src: tc('''class A {
                        @Requires({ p != null })
                        @Ensures({ result })
                        static boolean f(Integer p) { Integer n = p; return n != null }
                        @Requires({ p != null })
                        @Ensures({ result })
                        static boolean g(Long p) { Long n = p; return n != null }
                        @Ensures({ result })
                        static boolean h() { Integer n = 5; return n != null }
                    }''')],

        [group: "P424 boxed nullity", name: "a boxed local set to null is null",
         ok: true,
         src: tc('''class A {
                        @Ensures({ result })
                        static boolean f(Integer p) { Integer n = 3; n = null; return n == null }
                    }''')],

        [group: "P424 boxed nullity", name: "a reassignment forgets the old non-null",
         expect: ["Cannot prove postcondition of f", "fails on: f(null)"],
         src: tc('''class A {
                        @Ensures({ result })
                        static boolean f(Integer p) { Integer n = 3; n = p; return n != null }
                    }''')],

        [group: "P424 boxed nullity", name: "each branch's value",
         ok: true,
         src: tc('''class A {
                        @Ensures({ result == (p == null && !b) })
                        static boolean f(Integer p, boolean b) {
                            Integer n = 0
                            if (b) { n = 1 } else { n = p }
                            return n == null
                        }
                    }''')],

        [group: "P424 boxed nullity", name: "a null Long renders as null",
         expect: ["Cannot prove postcondition of f", "fails on: f(null)"],
         src: tc('''class A {
                        @Ensures({ result })
                        static boolean f(Long p) { Long n = p; return n != null }
                    }''')],

        [group: "P424 boxed nullity", name: "a null Boolean renders as null",
         expect: ["Cannot prove postcondition of f", "fails on: f(null)"],
         src: tc('''class A {
                        @Ensures({ result })
                        static boolean f(Boolean p) { Boolean n = p; return n != null }
                    }''')],
    ]
}
