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
 * 'P451 a @Requires callee in a condition' — Phase 450 gave a condition's contracted call its @Ensures, but a callee with a
 * @Requires bound its formals by translated value to guard it, and a list argument has none: `if (g(xs)) xs[0]` lost the
 * guard. Its @Requires now reads the arguments spliced in (Phase 450's). And a call's own precondition is checked under
 * the short-circuit and ternary operands that guard it (`n >= 0 && clip(n) > 4`), where it was checked without them.
 */
class G492_p451_requires_call_condition {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 451: a contracted call with a @Requires in a condition carries its @Ensures (`if (g(xs)) xs[0]` under `@Requires({ ys != null })`), and a call's precondition is checked under the `&&`, `||` or ternary operand guarding it (`n >= 0 && clip(n) > 4`) — each a false alarm before."

    static final List<Map> CASES = [

        // Each was a List index may be outside [0, size)
        [group: "P451 a @Requires callee in a condition", name: "an if on a callee with a @Requires", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        static int f(List<Integer> xs) {
                            if (g(xs)) return xs[0]
                            return 0
                        }
                        @Requires({ ys != null })
                        @Ensures({ result == (ys.size() > 0) })
                        static boolean g(List<Integer> ys) { ys.size() > 0 }
                    }''')],

        [group: "P451 a @Requires callee in a condition", name: "… an @Ensures that only implies it", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        static int f(List<Integer> xs) {
                            if (g(xs)) return xs[0]
                            return 0
                        }
                        @Requires({ ys != null })
                        @Ensures({ !result || ys.size() > 0 })
                        static boolean g(List<Integer> ys) { ys.size() > 1 }
                    }''')],

        [group: "P451 a @Requires callee in a condition", name: "… a ternary on one", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        static int f(List<Integer> xs) { g(xs) ? xs[0] : 0 }
                        @Requires({ ys != null })
                        @Ensures({ result == (ys.size() > 0) })
                        static boolean g(List<Integer> ys) { ys.size() > 0 }
                    }''')],

        [group: "P451 a @Requires callee in a condition", name: "an @Ensures that doesn't promise it still warns",
         expect: "List index may be outside",
         src: tc('''class A {
                        @Requires({ xs != null })
                        static int f(List<Integer> xs) {
                            if (g(xs)) return xs[0]
                            return 0
                        }
                        @Requires({ ys != null })
                        @Ensures({ !result || ys.size() >= 0 })
                        static boolean g(List<Integer> ys) { ys.size() > 0 }
                    }''')],

        [group: "P451 a @Requires callee in a condition", name: "the callee's own precondition is still checked",
         expect: "Cannot prove precondition of g",
         src: tc('''class A {
                        static int f(List<Integer> xs) {
                            if (g(xs)) return 1
                            return 0
                        }
                        @Requires({ ys != null })
                        @Ensures({ result == (ys.size() > 0) })
                        static boolean g(List<Integer> ys) { ys.size() > 0 }
                    }''')],

        // Each was a Cannot prove precondition of clip
        [group: "P451 a @Requires callee in a condition", name: "a call's precondition holds under the && guarding it", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            if (n >= 0 && clip(n) > 4) { assert n > 4 }
                            return 0
                        }
                        @Requires({ k >= 0 })
                        @Ensures({ result <= k })
                        static int clip(int k) { k > 10 ? 10 : k }
                    }''')],

        [group: "P451 a @Requires callee in a condition", name: "… under an ||", ok: true,
         src: tc('''class A {
                        static boolean f(int n) { n < 0 || clip(n) <= n }
                        @Requires({ k >= 0 })
                        @Ensures({ result <= k })
                        static int clip(int k) { k > 10 ? 10 : k }
                    }''')],

        [group: "P451 a @Requires callee in a condition", name: "… under a ternary's test", ok: true,
         src: tc('''class A {
                        static int f(int n) { n >= 0 ? clip(n) : 0 }
                        @Requires({ k >= 0 })
                        @Ensures({ result <= k })
                        static int clip(int k) { k > 10 ? 10 : k }
                    }''')],

        [group: "P451 a @Requires callee in a condition", name: "an && too weak for it still fails",
         expect: "Cannot prove precondition of clip",
         src: tc('''class A {
                        static int f(int n) {
                            if (n > -5 && clip(n) > 4) { assert n > 4 }
                            return 0
                        }
                        @Requires({ k >= 0 })
                        @Ensures({ result <= k })
                        static int clip(int k) { k > 10 ? 10 : k }
                    }''')],

        [group: "P451 a @Requires callee in a condition", name: "… as does a ternary's other arm",
         expect: "Cannot prove precondition of clip",
         src: tc('''class A {
                        static int f(int n) { n >= 0 ? 0 : clip(n) }
                        @Requires({ k >= 0 })
                        @Ensures({ result <= k })
                        static int clip(int k) { k > 10 ? 10 : k }
                    }''')],

        // A value's truth (`s && …`) is no boolean fact: left unassumed, not a crash
        [group: "P451 a @Requires callee in a condition", name: "a value's truth guarding a call is left unassumed",
         expect: "Cannot prove precondition of nonEmpty",
         src: tc('''class A {
                        static boolean f(String s) { s && nonEmpty(s) }
                        @Requires({ t != null })
                        static boolean nonEmpty(String t) { t.size() > 0 }
                    }''')],
    ]
}
