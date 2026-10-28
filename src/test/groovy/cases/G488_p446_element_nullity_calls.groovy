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
 * 'P446 element nullity across calls' — a callee's formal had element-nullity flags of its own at a call site, so a
 * caller's `xs[0] != null` never discharged the callee's `@Requires({ ys[0] != null })`, and a callee's
 * `@Ensures({ ys[0] != null })` never reached the caller's `xs`. A `List<String>` formal was also no String list in the
 * caller's encoder: tying its contents to the actual's (Phase 225) crashed Z3 on the sort mismatch. The formal now
 * takes its element type, and its flags are tied to the actual's, both ways.
 */
class G488_p446_element_nullity_calls {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 446: a caller's element-nullity facts discharge a callee's `@Requires({ ys[0] != null })` and a callee's `@Ensures({ ys[0] != null })` reaches the caller's list, where each was a false alarm; a `List<String>` formal's `every` no longer crashes Z3."

    static final List<Map> CASES = [

        // Each was `Cannot prove precondition of g at this call site`
        [group: "P446 element nullity across calls", name: "a caller's non-null element discharges a callee's", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] != null })
                        static int f(List<String> xs) { g(xs) }
                        @Requires({ ys != null && ys.size() > 0 && ys[0] != null })
                        static int g(List<String> ys) { ys[0].size() }
                    }''')],

        [group: "P446 element nullity across calls", name: "… over an array", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.length > 0 && xs[0] != null })
                        static int f(String[] xs) { g(xs) }
                        @Requires({ ys != null && ys.length > 0 && ys[0] != null })
                        static int g(String[] ys) { ys[0].size() }
                    }''')],

        [group: "P446 element nullity across calls", name: "… from a store before the call", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<String> xs) { xs[0] = 'a'; g(xs) }
                        @Requires({ ys != null && ys.size() > 0 && ys[0] != null })
                        static int g(List<String> ys) { ys[0].size() }
                    }''')],

        // It crashed: `Z3Exception: Sorts (Array Int Int) and (Array Int String) are incompatible`
        [group: "P446 element nullity across calls", name: "an every discharges an every", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.every { it != null } })
                        static int f(List<String> xs) { g(xs) }
                        @Requires({ ys != null && ys.every { it != null } })
                        static int g(List<String> ys) { 0 }
                    }''')],

        // It was `Possible NullPointerException`
        [group: "P446 element nullity across calls", name: "a callee's @Ensures makes the caller's element non-null", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<String> xs) { fill(xs); xs[0].size() }
                        @Requires({ ys != null && ys.size() > 0 })
                        @Ensures({ ys[0] != null })
                        static void fill(List<String> ys) { ys[0] = 'a' }
                    }''')],

        // The teeth
        [group: "P446 element nullity across calls", name: "a caller without the fact doesn't discharge it",
         expect: "Cannot prove precondition of g at this call site",
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<String> xs) { g(xs) }
                        @Requires({ ys != null && ys.size() > 0 && ys[0] != null })
                        static int g(List<String> ys) { ys[0].size() }
                    }''')],

        [group: "P446 element nullity across calls", name: "… nor after a store that may be null",
         expect: "Cannot prove precondition of g at this call site",
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] != null })
                        static int f(List<String> xs, String z) { xs[0] = z; g(xs) }
                        @Requires({ ys != null && ys.size() > 0 && ys[0] != null })
                        static int g(List<String> ys) { ys[0].size() }
                    }''')],

        [group: "P446 element nullity across calls", name: "a callee that writes null leaves the element unknown",
         expect: "Possible NullPointerException",
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] != null })
                        static int f(List<String> xs) { clobber(xs); xs[0].size() }
                        @Requires({ ys != null && ys.size() > 0 })
                        static void clobber(List<String> ys) { ys[0] = null }
                    }''')],

        // The callee's formal `ys` is the caller's `xs` only for its @Ensures: the caller's own `ys` keeps its flags
        [group: "P446 element nullity across calls", name: "a formal named like a caller's list doesn't touch it",
         expect: "Possible NullPointerException",
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && ys != null && ys.size() > 0 })
                        static int f(List<String> xs, List<String> ys) { fill(xs); ys[0].size() }
                        @Requires({ ys != null && ys.size() > 0 })
                        @Ensures({ ys[0] != null })
                        static void fill(List<String> ys) { ys[0] = 'a' }
                    }''')],
    ]
}
