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
 * 'P444 String element size' — a for-in's String variable and an `every` closure's parameter over a String list were
 * no Strings to the encoder (only parameters, fields and typed locals are): `x.size()` was an int of its own, not the
 * string's length. `@Requires({ xs.every { it.size() < 3 } })` said nothing of the strings, and `@Invariant({
 * x.size() < 3 })` over them refuted — a false alarm, with no call to show (Phase 443). `x.length()` was outside the
 * fragment. Both names are Strings now, so both spellings are the length.
 */
class G486_p444_string_element_size {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 444: a for-in's String variable and an `every` closure's String parameter are Strings, so `x.size()` / `x.length()` is the string's length — `@Requires({ xs.every { it.size() < 3 } })` now proves `@Invariant({ x.size() < 3 })`, where it refuted."

    static final List<Map> CASES = [

        // It refuted: `counterexample: it.size() = 0, x.size() = 3, xs.size() = 1`, `fails on: f([null])`
        [group: "P444 String element size", name: "an every over the strings proves a for-in invariant", ok: true,
         src: tc('''class A {
                        @Requires({ xs.every { it.size() < 3 } })
                        static void f(List<String> xs) {
                            @Invariant({ x.size() < 3 })
                            for (String x : xs) { }
                        }
                    }''')],

        // It was outside the fragment
        [group: "P444 String element size", name: "… spelled length()", ok: true,
         src: tc('''class A {
                        @Requires({ xs.every { it.length() < 3 } })
                        static void f(List<String> xs) {
                            @Invariant({ x.length() < 3 })
                            for (String x : xs) { }
                        }
                    }''')],

        [group: "P444 String element size", name: "an untyped for-in variable takes the list's element type", ok: true,
         src: tc('''class A {
                        @Requires({ xs.every { it.size() < 3 } })
                        static void f(List<String> xs) {
                            @Invariant({ x.size() < 3 })
                            for (x in xs) { }
                        }
                    }''')],

        // (the loop variable owes `x != null` even over List<@NonNull String>: found, not fixed — the guard stands in)
        [group: "P444 String element size", name: "an assert in the body over the strings", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.every { it.size() < 3 } })
                        static void f(List<String> xs) {
                            for (String x : xs) { if (x != null) assert x.size() < 3 }
                        }
                    }''')],

        [group: "P444 String element size", name: "an every's String parameter bounds an element read", ok: true,
         src: HDR + NONNULL_TYPEUSE_ANN + tc('''class A {
                        @Requires({ xs != null && xs.size() == 1 && xs.every { it.size() < 3 } })
                        @Ensures({ result < 3 })
                        static int f(List<@NonNull String> xs) { xs[0].size() }
                    }''')],

        // A refutation now has a string to show: one too long
        [group: "P444 String element size", name: "a refuted invariant passes a string that breaks it",
         expect: ["Cannot prove loop invariant holds for every element in f", 'fails on: f(["ABC"])'],
         src: tc('''class A {
                        static void f(List<String> xs) {
                            @Invariant({ x.size() < 3 })
                            for (String x : xs) { }
                        }
                    }''')],

        // An element the model made null is null in the call, whatever string it was also given (Phase 443 read `f([""])`)
        [group: "P444 String element size", name: "a null element is null in the call",
         expect: ["Possible NullPointerException", 'fails on: f([null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 1 })
                        static int f(List<String> xs) { xs[0] != 'ab' ? xs[0].size() : 0 }
                    }''')],
    ]
}
