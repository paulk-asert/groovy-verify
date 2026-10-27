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
 * 'P445 element nullity' — an element's nullity is a per-element flag (`xs$nullElem`, Phase 37) that a
 * `@Requires({ xs[0] != null })` constrains and an `xs[i].m()` obligation reads. It followed nothing else: an element
 * store left it as the precondition fixed it (`xs[0] = null; xs[0].size()` proved — unsound), while a for-in's `x`,
 * a `String y = xs[0]`, an `every`'s `it` and a String compared to a literal each had a nullity of their own (false
 * alarms). The flag now follows stores, appends, aliases and havocs, and those names read it.
 */
class G487_p445_element_nullity {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 445: an element's nullity follows its stores (`xs[0] = null` after `@Requires({ xs[0] != null })` is refuted, where it proved) and reaches a for-in variable, an element local, `xs.every { it != null }`, `List<@NonNull String>` and `xs[0] == 'ab'`, where each was a false NPE alarm."

    static final List<Map> CASES = [

        // Unsound before: the first two compiled cleanly
        [group: "P445 element nullity", name: "a null stored over a non-null element is null",
         expect: "Possible NullPointerException",
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] != null })
                        static int f(List<String> xs) { xs[0] = null; xs[0].size() }
                    }''')],

        // A value that translates (unlike `null`, whose store havocs the contents) stores its own nullity
        [group: "P445 element nullity", name: "… and a parameter that may be null",
         expect: "Possible NullPointerException",
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] != null })
                        static int f(List<String> xs, String z) { xs[0] = z; xs[0].size() }
                    }''')],

        [group: "P445 element nullity", name: "… and through set",
         expect: "Possible NullPointerException",
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] != null })
                        static int f(List<String> xs) { xs.set(0, null); xs[0].size() }
                    }''')],

        // (a loop havocs what it writes, so this one was already refuted: kept as the store's loop twin)
        [group: "P445 element nullity", name: "… and in a loop",
         expect: "Possible NullPointerException",
         src: tc('''class A {
                        @Requires({ xs != null && xs.length > 0 && xs.every { it != null } })
                        static int f(String[] xs) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= xs.length })
                            while (i < xs.length) { xs[i] = null; i++ }
                            xs[0].size()
                        }
                    }''')],

        [group: "P445 element nullity", name: "a value read before the store keeps its own", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] != null })
                        static int f(List<String> xs) { String y = xs[0]; xs[0] = null; y.size() }
                    }''')],

        [group: "P445 element nullity", name: "an appended literal isn't null", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        static int f(List<String> xs) { xs.add('a'); xs[xs.size() - 1].size() }
                    }''')],

        // False alarms before: each was a Possible NullPointerException
        [group: "P445 element nullity", name: "every { it != null } makes an element non-null", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs.every { it != null } })
                        static int f(List<String> xs) { xs[0].size() }
                    }''')],

        [group: "P445 element nullity", name: "… and a for-in's variable", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.every { it != null } })
                        static void f(List<String> xs) { for (String x : xs) { assert x.size() >= 0 } }
                    }''')],

        [group: "P445 element nullity", name: "List<@NonNull String> makes a for-in's variable non-null", ok: true,
         src: HDR + NONNULL_TYPEUSE_ANN + tc('''class A {
                        @Requires({ xs != null })
                        static void f(List<@NonNull String> xs) { for (String x : xs) { assert x.size() >= 0 } }
                    }''')],

        [group: "P445 element nullity", name: "a local read from a non-null element", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] != null })
                        static int f(List<String> xs) { String y = xs[0]; y.size() }
                    }''')],

        [group: "P445 element nullity", name: "an element equal to a literal isn't null", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] == 'ab' })
                        static int f(List<String> xs) { xs[0].size() }
                    }''')],

        [group: "P445 element nullity", name: "… nor a parameter", ok: true,
         src: tc('''class A {
                        @Requires({ s == 'ab' })
                        static int f(String s) { s.size() }
                    }''')],

        // `null != 'ab'` is true: unequal to a literal says nothing of null
        [group: "P445 element nullity", name: "a parameter unequal to a literal may be null",
         expect: "Possible NullPointerException",
         src: tc('''class A {
                        @Requires({ s != 'ab' })
                        static int f(String s) { s.size() }
                    }''')],
        // Phase 444 found it: the call put null where the precondition fixes 'ab' (`f([null, null])`)
        [group: "P445 element nullity", name: "a failing call keeps the element a literal fixed",
         expect: ['Possible NullPointerException', 'fails on: f(["ab", null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == 'ab' })
                        static int f(List<String> xs) { xs[1].size() }
                    }''')],
    ]
}
