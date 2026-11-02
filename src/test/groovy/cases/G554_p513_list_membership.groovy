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
 * 'P513 list membership' — {@code v in xs} for a list or an array by name: Groovy's {@code xs.isCase(v)}, which is
 * {@code xs.contains(v)}, and on a null {@code xs} whether {@code v} is null, with no exception (measured, Groovy
 * 6.0.0). It was outside the fragment (a set's, a map's, a list literal's and a range's were modelled), so a
 * contract stating it was skipped. A {@code String}'s {@code in} is a substring test, and isn't taken as a list's.
 */
class G554_p513_list_membership {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 513: `v in xs` for a list or an array is `xs.contains(v)`, and on a null `xs` whether `v` is null, as Groovy runs it; `v !in xs` its negation."

    static final List<Map> CASES = [
        [group: "P513 list membership", name: "a member, by contains", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && 5 in xs })
                        @Ensures({ result })
                        static boolean f(List<Integer> xs) { xs.contains(5) }
                    }''')],
        [group: "P513 list membership", name: "as Groovy runs it, a null list too", ok: true,
         src: tc('''class C {
                        @Ensures({ result == (v in xs) })
                        static boolean f(Integer v, List<Integer> xs) { xs == null ? v == null : xs.contains(v) }
                    }''')],
        [group: "P513 list membership", name: "a null list's, not contains", expect: ['Cannot prove postcondition', 'fails on: f(null, null)'],
         src: tc('''class C {
                        @Ensures({ result == (v in xs) })
                        static boolean f(Integer v, List<Integer> xs) { xs != null && xs.contains(v) }
                    }''')],
        [group: "P513 list membership", name: "not a member", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && 5 !in xs })
                        @Ensures({ !result })
                        static boolean f(List<Integer> xs) { xs.contains(5) }
                    }''')],
        [group: "P513 list membership", name: "no null in a list", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && !(null in xs) })
                        static int f(List<Integer> xs) { xs[1] + 1 }
                    }''')],
        [group: "P513 list membership", name: "… stated with !in", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 && null !in xs })
                        static int f(List<Integer> xs) { xs[1] + 1 }
                    }''')],
        [group: "P513 list membership", name: "an array's member", ok: true,
         src: tc('''class C {
                        @Requires({ a != null && 3 in a })
                        @Ensures({ result })
                        static boolean f(int[] a) { a.contains(3) }
                    }''')],
        [group: "P513 list membership", name: "a member after an add", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ 5 in xs })
                        static void f(List<Integer> xs) { xs.add(5) }
                    }''')],
        [group: "P513 list membership", name: "… another value added", expect: ['Cannot prove postcondition', 'fails on: f(['],
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ 5 in xs })
                        static void f(List<Integer> xs) { xs.add(4) }
                    }''')],
        [group: "P513 list membership", name: "a member, in the body", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 1 && xs[0] == 7 })
                        @Ensures({ result })
                        static boolean f(List<Integer> xs) { 7 in xs }
                    }''')],
        [group: "P513 list membership", name: "… on a null list", expect: ['Cannot prove postcondition', 'fails on: f(null)'],
         src: tc('''class C {
                        @Ensures({ !result })
                        static boolean f(List<Integer> xs) { null in xs }
                    }''')],
        [group: "P513 list membership", name: "a literal list's, as before", ok: true,
         src: tc('''class C {
                        @Ensures({ result == (v == 1 || v == 2) })
                        static boolean f(int v) { v in [1, 2] }
                    }''')],
        [group: "P513 list membership", name: "a local list's member", ok: true,
         src: tc('''class C {
                        @Ensures({ result })
                        static boolean f(int v) { List<Integer> ys = []; ys.add(v); v in ys }
                    }''')],
        [group: "P513 list membership", name: "a String list's member", ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && 'a' in xs })
                        @Ensures({ result })
                        static boolean f(List<String> xs) { xs.contains('a') }
                    }''')],
        [group: "P513 list membership", name: "in a String, outside as before", expect: ['outside fragment'],
         src: tc('''class C {
                        @Ensures({ result })
                        static boolean f(String s) { 'ab' in s }
                    }''')],
    ]
}
