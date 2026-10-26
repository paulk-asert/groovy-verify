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
 * 'P426 safe call index' — `a[xs?.size()]` on a null `xs` was reported twice on the one call: its null (Phase 422,
 * right) and an index out of bounds (Phase 422's sentinel, below every number), though Groovy throws before anything is
 * indexed — measured on Groovy 6, a null index, its arithmetic (either operand) and its `int` cast all throw.
 *
 * An index whose value is a safe call's has its bounds checked where the receiver isn't null.
 */
class G468_p426_safe_call_index {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 426: `a[xs?.size()]` reports only the null on a null `xs` (Groovy throws before indexing), its bounds checked where `xs` isn't null, so a precondition on that case proves them."

    static final List<Map> CASES = [

        // It failed on f(new int[0], null) as an index, too
        [group: "P426 safe call index", name: "a safe call's index is bounded where it isn't null",
         expect: ["Possible IndexOutOfBoundsException", "obligation: 0 <= xs?.size() && xs?.size() < a.size()",
                  "fails on: f(new int[0], [])", "xs?.size() is null when xs is", "fails on: f(new int[0], null)"],
         src: tc('''class A {
                        static int f(int[] a, List xs) { a[xs?.size()] }
                    }''')],

        [group: "P426 safe call index", name: "… through its arithmetic",
         expect: ["Possible IndexOutOfBoundsException", "fails on: f(new int[0], [])"],
         src: tc('''class A {
                        static int f(int[] a, List xs) { a[1 + xs?.size()] }
                    }''')],

        // The bounds prove; only the null is left
        [group: "P426 safe call index", name: "a precondition on the non-null case proves the bounds",
         expect: ["xs?.size() is null when xs is", "fails on: f(new int[0], null)"],
         refute: "IndexOutOfBoundsException",
         src: tc('''class A {
                        @Requires({ a != null && (xs == null || xs.size() < a.length) })
                        static int f(int[] a, List xs) { a[xs?.size()] }
                    }''')],

        [group: "P426 safe call index", name: "… and with the null ruled out, nothing is left",
         ok: true,
         src: tc('''class A {
                        @Requires({ a != null && xs != null && xs.size() < a.length })
                        static int f(int[] a, List xs) { a[xs?.size()] }
                    }''')],
    ]
}
