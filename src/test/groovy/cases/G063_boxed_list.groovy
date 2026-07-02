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

/** 'boxed & list' — 10 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G063_boxed_list {

    static final List<Map> CASES = [

        // ---------- Boxed types & lists (structural: the encoder is untyped) ----------
        // The encoder treats every integer type as a mathematical Int and matches arrays/lists by
        // syntactic shape (`a[i]`, `.length`/`.size()`), so `Integer`, `Integer[]`, and index-accessed
        // `List<Integer>` verify exactly like `int` / `int[]`. (Element nullability is the known gap.)
        [group: 'boxed & list', name: 'Integer scalar postcondition', ok: true,
         src: tc('''class C {
                       @Ensures({ result >= a && result >= b })
                       static Integer max(Integer a, Integer b) { a >= b ? a : b }
                   }''')],
        [group: 'boxed & list', name: 'Integer scalar postcondition refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Ensures({ result >= a && result >= b })
                       static Integer max(Integer a, Integer b) { a >= b ? b : a }
                   }''')],
        [group: 'boxed & list', name: 'Integer[] sorted-diff verified', ok: true,
         src: tc('''class C {
                       @Requires({ (0..<a.length - 1).every { a[it] <= a[it + 1] } && 0 <= k && k + 1 < a.length })
                       @Ensures({ result <= 0 })
                       static int diff(Integer[] a, int k) { a[k] - a[k + 1] }
                   }''')],
        [group: 'boxed & list', name: 'Integer[] bounds bug refuted', expect: 'IndexOutOfBoundsException',
         src: tc('class C { static int g(Integer[] a, int i) { a[i] } }')],
        [group: 'boxed & list', name: 'List<Integer> index read (range.every)', ok: true,
         src: tc('''class C {
                       @Requires({ (0..<xs.size()).every { xs[it] >= 0 } && 0 <= k && k < xs.size() })
                       @Ensures({ result >= 0 })
                       static int get(List<Integer> xs, int k) { xs[k] }
                   }''')],
        [group: 'boxed & list', name: 'List<Integer> index read (element-wise every)', ok: true,
         src: tc('''class C {
                       @Requires({ xs.every { it >= 0 } && 0 <= k && k < xs.size() })
                       @Ensures({ result >= 0 })
                       static int get(List<Integer> xs, int k) { xs[k] }
                   }''')],
        [group: 'boxed & list', name: 'List<Integer> subscript store frame', ok: true,
         src: tc('''class C {
                       @Requires({ 0 <= j && j < xs.size() })
                       @Ensures({ xs[j] == v })
                       static void set(List<Integer> xs, int j, int v) { xs[j] = v }
                   }''')],
        [group: 'boxed & list', name: 'List<Integer> sorted-diff verified', ok: true,
         src: tc('''class C {
                       @Requires({ (0..<xs.size() - 1).every { xs[it] <= xs[it + 1] } && 0 <= k && k + 1 < xs.size() })
                       @Ensures({ result <= 0 })
                       static int diff(List<Integer> xs, int k) { xs[k] - xs[k + 1] }
                   }''')],
        // List<String>: value reasoning over elements is out of fragment, but the index-bounds safety
        // check is element-type-agnostic — guarded verifies, unguarded refutes.
        [group: 'boxed & list', name: 'List<String> guarded index verified', ok: true,
         src: tc('''class C {
                       @Requires({ 0 <= k && k < xs.size() })
                       static String get(List<String> xs, int k) { xs[k] }
                   }''')],
        [group: 'boxed & list', name: 'List<String> unguarded index refuted', expect: 'IndexOutOfBoundsException',
         src: tc('class C { static String g(List<String> xs, int i) { xs[i] } }')],
    ]
}
