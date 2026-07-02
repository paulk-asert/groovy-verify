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

/** 'Native isSorted' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G203_native_issorted {

    static final List<Map> CASES = [

        // ---------- Native sortedness idiom — `a.isSorted()` / `a.sorted` (Groovy 6 GDK, native int[]/long[]) ----------
        // `a.isSorted()` is the native, ascending-with-ties GDK predicate (the primitive int[]/long[]
        // overloads are native in the GDK). It lowers to the SAME flat multi-pattern axiom as
        // `Sorted.ascending(a)`, so the gap fact discharges identically — preferred where a native spelling
        // exists. No `import verification.Sorted` needed.
        [group: 'Native isSorted', name: 'int[] a.isSorted() gives gap fact', ok: true,
         src: tc('''class C {
                       @Requires({ a.isSorted() && 0 <= i && i < j && j < a.length })
                       @Ensures({ a[i] <= a[j] })
                       static int gap(int[] a, int i, int j) { 0 }
                   }''')],
        // The boolean-getter property form `a.sorted` is the same predicate (Groovy maps `a.sorted` to the
        // `isSorted()` getter), recognised in the property-access path.
        [group: 'Native isSorted', name: 'int[] a.sorted (property form) gives gap fact', ok: true,
         src: tc('''class C {
                       @Requires({ a.sorted && 0 <= i && i < j && j < a.length })
                       @Ensures({ a[i] <= a[j] })
                       static int gap(int[] a, int i, int j) { 0 }
                   }''')],
        // List receiver, native method + property forms (stock GDK isSorted, no extension needed). The
        // element reads `xs[i]`/`xs[j]` need no cast — generics are restored in the closure (GROOVY-12071).
        [group: 'Native isSorted', name: 'List xs.isSorted() gives gap fact', ok: true,
         src: tc('''class C {
                       @Requires({ xs.isSorted() && 0 <= i && i < j && j < xs.size() })
                       @Ensures({ xs[i] <= xs[j] })
                       static int gap(List<Integer> xs, int i, int j) { 0 }
                   }''')],
        [group: 'Native isSorted', name: 'List xs.sorted (property form) gives gap fact', ok: true,
         src: tc('''class C {
                       @Requires({ xs.sorted && 0 <= i && i < j && j < xs.size() })
                       @Ensures({ xs[i] <= xs[j] })
                       static int gap(List<Integer> xs, int i, int j) { 0 }
                   }''')],
        // Without sortedness the same claim refutes — the native predicate is doing real work.
        [group: 'Native isSorted', name: 'no isSorted => gap fact refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ 0 <= i && i < j && j < a.length })
                       @Ensures({ a[i] <= a[j] })
                       static int gap(int[] a, int i, int j) { 0 }
                   }''')],
    ]
}
