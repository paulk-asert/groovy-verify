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

/** 'Sorted helper' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G202_sorted_helper {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The Sorted.ascending/strictlyAscending helper yields the sortedness gap fact (a[i] <=/< a[j] for i<j); no sortedness ⇒ the fact refutes.'

    static final List<Map> CASES = [

        // ---------- Sorted helper — the canonical sortedness precondition (flat 2-D, multi-pattern) ----------
        // The random-access GAP FACT: from `Sorted.ascending(a)`, an arbitrary i < j gives a[i] <= a[j] in
        // ONE deterministic instantiation (multi-pattern {a[i], a[j]}). This is the lemma binary search
        // needs from sortedness; the hand-nested `every` got it only via Z3's outer auto-pattern.
        [group: 'Sorted helper', name: 'ascending gives gap fact a[i] <= a[j] (i<j)', ok: true,
         src: tc('''class C {
                       @Requires({ Sorted.ascending(a) && 0 <= i && i < j && j < a.length })
                       @Ensures({ a[i] <= a[j] })
                       static int gap(int[] a, int i, int j) { 0 }
                   }''')],
        // Without sortedness the same claim refutes (so the helper is doing real work, not vacuous).
        [group: 'Sorted helper', name: 'no sortedness => gap fact refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ 0 <= i && i < j && j < a.length })
                       @Ensures({ a[i] <= a[j] })
                       static int gap(int[] a, int i, int j) { 0 }
                   }''')],
        // strictlyAscending gives the STRICT gap fact a[i] < a[j].
        [group: 'Sorted helper', name: 'strictlyAscending gives a[i] < a[j] (i<j)', ok: true,
         src: tc('''class C {
                       @Requires({ Sorted.strictlyAscending(a) && 0 <= i && i < j && j < a.length })
                       @Ensures({ a[i] < a[j] })
                       static int gap(int[] a, int i, int j) { 0 }
                   }''')],
        // ascending does NOT entail the STRICT fact (ties allowed) — refutes, keeping the helper honest.
        [group: 'Sorted helper', name: 'ascending does not give STRICT a[i] < a[j]', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ Sorted.ascending(a) && 0 <= i && i < j && j < a.length })
                       @Ensures({ a[i] < a[j] })
                       static int gap(int[] a, int i, int j) { 0 }
                   }''')],
        // descending mirror: a[i] >= a[j] for i < j.
        [group: 'Sorted helper', name: 'descending gives a[i] >= a[j] (i<j)', ok: true,
         src: tc('''class C {
                       @Requires({ Sorted.descending(a) && 0 <= i && i < j && j < a.length })
                       @Ensures({ a[i] >= a[j] })
                       static int gap(int[] a, int i, int j) { 0 }
                   }''')],
        // List receiver works the same way (List<Integer> element sort is Int). `xs[i]`/`xs[j]` read back
        // as `Integer` inside the contract closure (GROOVY-12071 restored the closure's generic types), so
        // the `<=` type-checks with no cast — nothing to do with the Sorted helper, which type-checks plainly.
        [group: 'Sorted helper', name: 'ascending on List<Integer> gives gap fact', ok: true,
         src: tc('''class C {
                       @Requires({ Sorted.ascending(xs) && 0 <= i && i < j && j < xs.size() })
                       @Ensures({ xs[i] <= xs[j] })
                       static int gap(List<Integer> xs, int i, int j) { 0 }
                   }''')],
    ]
}
