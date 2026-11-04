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
 * 'P527 contract extremum' — a primitive array's {@code max()}/{@code min()} throws on an empty array (measured, Groovy 6:
 * {@code UnsupportedOperationException}; a list's or {@code Integer[]}'s answers null). In a body the call carried a
 * non-empty obligation (Phase 60); in a contract it was unchecked. Now a contract that filters ({@code @Requires}, the
 * class invariant at entry) makes the array non-empty for the body, as Phase 414 makes a dereferenced reference
 * non-null — the call threw before the body ran — and a contract that is checked ({@code @Ensures}, the invariant at
 * exit) owes {@code 0 < a.length} where the call is reached, under the guards before it.
 */
class G568_p527_contract_extremum {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 527: a primitive array's max()/min() in a contract — a precondition's or entry invariant's makes the array non-empty for the body (the call throws before it runs); a postcondition's or exit invariant's owes 0 < a.length where it is reached."

    static final String G = "P527 contract extremum"
    static final String THROWS = 'may throw rather than hold or fail'

    static final List<Map> CASES = [
        // ---- a precondition filters: the body sees only arrays the call didn't throw on ----
        [group: G, name: "a precondition's max() makes the array non-empty: the body's max() verifies", ok: true,
         src: tc('class C { @Requires({ a != null && a.max() > 0 }) @Ensures({ result == a.max() }) static int f(int[] a) { a.max() } }')],
        [group: G, name: "a precondition's min() bounds the body's a[0]", ok: true,
         src: tc('class C { @Requires({ a != null && a.min() >= 0 }) @Ensures({ result >= 0 }) static int f(int[] a) { a[0] } }')],
        [group: G, name: "a precondition's max() under a negation still filters", ok: true,
         src: tc('class C { @Requires({ a != null && !(a.max() < 0) }) @Ensures({ result > 0 }) static int f(int[] a) { a.length } }')],
        [group: G, name: "a negated || evaluates both its sides: !(b || a.max() < 0) filters", ok: true,
         src: tc('class C { @Requires({ a != null && !(b || a.max() < 0) }) @Ensures({ result > 0 }) static int f(int[] a, boolean b) { a.length } }')],
        [group: G, name: "a double[]'s max() in a precondition filters too", ok: true,
         src: tc('class C { @Requires({ a != null && a.max() > 0.0d }) @Ensures({ result > 0 }) static int f(double[] a) { a.length } }')],
        [group: G, name: "a precondition's max() behind an || doesn't filter: the body's max() is refused", expect: 'IndexOutOfBoundsException',
         src: tc('class C { @Requires({ a != null && (a.length == 0 || a.max() > 0) }) static int f(int[] a) { a.max() } }')],
        [group: G, name: "a precondition's max() behind a flag's || doesn't filter: a.length > 0 isn't known", expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ a != null && (b || a.max() > 0) }) @Ensures({ result > 0 }) static int f(int[] a, boolean b) { a.length } }')],
        [group: G, name: "an Integer[]'s max() answers null on an empty array: a postcondition's owes nothing", ok: true,
         src: tc('class C { @Requires({ a != null }) @Ensures({ a.max() == a.max() }) static int f(Integer[] a) { a.length } }')],
        // ---- a postcondition is checked: the call must be reached on a non-empty array ----
        [group: G, name: "a postcondition's max() on a maybe-empty array is the contract throwing, not the claim failing",
         expect: [THROWS, 'a.max()', '0 < a.length', 'fails on: f(new int[0])'],
         src: tc('class C { @Requires({ a != null }) @Ensures({ result <= a.max() }) static int f(int[] a) { a.length == 0 ? 0 : a[0] } }')],
        [group: G, name: "a postcondition's min() guarded by its own || short-circuit", ok: true,
         src: tc('class C { @Requires({ a != null }) @Ensures({ a.length == 0 || result >= a.min() }) static int f(int[] a) { a.length == 0 ? 0 : a[0] } }')],
        [group: G, name: "a postcondition's max() under the precondition's non-emptiness", ok: true,
         src: tc('class C { @Requires({ a != null && a.length > 0 }) @Ensures({ result <= a.max() }) static int f(int[] a) { a[0] } }')],
        [group: G, name: "a postcondition's max() where the empty array's path throws instead of returning", ok: true,
         src: tc('class C { @Requires({ a != null }) @Ensures({ result <= a.max() }) static int f(int[] a) { if (a.length == 0) throw new IllegalArgumentException("empty"); a[0] } }')],
        [group: G, name: "a postcondition's max() under a ternary's condition", ok: true,
         src: tc('class C { @Requires({ a != null }) @Ensures({ result == (a.length > 0 ? a.max() : -1) }) static int f(int[] a) { a.length > 0 ? a.max() : -1 } }')],
        [group: G, name: "a postcondition's max() guarded by && on the wrong side is reached: refused",
         expect: [THROWS, 'fails on: f(new int[0])'],
         src: tc('class C { @Requires({ a != null }) @Ensures({ result <= a.max() && a.length >= 0 }) static int f(int[] a) { a.length == 0 ? 0 : a[0] } }')],
        [group: G, name: "a tautology over an empty array's max() no longer proves", expect: THROWS,
         src: tc('class C { @Requires({ a != null }) @Ensures({ a.max() == a.max() }) static int f(int[] a) { a.length } }')],
        // ---- the class invariant: assumed at entry, owed at exit ----
        [group: G, name: "an invariant's min() makes the field non-empty at entry", ok: true,
         src: tc('''@Invariant({ a != null && a.min() >= 0 })
                    class C { int[] a = [1] as int[]; @Ensures({ result > 0 }) int g() { a.length } }''')],
        [group: G, name: "an invariant's min() is owed at exit: emptying the field is refused", expect: [THROWS, 'class invariant', 'a.min()'],
         src: tc('''@Invariant({ a != null && a.min() >= 0 })
                    class C { int[] a = [1] as int[]; void clear() { a = new int[0] } }''')],
        [group: G, name: "an invariant's min() is owed at exit: a non-empty replacement verifies", ok: true,
         src: tc('''@Invariant({ a != null && a.min() >= 0 })
                    class C { int[] a = [1] as int[]; void reset() { a = new int[2] } }''')],
        // ---- a list's extremum answers null: Phase 492's model, not this slice's ----
        [group: G, name: "a list's max() in a precondition isn't a filter but a value: the body's max() verifies through its non-null", ok: true,
         src: tc('class C { @Requires({ xs != null && xs.max() > 0 }) @Ensures({ result > 0 }) static int f(List<Integer> xs) { xs.max() } }')],
    ]
}
