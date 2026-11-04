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
 * 'P528 contract partial ops' — Phase 527's rule for a contract's {@code max()} widened to its other partial operations:
 * an array's subscript (out of bounds it throws {@code ArrayIndexOutOfBoundsException}, measured for {@code int[]} and
 * {@code Integer[]}; a list's reads null past its end and isn't one) and a division (an integral or decimal {@code /},
 * {@code %}, {@code intdiv}, {@code remainder} by zero throws {@code ArithmeticException}, {@code mod} unless positive;
 * an IEEE-754 division gives {@code Infinity}). A contract that filters makes each operation it reached defined for the
 * body; a contract that is checked owes that definedness where the operation is reached.
 */
class G569_p528_contract_partial_ops {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 528: an array subscript and a division in a contract — a precondition's or entry invariant's makes the index in bounds and the divisor non-zero for the body; a postcondition's or exit invariant's owes it where it is reached."

    static final String G = "P528 contract partial ops"
    static final String THROWS = 'may throw rather than hold or fail'

    static final List<Map> CASES = [
        // ---- a precondition filters ----
        [group: G, name: "a precondition's a[0] makes the array non-empty for the body", ok: true,
         src: tc('class C { @Requires({ a != null && a[0] > 0 }) @Ensures({ result > 0 }) static int f(int[] a) { a.length } }')],
        [group: G, name: "a precondition's a[0] discharges the body's a[0]", ok: true,
         src: tc('class C { @Requires({ a != null && a[0] > 0 }) static int f(int[] a) { a[0] } }')],
        [group: G, name: "an Integer[]'s subscript throws too: it filters", ok: true,
         src: tc('class C { @Requires({ a != null && a[0] != null }) @Ensures({ result > 0 }) static int f(Integer[] a) { a.length } }')],
        [group: G, name: "a precondition's a[-1] makes the array non-empty (a negative index within the length is defined)", ok: true,
         src: tc('class C { @Requires({ a != null && a[-1] > 0 }) @Ensures({ result > 0 }) static int f(int[] a) { a.length } }')],
        [group: G, name: "a precondition's a[i] with i >= 0 bounds the body's a[i]", ok: true,
         src: tc('class C { @Requires({ a != null && i >= 0 && a[i] > 0 }) static int f(int[] a, int i) { a[i] } }')],
        [group: G, name: "a precondition's a[i] allows a negative i: i >= 0 isn't known", expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ a != null && a[i] > 0 }) @Ensures({ result >= 0 }) static int f(int[] a, int i) { i } }')],
        [group: G, name: "a slice in a postcondition isn't a scalar subscript: no obligation", ok: true,
         src: tc('class C { @Requires({ a != null && a.length >= 2 }) @Ensures({ a[0..<2].sum() == a[0] + a[1] }) static int f(int[] a) { 1 } }')],
        [group: G, name: "a precondition's a[0] behind an || doesn't filter: the body's a[0] is refused", expect: 'IndexOutOfBoundsException',
         src: tc('class C { @Requires({ a != null && (a.length == 0 || a[0] > 0) }) static int f(int[] a) { a[0] } }')],
        [group: G, name: "a list's subscript reads null past its end: no filter", expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ xs != null && xs[0] == null }) @Ensures({ result > 0 }) static int f(List<Integer> xs) { xs.size() } }')],
        [group: G, name: "a precondition's intdiv makes the divisor non-zero for the body", ok: true,
         src: tc('class C { @Requires({ 10.intdiv(n) > 1 }) static int f(int n) { 1.intdiv(n) } }')],
        [group: G, name: "a precondition's % makes the divisor non-zero for a postcondition", ok: true,
         src: tc('class C { @Requires({ x % n == 0 }) @Ensures({ result != 0 }) static int f(int x, int n) { n } }')],
        [group: G, name: "an invariant's a[0] makes the field non-empty at entry", ok: true,
         src: tc('''@Invariant({ a != null && a[0] >= 0 })
                    class C { int[] a = [1] as int[]; @Ensures({ result > 0 }) int g() { a.length } }''')],
        // ---- a postcondition is checked ----
        [group: G, name: "a postcondition's a[0] on a maybe-empty array: the contract throws",
         expect: [THROWS, 'a[0]', '0 <= 0 && 0 < a.length', 'fails on: f(new int[0])'],
         src: tc('class C { @Requires({ a != null }) @Ensures({ a[0] == a[0] }) static int f(int[] a) { 1 } }')],
        [group: G, name: "a postcondition's a[i] guarded by its own short-circuit", ok: true,
         src: tc('class C { @Requires({ a != null }) @Ensures({ i < 0 || i >= a.length || result == a[i] }) static int f(int[] a, int i) { i >= 0 && i < a.length ? a[i] : 0 } }')],
        [group: G, name: "a postcondition's a[0] under a ternary's condition", ok: true,
         src: tc('class C { @Requires({ a != null }) @Ensures({ result == (a.length > 0 ? a[0] : -1) }) static int f(int[] a) { a.length > 0 ? a[0] : -1 } }')],
        [group: G, name: "a negative index within the length is refused, as in the body (counting from the end isn't modelled)",
         expect: [THROWS, 'counts from the end'],
         src: tc('class C { @Requires({ a != null && a.length > 0 }) @Ensures({ a[-1] == a[-1] }) static int f(int[] a) { 1 } }')],
        [group: G, name: "a postcondition's intdiv by a maybe-zero divisor: the contract throws", expect: [THROWS, 'n != 0', 'fails on: f('],
         src: tc('class C { @Ensures({ x.intdiv(n) == x.intdiv(n) }) static int f(int x, int n) { 1 } }')],
        [group: G, name: "a postcondition's % by a maybe-zero divisor: the contract throws", expect: [THROWS, 'n != 0'],
         src: tc('class C { @Ensures({ x % n == x % n }) static int f(int x, int n) { 1 } }')],
        [group: G, name: "a postcondition's % guarded by n != 0", ok: true,
         src: tc('class C { @Ensures({ n == 0 || x % n == x % n }) static int f(int x, int n) { 1 } }')],
        [group: G, name: "a postcondition's division where the zero path throws instead of returning", ok: true,
         src: tc('class C { @Ensures({ result.intdiv(n) == 0 }) static int f(int n) { if (n == 0) throw new IllegalArgumentException(); 0 } }')],
        [group: G, name: "an IEEE-754 division owes nothing (x / 0.0d is Infinity)", ok: true,
         src: tc('class C { @Ensures({ x / d == x / d || true }) static int f(double x, double d) { 1 } }')],
        // ---- the class invariant at exit ----
        [group: G, name: "an invariant's a[0] is owed at exit: emptying the field is refused", expect: [THROWS, 'class invariant', 'a[0]'],
         src: tc('''@Invariant({ a != null && a[0] >= 0 })
                    class C { int[] a = [1] as int[]; void clear() { a = new int[0] } }''')],
        [group: G, name: "an invariant's a[0] is owed at exit: a non-empty replacement verifies", ok: true,
         src: tc('''@Invariant({ a != null && a[0] >= 0 })
                    class C { int[] a = [1] as int[]; void reset() { a = new int[2] } }''')],
    ]
}
