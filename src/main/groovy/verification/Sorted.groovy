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
package verification

import groovy.transform.CompileStatic

/**
 * The canonical <em>sortedness</em> precondition the verifier recognises in
 * {@code @Requires}/{@code @Ensures}/{@code @Invariant} contracts:
 *
 * <pre>
 *   {@literal @}Requires({ Sorted.ascending(a) })
 * </pre>
 *
 * <p>Sortedness is the textbook precondition (binary search, merge, dedup,
 * insertion point, median…). It <em>is</em> expressible as a hand-written nested
 * {@code every} — {@code (0..&lt;n).every { p -> (p+1..&lt;n).every { a[p] &lt;= a[it] } } } —
 * but that form pins an explicit instantiation trigger only on the inner variable,
 * leaving the outer quantifier on Z3's auto-pattern/MBQI heuristics (the
 * "trigger-cliff"). This helper is recognised by {@link Encoder} and emitted as a
 * <em>flat</em> two-variable axiom
 * {@code ∀ j,k. 0 &lt;= j &lt; k &lt; n ⇒ a[j] R a[k]} with an explicit
 * <em>multi-pattern</em> trigger {@code {a[j], a[k]}}. So the random-access "gap" fact
 * (e.g. {@code a[i] &lt;= a[mid]} for {@code i &lt; mid}) fires in a single, deterministic
 * instantiation the moment both selects are ground — exactly what Dafny's
 * {@code forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]} relies on.
 *
 * <p>Like {@link Forall} and {@link Sets} it stays <em>executable</em>, so the
 * groovy-contracts runtime check still works: each method evaluates the predicate
 * directly. It is pure sugar over a fact the contract already asserts — no new
 * assumption is introduced, so it adds no soundness surface.
 *
 * <p>{@code int[]} and {@code List} receivers are modelled; the element comparison
 * rides Z3's order over the element sort (Int and exact Real). Four orderings are
 * provided: non-strict and strict, ascending and descending.
 */
@CompileStatic
class Sorted {

    /** True iff {@code a[j] <= a[k]} for all {@code j < k} — ascending, ties allowed. */
    static boolean ascending(int[] a) {
        for (int i = 1; i < a.length; i++) if (a[i - 1] > a[i]) return false
        true
    }

    /** True iff {@code a[j] >= a[k]} for all {@code j < k} — descending, ties allowed. */
    static boolean descending(int[] a) {
        for (int i = 1; i < a.length; i++) if (a[i - 1] < a[i]) return false
        true
    }

    /** True iff {@code a[j] < a[k]} for all {@code j < k} — strictly ascending (no ties). */
    static boolean strictlyAscending(int[] a) {
        for (int i = 1; i < a.length; i++) if (a[i - 1] >= a[i]) return false
        true
    }

    /** True iff {@code a[j] > a[k]} for all {@code j < k} — strictly descending (no ties). */
    static boolean strictlyDescending(int[] a) {
        for (int i = 1; i < a.length; i++) if (a[i - 1] <= a[i]) return false
        true
    }

    // List mirrors. A raw {@code List} (with an explicit {@code Comparable} cast inside) is used rather
    // than {@code List<? extends Comparable>} so the call site type-checks under {@code @TypeChecked}
    // without the wildcard-generic method-resolution failure that the parameterised form provokes.

    /** List mirror of {@link #ascending(int[])}. */
    static boolean ascending(List a) {
        for (int i = 1; i < a.size(); i++) if (((Comparable) a.get(i - 1)).compareTo(a.get(i)) > 0) return false
        true
    }

    /** List mirror of {@link #descending(int[])}. */
    static boolean descending(List a) {
        for (int i = 1; i < a.size(); i++) if (((Comparable) a.get(i - 1)).compareTo(a.get(i)) < 0) return false
        true
    }

    /** List mirror of {@link #strictlyAscending(int[])}. */
    static boolean strictlyAscending(List a) {
        for (int i = 1; i < a.size(); i++) if (((Comparable) a.get(i - 1)).compareTo(a.get(i)) >= 0) return false
        true
    }

    /** List mirror of {@link #strictlyDescending(int[])}. */
    static boolean strictlyDescending(List a) {
        for (int i = 1; i < a.size(); i++) if (((Comparable) a.get(i - 1)).compareTo(a.get(i)) <= 0) return false
        true
    }
}
