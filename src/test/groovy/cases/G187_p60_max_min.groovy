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

/** 'P60 max/min' — 8 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G187_p60_max_min {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'result == a.max()/a.min() as the witnessed-extremum spec; returning a[0] refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 60: xs.max() / xs.min() as the witnessed-extremum spec ----------
        // The ergonomic win: `result == a.max()` means exactly the every/any spec the
        // maxElement example spells out by hand — and the same max-finding loop discharges it.
        [group: 'P60 max/min', name: 'result == a.max() verified', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ result == a.max() })
                        static int maxOf(int[] a) {
                            int m = a[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= a.length &&
                                         (0..<i).every { a[it] <= m } &&
                                         (0..<i).any { a[it] == m } })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] > m) m = a[i]
                                i = i + 1
                            }
                            return m
                        }
                    }''')],
        [group: 'P60 max/min', name: 'result == a.min() verified', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ result == a.min() })
                        static int minOf(int[] a) {
                            int m = a[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= a.length &&
                                         (0..<i).every { m <= a[it] } &&
                                         (0..<i).any { a[it] == m } })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] < m) m = a[i]
                                i = i + 1
                            }
                            return m
                        }
                    }''')],
        // Soundness anchor: returning the first element isn't the max — `result == a.max()` refutes
        // (a later element can exceed a[0], so result fails the bound half of the extremum spec).
        [group: 'P60 max/min', name: 'returning a[0] is not a.max() (refutes)',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ result == a.max() })
                        static int firstOf(int[] a) { a[0] }
                    }''')],
        // Mint-once: two `a.max()` occurrences are the same term, so reflexive equality holds. Non-empty is
        // required because `[].max()` throws — without the guard the contract isn't even runtime-evaluable.
        [group: 'P60 max/min', name: 'a.max() == a.max() (mint-once)', ok: true,
         src: tc('class C { @Requires({ a != null && a.length > 0 }) @Ensures({ a.max() == a.max() }) static int f(int[] a) { 0 } }')],
        // max()/min() throw UnsupportedOperationException on an empty receiver, so the verifier requires the
        // receiver be provably non-empty — the same `0 < size` obligation as a `[0]` read (like first()/pop()).
        [group: 'P60 max/min', name: 'max() on a possibly-empty array is refused (non-empty obligation)', expect: 'IndexOutOfBoundsException',
         src: tc('class C { @Requires({ a != null }) @Ensures({ result == a.max() }) static int f(int[] a) { a.max() } }')],
        [group: 'P60 max/min', name: 'max() over a guaranteed-non-empty array verifies', ok: true,
         src: tc('class C { @Requires({ a != null && a.length > 0 }) @Ensures({ result == a.max() }) static int f(int[] a) { a.max() } }')],
        [group: 'P60 max/min', name: 'min() on a possibly-empty array is refused', expect: 'IndexOutOfBoundsException',
         src: tc('class C { @Requires({ a != null }) @Ensures({ result == a.min() }) static int f(int[] a) { a.min() } }')],
        // Vacuity guard: on an empty array the extremum is unconstrained (Groovy's [].max() is
        // undefined), so a claim about it is NOT provable — the existential can't fire vacuously.
        [group: 'P60 max/min', name: 'empty-range max claim refuted (no vacuous pass)',
         expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ a != null && a.length == 0 }) @Ensures({ a.max() == 5 }) static int f(int[] a) { 0 } }')],
    ]
}
