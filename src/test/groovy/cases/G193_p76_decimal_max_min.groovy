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

/** 'P76 decimal max/min' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G193_p76_decimal_max_min {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'List<BigDecimal> max/min as a witnessed extremum (bounds every element, achieved by one).'

    static final List<Map> CASES = [

        // ---------- Phase 76: List<BigDecimal>.max() / .min() — the Real witnessed extremum ----------
        // The sort-generic maxMinOf now serves Real (BigDecimal) contents, not just Int (Phase 60): a fresh
        // `r` that bounds every element AND is achieved by one, with the order comparisons reused (le/ge are
        // arithmetic-polymorphic over Int and Real in Z3). Composes with the Phase-70 decimal `.sum()`.
        [group: 'P76 decimal max/min', name: 'decimal max bounds every element', ok: true,
         src: tc('''class C {
                       @Requires({ xs.size() > 0 })
                       @Ensures({ (0..<xs.size()).every { xs[it] <= xs.max() } })
                       static void check(List<BigDecimal> xs) { }
                   }''')],
        [group: 'P76 decimal max/min', name: 'decimal max is achieved by some element', ok: true,
         src: tc('''class C {
                       @Requires({ xs.size() > 0 })
                       @Ensures({ (0..<xs.size()).any { xs[it] == xs.max() } })
                       static void check(List<BigDecimal> xs) { }
                   }''')],
        [group: 'P76 decimal max/min', name: 'decimal min bounds every element (>=)', ok: true,
         src: tc('''class C {
                       @Requires({ xs.size() > 0 })
                       @Ensures({ (0..<xs.size()).every { xs[it] >= xs.min() } })
                       static void check(List<BigDecimal> xs) { }
                   }''')],
        // Both extrema compose: max >= min for any non-empty decimal list (min is achieved at some j, and
        // max bounds that same element).
        [group: 'P76 decimal max/min', name: 'decimal max >= min (non-empty)', ok: true,
         src: tc('''class C {
                       @Requires({ xs.size() > 0 })
                       @Ensures({ xs.max() >= xs.min() })
                       static void check(List<BigDecimal> xs) { }
                   }''')],
        // Concrete shape: over a 2-element list the max bounds both entries.
        [group: 'P76 decimal max/min', name: 'decimal max of pair bounds both', ok: true,
         src: tc('''class C {
                       @Requires({ xs.size() == 2 })
                       @Ensures({ xs.max() >= xs[0] && xs.max() >= xs[1] })
                       static void check(List<BigDecimal> xs) { }
                   }''')],
    ]
}
