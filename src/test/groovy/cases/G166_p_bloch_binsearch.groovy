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

/** 'P-bloch binsearch' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G166_p_bloch_binsearch {

    static final List<Map> CASES = [
        // ---------- Joshua Bloch's binary-search / mergesort midpoint overflow (a JDK bug ~9 years hidden) ----------
        // "Nearly All Binary Searches and Mergesorts are Broken" (2006): `int mid = (low + high) / 2` overflows
        // once `low + high` exceeds Integer.MAX_VALUE, yielding a *negative* index. @CheckOverflow catches it at
        // compile time with the exact counterexample (a large array searched near the top); Bloch's one-line fix
        // `low + (high - low) / 2` stays within [low, high] ⊆ [0, MAX] and verifies. (Groovy spelling: `.intdiv(2)`
        // is Java's integer `/`; the overflow is in the `low + high` addition, before any division.)
        [group: 'P-bloch binsearch', name: 'buggy midpoint (low + high).intdiv(2) overflows',
         expect: 'addition overflows 32-bit signed range',
         src: tc('''class BinarySearch {
                        @CheckOverflow
                        @Requires({ 0 <= low && low <= high })          // a valid index window
                        @Ensures({ low <= result && result <= high })   // the midpoint lies within it
                        static int mid(int low, int high) { (low + high).intdiv(2) }
                    }''')],
        [group: 'P-bloch binsearch', name: 'fixed midpoint low + (high - low).intdiv(2) verifies', ok: true,
         src: tc('''class BinarySearch {
                        @CheckOverflow
                        @Requires({ 0 <= low && low <= high })
                        @Ensures({ low <= result && result <= high })
                        static int mid(int low, int high) { low + (high - low).intdiv(2) }
                    }''')],
    ]
}
