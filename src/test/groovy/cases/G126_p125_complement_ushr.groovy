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

/** 'P125 complement & ushr' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G126_p125_complement_ushr {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Bitwise complement ~x (the exact Int identity -x-1) and the unsigned/logical right shift x>>>1 (via the 32-bit bit-vector, always non-negative — unlike the arithmetic >>).'

    static final List<Map> CASES = [
        // ---------- Phase 125: bitwise complement (~) and unsigned right shift (>>>) ----------
        // ~x is the two's-complement complement, an exact Int identity (-x - 1) — no bit-vector, not refute-hostile.
        [group: 'P125 complement & ushr', name: 'complement identity ~x == -x - 1', ok: true,
         src: tc('class C { @Ensures({ result == -x - 1 }) static int comp(int x) { ~x } }')],
        [group: 'P125 complement & ushr', name: 'complement literal ~5 == -6', ok: true,
         src: tc('class C { @Ensures({ result == -6 }) static int c() { ~5 } }')],
        [group: 'P125 complement & ushr', name: 'a wrong complement refutes', expect: 'postcondition',
         src: tc('class C { @Ensures({ result == -x }) static int comp(int x) { ~x } }')],
        // >>> is the logical (zero-fill) shift via the 32-bit bit-vector: x >>> 1 is always non-negative …
        [group: 'P125 complement & ushr', name: 'unsigned shift is always non-negative', ok: true,
         src: tc('class C { @Ensures({ result >= 0 }) static int ushr(int x) { x >>> 1 } }')],
        // … whereas the arithmetic >> sign-fills, so it CAN be negative — the contrast that makes >>> distinct.
        [group: 'P125 complement & ushr', name: 'arithmetic >> can be negative (contrast)', expect: 'postcondition',
         src: tc('class C { @Ensures({ result >= 0 }) static int s(int x) { x >> 1 } }')],
    ]
}
