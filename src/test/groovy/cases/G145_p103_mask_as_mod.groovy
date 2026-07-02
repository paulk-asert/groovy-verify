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

/** 'P103 mask-as-mod' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G145_p103_mask_as_mod {

    static final List<Map> CASES = [
        // Phase 103 — a low-bit mask `x & (2^k - 1)` is modelled as the Euclidean mod `x mod 2^k` (its low k
        // bits, exact for all x), keeping it in LIA so it bridges to %/+/divisibility. Lands the OpenJML
        // BitVectors tutorial's final proof (round-up to a multiple of 16), where a bit-vector `&` times out
        // on `result % 16 == 0`. Also makes parity/masking (`x & 1`) arithmetic rather than bit-blasted.
        [group: 'P103 mask-as-mod', name: 'OpenJML round-up to 16 proves (range + mod16)', ok: true,
         src: tc('''class C {
                        @Requires({ n <= 0x7ffffff0 })
                        @Ensures({ n <= result && result <= n + 15 && result % 16 == 0 })
                        static int roundUp(int n) { n + ((-n) & 0x0f) }
                    }''')],
        [group: 'P103 mask-as-mod', name: 'soundness: result%16==8 refutes (n=INT_MIN)', ok: false, expect: 'postcondition',
         src: tc('''class C {
                        @Requires({ n <= 0x7ffffff0 })
                        @Ensures({ result % 16 == 8 })
                        static int roundUp(int n) { n + ((-n) & 0x0f) }
                    }''')],
        [group: 'P103 mask-as-mod', name: 'parity x & 1 in {0,1} arithmetic', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 || result == 1 })
                        static int parity(int x) { x & 1 }
                    }''')],
        [group: 'P103 mask-as-mod', name: 'low-bit mask x & 7 in [0,7]', ok: true,
         src: tc('''class C {
                        @Ensures({ result >= 0 && result <= 7 })
                        static int low3(int x) { x & 7 }
                    }''')],
    ]
}
