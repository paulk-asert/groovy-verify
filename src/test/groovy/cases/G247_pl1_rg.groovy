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

/** 'PL1 rg' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G247_pl1_rg {

    static final List<Map> CASES = [

        // ----- Rely/guarantee well-formedness (Smith §IV compatibility lemmas) -----
        // The producer/consumer R/G conditions over shared (head, tail). Each predicate is a two-state function:
        // the first half of its parameters is the pre-state, the second half the post-state. The verifier auto-
        // discharges: each rely reflexive + transitive, each guarantee reflexive, and G_i ⟹ R_j (i≠j). A
        // well-formed, compatible set compiles cleanly.
        [group: 'PL1 rg', name: 'rg: producer/consumer conditions are compatible (verifies)', ok: true,
         src: tc('''class Buffer {
                        @Rely('Consumer')      static boolean rCons(int oh, int ot, int h, int t) { h == oh && ot <= t }
                        @Guarantee('Producer') static boolean gProd(int oh, int ot, int h, int t) { h == oh && ot <= t }
                        @Rely('Producer')      static boolean rProd(int oh, int ot, int h, int t) { t == ot }
                        @Guarantee('Consumer') static boolean gCons(int oh, int ot, int h, int t) { t == ot && oh <= h }
                    }''')],
        // Incompatible: the producer's guarantee no longer keeps `head` fixed, so it fails to imply the consumer's
        // rely (which requires head == oh) — G_Producer ⟹ R_Consumer refutes.
        [group: 'PL1 rg', name: 'rg: producer guarantee not implying consumer rely refutes', expect: 'Rely/guarantee compatibility does not hold',
         src: tc('''class Buffer {
                        @Rely('Consumer')      static boolean rCons(int oh, int ot, int h, int t) { h == oh && ot <= t }
                        @Guarantee('Producer') static boolean gProd(int oh, int ot, int h, int t) { ot <= t }
                    }''')],
        // Ill-formed: a rely that demands the environment *increment* head is not reflexive (it forbids "no change")
        // — reflexivity refutes.
        [group: 'PL1 rg', name: 'rg: non-reflexive rely refutes', expect: 'Rely/guarantee compatibility does not hold',
         src: tc('''class Buffer {
                        @Rely('T')             static boolean rBad(int oh, int h) { h == oh + 1 }
                    }''')],
        // Ill-formed: a rely that is not transitive — "tail stays within one of its old value" doesn't compose.
        [group: 'PL1 rg', name: 'rg: non-transitive rely refutes', expect: 'Rely/guarantee compatibility does not hold',
         src: tc('''class Buffer {
                        @Rely('T')             static boolean rNT(int ot, int t) { t <= ot + 1 && ot <= t }
                    }''')],
    ]
}
