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

/** 'P68 financial' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G190_p68_financial {

    static final List<Map> CASES = [
        // (Decimal-list `sum()` is now modelled — Phase 70 — so the former "skips loudly" boundary test
        // moved to the P70 group below as a verifying example.)

        // ---------- Phase 68: financial conservation & no-cents-lost proofs ----------
        // "No money is lost in an account transfer": the total across two BigDecimal balances is
        // invariant. Z3's exact Real sort models BigDecimal +/- faithfully, so this is a real proof.
        [group: 'P68 financial', name: 'transfer conserves total (no money lost)', ok: true,
         src: tc('''class Bank {
                       BigDecimal alice, bob
                       @Requires({ amt >= 0.0 && amt <= alice })
                       @Ensures({ alice + bob == old.alice + old.bob })          // no money is lost in the transfer
                       void transfer(BigDecimal amt) { alice = alice - amt; bob = bob + amt }
                   }
                   // Change the body to `bob = bob + amt - 0.01` — a salami slice — and the @Ensures REFUTES.''')],
        // The proof is NOT vacuous: a transfer that skims a cent (the classic "salami slice") is
        // caught — the total drops by 0.01, so conservation refutes. (This needed the Phase 67
        // decimal-assignment fix: an int-shadowed field write used to hide the skim.)
        [group: 'P68 financial', name: 'salami-slice skim is caught (refutes)',
         expect: 'Cannot prove postcondition',
         src: tc('''class Bank {
                       BigDecimal alice
                       BigDecimal bob
                       @Requires({ amt >= 0.0 })
                       @Ensures({ alice + bob == old.alice + old.bob })
                       void transfer(BigDecimal amt) { alice = alice - amt; bob = bob + amt - 0.01 }
                   }''')],
        // "No fractional cents are syphoned in an interest calculation": modelling money as integer
        // cents, the credited (floored) amount plus the retained remainder equals the exact interest
        // — nothing vanishes. (Integer cents is the soundest money model; the framework is strongest here.)
        [group: 'P68 financial', name: 'interest credits every cent (round-trip)', ok: true,
         src: tc('''class C {
                       @Requires({ principal >= 0 && rateNum >= 0 && rateDen > 0 })
                       @Ensures({ result * rateDen + (principal * rateNum) % rateDen == principal * rateNum })   // every cent accounted for
                       static int interestCents(int principal, int rateNum, int rateDen) {
                           (principal * rateNum).intdiv(rateDen)
                       }
                   }''')],
        // The retained remainder is a real, bounded fraction of a cent — accounted for, not pocketed.
        [group: 'P68 financial', name: 'interest remainder is bounded [0, den)', ok: true,
         src: tc('''class C {
                       @Requires({ principal >= 0 && rateNum >= 0 && rateDen > 0 })
                       @Ensures({ result >= 0 && result < rateDen })
                       static int leftoverCents(int principal, int rateNum, int rateDen) {
                           (principal * rateNum) % rateDen
                       }
                   }''')],
        // Soundness anchor: a calc claiming it credits the *exact* interest (no remainder) is refuted
        // whenever a remainder exists — the framework catches the lost fractional cents.
        [group: 'P68 financial', name: 'claiming exact credit (losing remainder) refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ principal >= 0 && rateNum >= 0 && rateDen > 0 })
                       @Ensures({ result * rateDen == principal * rateNum })
                       static int interestCents(int principal, int rateNum, int rateDen) {
                           (principal * rateNum).intdiv(rateDen)
                       }
                   }''')],
    ]
}
