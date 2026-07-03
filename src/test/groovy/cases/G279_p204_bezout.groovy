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

/** 'P204 bezout' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G279_p204_bezout {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Bezout coefficients (math-comp div.v egcdn): Bezout.u/v(m, n) are skolemized coefficient witnesses with the defining axiom m*u + n*v == Gcd.of(m, n), minted only for contracts that mention them. The identity itself verifies; coprime arguments yield the unit combination (m*u + n*v == 1); Euclid/Gauss — coprime(a,n) and n | a*b implies n | b — verifies as ring algebra over the axiom with the divisibility witness skolemized as a parameter. Teeth: an off-by-one identity claim is disproved, and a wrong Gauss quotient never proves.'

    static final List<Map> CASES = [

        // ---------- Phase 204: Bezout coefficients — the div.v layer under gcd$ ----------
        // The defining identity, directly.
        [group: 'P204 bezout', name: 'Bezout identity m*u + n*v == gcd', ok: true,
         src: tc('''class C {
                       @Ensures({ m * Bezout.u(m, n) + n * Bezout.v(m, n) == Gcd.of(m, n) })
                       static void identity(int m, int n) {}
                   }''')],
        // Coprime arguments: the combination is the unit.
        [group: 'P204 bezout', name: 'coprime gives the unit combination', ok: true,
         src: tc('''class C {
                       @Requires({ Gcd.of(a, n) == 1 })
                       @Ensures({ a * Bezout.u(a, n) + n * Bezout.v(a, n) == 1 })
                       static void unit(int a, int n) {}
                   }''')],
        // Euclid/Gauss: coprime(a, n) && n | a*b  ⟹  n | b — the divisibility hypothesis arrives with its
        // witness t (a*b == n*t, the same skolemized-∃ posture as everywhere in the repo), and the quotient
        // of b by n is exhibited: b == n * (u*t + v*b), pure ring algebra over the Bezout axiom.
        [group: 'P204 bezout', name: 'Gauss: coprime and n | a*b imply n | b', ok: true,
         src: tc('''class C {
                       @Requires({ Gcd.of(a, n) == 1 && a * b == n * t })
                       @Ensures({ b == n * (Bezout.u(a, n) * t + Bezout.v(a, n) * b) })
                       static void gauss(int a, int n, int b, int t) {}
                   }''')],
        // Teeth, disproof form: the identity is off by one — provably ruled out.
        [group: 'P204 bezout', name: 'off-by-one identity is disproved', ok: true,
         src: tc('''class C {
                       @Ensures({ m * Bezout.u(m, n) + n * Bezout.v(m, n) != Gcd.of(m, n) + 1 })
                       static void offByOne(int m, int n) {}
                   }''')],
        // Teeth, inconsistency canary: a wrong Gauss quotient must never cleanly prove (refutes, or the
        // NIA universals time MBQI out — either way the diagnostic matches; a clean verify fails loudly).
        [group: 'P204 bezout', name: 'a wrong Gauss quotient never proves (inconsistency canary)', expect: 'postcondition of gauss',
         src: tc('''class C {
                       @Requires({ Gcd.of(a, n) == 1 && a * b == n * t })
                       @Ensures({ b == n * (Bezout.u(a, n) * t + Bezout.v(a, n) * b) + 1 })
                       static void gauss(int a, int n, int b, int t) {}
                   }''')],
    ]
}
