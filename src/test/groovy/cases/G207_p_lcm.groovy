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

/** 'P-lcm' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G207_p_lcm {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Least common multiple via Lcm.of(a,b): the identity lcm*gcd == a*b proves symbolically and literals unfold via Euclid.'

    static final List<Map> CASES = [

        // ---------- Lcm.of(a, b) — least common multiple (sibling of Gcd.of) ----------
        // Lowered to an uninterpreted lcm$ built on gcd$: base (lcm(a,0)=lcm(0,b)=0) + the fundamental
        // identity lcm(a,b)*gcd(a,b) == a*b. The identity proves symbolically; concrete values unfold via
        // Euclid's gcd then NIA. Like gcd/fib it is prove-friendly but refute-hostile on values.
        [group: 'P-lcm', name: 'identity: Lcm.of(a,b) * Gcd.of(a,b) == a*b', ok: true,
         src: tc('class C { @Ensures({ Lcm.of(a, b) * Gcd.of(a, b) == a * b }) static int f(int a, int b) { 0 } }')],
        [group: 'P-lcm', name: 'Lcm.of(4, 6) == 12', ok: true,
         src: tc('class C { @Ensures({ result == 12 }) static int f() { Lcm.of(4, 6) } }')],
        [group: 'P-lcm', name: 'Lcm.of(a, 0) == 0', ok: true,
         src: tc('class C { @Ensures({ result == 0 }) static int f(int a) { Lcm.of(a, 0) } }')],
        // Dividing by a gcd discharges its divisor-non-zero obligation (the lcm idiom `a / gcd * b`),
        // via the gcd-nonzero axiom — `Gcd.of(a,b) != 0` when the args aren't both zero.
        [group: 'P-lcm', name: 'divide by gcd: divisor obligation discharges', ok: true,
         src: tc('class C { @Requires({ a != 0 || b != 0 }) static int f(int a, int b) { a.intdiv(Gcd.of(a, b)) } }')],
        // Soundness: without that precondition gcd(0,0)==0 is possible, so the divisor obligation is NOT
        // discharged — loudly rejected (could-not-decide on the divisor), never a silent pass.
        [group: 'P-lcm', name: 'divide by gcd without precondition is not discharged (sound)', expect: 'Could not decide divisor non-zero',
         src: tc('class C { static int f(int a, int b) { a.intdiv(Gcd.of(a, b)) } }')],
        // A false VALUE soft-fails to a loud "could not decide" (refute-hostile, like gcd) — sound,
        // rejected, never a false pass.
        [group: 'P-lcm', name: 'Lcm.of(4, 6) == 13: false value soft-fails (sound)', expect: 'Could not decide',
         src: tc('class C { @Ensures({ result == 13 }) static int f() { Lcm.of(4, 6) } }')],
    ]
}
