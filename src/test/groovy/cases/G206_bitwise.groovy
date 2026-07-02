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

/** 'bitwise' — 12 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G206_bitwise {

    static final List<Map> CASES = [

        // ---------- Bitwise / shift operators (& | ^ << >>) ----------
        // Shifts by a non-negative literal stay in unbounded Int arithmetic (x<<k = x*2^k, x>>k =
        // floor(x/2^k)), consistent with how */intdiv are modelled. Bitwise & | ^ (and variable shifts)
        // have no arithmetic form, so they lower to Z3's bit-vector theory at Java's 32-bit width —
        // faithful two's-complement (e.g. `a & 1` is the low bit), bit-blasted (timeout-gated).
        [group: 'bitwise', name: 'x << 1 == x * 2 (literal shift = arithmetic)', ok: true,
         src: tc('class C { @Ensures({ result == x * 2 }) static int f(int x) { x << 1 } }')],
        [group: 'bitwise', name: '1 << 4 == 16', ok: true,
         src: tc('class C { @Ensures({ result == 16 }) static int f() { 1 << 4 } }')],
        [group: 'bitwise', name: 'x >> 1 == x.intdiv(2) for x >= 0', ok: true,
         src: tc('class C { @Requires({ x >= 0 }) @Ensures({ result == x.intdiv(2) }) static int f(int x) { x >> 1 } }')],
        [group: 'bitwise', name: '6 & 3 == 2', ok: true,
         src: tc('class C { @Ensures({ result == 2 }) static int f() { 6 & 3 } }')],
        [group: 'bitwise', name: '6 | 1 == 7', ok: true,
         src: tc('class C { @Ensures({ result == 7 }) static int f() { 6 | 1 } }')],
        [group: 'bitwise', name: '5 ^ 3 == 6', ok: true,
         src: tc('class C { @Ensures({ result == 6 }) static int f() { 5 ^ 3 } }')],
        // Symbolic two's-complement identities (BV).
        [group: 'bitwise', name: 'a ^ a == 0', ok: true,
         src: tc('class C { @Ensures({ result == 0 }) static int f(int a) { a ^ a } }')],
        [group: 'bitwise', name: 'a & a == a', ok: true,
         src: tc('class C { @Ensures({ result == a }) static int f(int a) { a & a } }')],
        [group: 'bitwise', name: 'a | 0 == a', ok: true,
         src: tc('class C { @Ensures({ result == a }) static int f(int a) { a | 0 } }')],
        // BV-specific: `a & 1` is the low bit — 0 or 1 (a property no arithmetic shadow gives).
        [group: 'bitwise', name: 'a & 1 in {0, 1}', ok: true,
         src: tc('class C { @Ensures({ result == 0 || result == 1 }) static int f(int a) { a & 1 } }')],
        // Soundness: a wrong CONCRETE bit value refutes crisply (Z3 folds the BV to a constant).
        [group: 'bitwise', name: '6 & 3 == 3 refutes', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ result == 3 }) static int f() { 6 & 3 } }')],
        // A false SYMBOLIC bitwise claim is the refute-hostile direction — bit-blasting the negation
        // can't find a model in the 2s budget, so it soft-fails as a loud "could not decide" (sound:
        // rejected, never a false pass), rather than a crisp counterexample.
        [group: 'bitwise', name: 'a & b == a: false symbolic claim soft-fails (sound)', expect: 'Could not decide',
         src: tc('class C { @Ensures({ result == a }) static int f(int a, int b) { a & b } }')],
    ]
}
