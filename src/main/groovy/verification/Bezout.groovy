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
package verification

import groovy.transform.CompileStatic

/**
 * The Bézout-coefficient spec helpers (Phase 204, math-comp's {@code egcdn} twin), recognised by
 * {@link NumberTheoryPack}: {@code Bezout.u(m, n)} and {@code Bezout.v(m, n)} are integer coefficients
 * with {@code m*u + n*v == Gcd.of(m, n)} — the defining axiom, minted (triggered on the {@code bezU$}
 * term) only when a contract mentions them. Executable via the extended Euclid so the runtime check works.
 */
@CompileStatic
class Bezout {

    /** The pair (u, v) with m*u + n*v == gcd(m, n) (extended Euclid, iterative). */
    private static int[] pair(int m, int n) {
        int or = m, r = n, os = 1, s = 0, ot = 0, t = 1
        while (r != 0) {
            int q = or.intdiv(r)
            int tr = or - q * r; or = r; r = tr
            int ts = os - q * s; os = s; s = ts
            int tt = ot - q * t; ot = t; t = tt
        }
        [os, ot] as int[]
    }

    /** u with m*u + n*v == gcd(m, n). */
    static int u(int m, int n) { pair(m, n)[0] }

    /** v with m*u + n*v == gcd(m, n). */
    static int v(int m, int n) { pair(m, n)[1] }
}
