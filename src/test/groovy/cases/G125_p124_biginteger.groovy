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

/** 'P124 BigInteger' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G125_p124_biginteger {

    static final List<Map> CASES = [
        // ---------- Phase 124: BigInteger ----------
        // BigInteger is Groovy's arbitrary-precision integer, which is Z3's unbounded Int sort exactly — so it is
        // the *most* faithful integer type (no width / overflow concern at all). Values flow as Int (the encoder's
        // default sort), and a literal (`42g`) folds to an Int constant.
        [group: 'P124 BigInteger', name: 'addition verifies (unbounded Int)', ok: true,
         src: tc('''class C {
            @Requires({ a >= 0 && b >= 0 })
            @Ensures({ result == a + b })
            static BigInteger add(BigInteger a, BigInteger b) { a + b }
        }''')],
        [group: 'P124 BigInteger', name: 'a wrong sum refutes', expect: 'postcondition',
         src: tc('''class C {
            @Requires({ a >= 0 && b >= 0 })
            @Ensures({ result == a + b })
            static BigInteger add(BigInteger a, BigInteger b) { a - b }
        }''')],
        [group: 'P124 BigInteger', name: 'literal folds (42g)', ok: true,
         src: tc('''class C {
            @Ensures({ result == 42g })
            static BigInteger f() { 42g }
        }''')],
        [group: 'P124 BigInteger', name: 'nonlinear product (a*b >= 0) via NIA', ok: true,
         src: tc('''class C {
            @Requires({ a >= 0 && b >= 0 })
            @Ensures({ result >= 0 })
            static BigInteger mul(BigInteger a, BigInteger b) { a * b }
        }''')],
        // Honest boundary: a *literal* wider than 64 bits is left to skip loudly (the long-range fold doesn't apply);
        // arbitrary-precision *arithmetic* on values is unaffected — only an out-of-long-range literal constant skips.
        [group: 'P124 BigInteger', name: 'literal beyond 64 bits skips (boundary)', expect: 'outside the spike',
         src: tc('''class C {
            @Ensures({ result == 100000000000000000000g })
            static BigInteger big() { 100000000000000000000g }
        }''')],
    ]
}
