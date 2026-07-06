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

/** 'P222 signals arms' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G294_p222_signals_arms {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'One-directional (JML signals-style) @ThrowsIf arms and survival facts (Phase 222). exhaustive = false disclaims the arm-set\'s only-when direction — the condition is SUFFICIENT for the throw but not the whole story — so must-throw stays an obligation while unlisted throw reasons are in-contract (verifier skips only-when; the rung treats an unjustified matching throw as in-domain). That admits Integer.parseInt\'s arm ({ s == null }, its full condition being outside the fragment; note parseInt CALLS are natively modelled with a validity obligation — the arm is ledger/rung documentation). The second half is SURVIVAL FACTS: an executed call the program moved past did not throw, so each registry arm\'s condition is asserted FALSE on the continuation (the contrapositive of must-throw, valid for iff and one-directional arms alike) — wired into the body assign paths, deliberately NOT into the Phase 218 admission axiom (a contract MENTIONS a value; it does not execute a call). Showpieces: Objects.checkIndex-then-index proves the array access from the JDK\'s own guard method (contrapositive bounds + identity ensures); Math.negateExact survival proves a != Integer.MIN_VALUE.'

    static final List<Map> CASES = [

        // ---------- Phase 222: one-directional arms + survival facts ----------
        // THE showpiece: the JDK's own guard method proves the array access — checkIndex's
        // contrapositive (survival ⟹ 0 <= i < a.length) + its identity ensures (j == i)
        [group: 'P222 signals arms', name: 'checkIndex-then-index: the JDK guard method proves the array access', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        static int f(int[] a, int i) {
                            int j = java.util.Objects.checkIndex(i, a.length)
                            return a[j]
                        }
                    }''')],
        // negateExact survival ⟹ a != Integer.MIN_VALUE (the contrapositive as a distinct fact)
        [group: 'P222 signals arms', name: 'negateExact survival proves a above MIN_VALUE (contrapositive)', ok: true,
         src: tc('''class C {
                        @Ensures({ result != Integer.MIN_VALUE })
                        static int f(int a) {
                            int q = Math.negateExact(a)
                            return a
                        }
                    }''')],
        // one-directional user method: second throw reason is fine under exhaustive = false
        [group: 'P222 signals arms', name: 'exhaustive=false: the unlisted throw reason is in-contract', ok: true,
         src: tc('''class C {
                        @ThrowsIf(value = { n < 0 }, exception = IllegalArgumentException, woven = false, exhaustive = false)
                        static int f(int n) {
                            if (n < 0) throw new IllegalArgumentException('negative')
                            if (n > 100) throw new IllegalArgumentException('too big')
                            return n
                        }
                    }''')],
        // the iff twin still refutes only-when
        [group: 'P222 signals arms', name: 'the iff twin still refutes the unlisted reason', expect: 'although no @ThrowsIf condition holds',
         src: tc('''class C {
                        @ThrowsIf(value = { n < 0 }, exception = IllegalArgumentException, woven = false)
                        static int f(int n) {
                            if (n < 0) throw new IllegalArgumentException('negative')
                            if (n > 100) throw new IllegalArgumentException('too big')
                            return n
                        }
                    }''')],
        // must-throw is still an obligation under exhaustive = false
        [group: 'P222 signals arms', name: 'must-throw stays an obligation under exhaustive=false', expect: 'can return normally although the condition holds',
         src: tc('''class C {
                        @ThrowsIf(value = { n < 0 }, exception = IllegalArgumentException, woven = false, exhaustive = false)
                        static int f(int n) {
                            return n
                        }
                    }''')],
    ]
}
