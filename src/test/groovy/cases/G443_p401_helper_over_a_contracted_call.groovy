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

/**
 * 'P401 helper over a contracted call' — a contract-free helper is evaluated as its body (Phase 8a), but a contracted
 * call inside that body didn't translate (the pure evaluator leaves contracted methods to the call-site machinery), so
 * the helper's own symbol was left unconstrained: `assert viaLiteral() == 2` with `viaLiteral() { isqrt(5) }` stayed
 * open whatever isqrt promised. Inside a helper's body such a call is now a value bound by the callee's @Ensures,
 * assumed only under its @Requires; a refutation resting on it withholds its call.
 */
class G443_p401_helper_over_a_contracted_call {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 401: a contracted call inside a contract-free helper's body is bound by the callee's @Ensures (under its @Requires), so a claim about the helper follows from the callee's contract; a refutation resting on it withholds its call."

    static final String NOTE = "no failing call: the failure rests on what isqrt(…) returns inside a helper"

    static final List<Map> CASES = [

        // Before (Phase 400's boundary): `Assertion may not hold: (G.viaLiteral() == 2)` — viaLiteral's own symbol was unconstrained, its body's isqrt(5) untranslated.
        [group: "P401 helper over a contracted call", name: "a contract-free helper over a contracted call proves by the callee's contract",
         ok: true,
         src: tc('''class G {
                            @Requires({ n >= 0 })
                            @Ensures({ result >= 0 && result * result <= n && n < (result + 1) * (result + 1) })
                            static int isqrt(int n) {
                                int r = 0
                                @Invariant({ 0 <= r && r * r <= n })
                                @Decreases({ n - r * r })
                                while ((r + 1) * (r + 1) <= n) { r = r + 1 }
                                return r
                            }
                            static int viaLiteral() {
                                isqrt(5)
                            }
                            static void main(String[] args) {
                                assert viaLiteral() == 2
                                assert isqrt(9) == 3
                            }
                        }''')],

        // groovy6-functional's GoodCalls.viaIfCondition: the call on the branch n >= 0, -1 on the other.
        [group: "P401 helper over a contracted call", name: "… under a branch of the helper too",
         ok: true,
         src: tc('''class G {
                            @Requires({ n >= 0 })
                            @Ensures({ result >= 0 && result * result <= n && n < (result + 1) * (result + 1) })
                            static int isqrt(int n) {
                                int r = 0
                                @Invariant({ 0 <= r && r * r <= n })
                                @Decreases({ n - r * r })
                                while ((r + 1) * (r + 1) <= n) { r = r + 1 }
                                return r
                            }
                            static int viaIfCondition(int n) {
                                if (n >= 0) {
                                    return isqrt(n)
                                }
                                -1
                            }
                            static void main(String[] args) {
                                assert viaIfCondition(9) == 3
                                assert viaIfCondition(-1) == -1
                            }
                        }''')],

        [group: "P401 helper over a contracted call", name: "a wrong claim through the helper refutes, the call withheld",
         expect: ["Assertion may not hold: (G.viaLiteral() == 3)", NOTE], refute: "fails on: main",
         src: tc('''class G {
                            @Requires({ n >= 0 })
                            @Ensures({ result >= 0 && result * result <= n && n < (result + 1) * (result + 1) })
                            static int isqrt(int n) {
                                int r = 0
                                @Invariant({ 0 <= r && r * r <= n })
                                @Decreases({ n - r * r })
                                while ((r + 1) * (r + 1) <= n) { r = r + 1 }
                                return r
                            }
                            static int viaLiteral() {
                                isqrt(5)
                            }
                            static void main(String[] args) {
                                assert viaLiteral() == 3
                            }
                        }''')],

        // Unguarded, h(-1)'s isqrt(-1) would assume r*r <= -1 and prove anything; the precondition's failure is reported in h.
        [group: "P401 helper over a contracted call", name: "the callee's contract holds only under its precondition: no vacuity",
         expect: ["Cannot prove precondition of isqrt at this call site", "Assertion may not hold: (G.h(-1) == 5)", NOTE], refute: "fails on: main",
         src: tc('''class G {
                            @Requires({ n >= 0 })
                            @Ensures({ result >= 0 && result * result <= n && n < (result + 1) * (result + 1) })
                            static int isqrt(int n) {
                                int r = 0
                                @Invariant({ 0 <= r && r * r <= n })
                                @Decreases({ n - r * r })
                                while ((r + 1) * (r + 1) <= n) { r = r + 1 }
                                return r
                            }
                            static int h(int n) { isqrt(n) }
                            static void main(String[] args) {
                                assert h(-1) == 5
                            }
                        }''')],
    ]
}
