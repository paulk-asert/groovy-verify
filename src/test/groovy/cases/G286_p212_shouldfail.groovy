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

/** 'P212 shouldFail' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G286_p212_shouldfail {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'GroovyAssert.shouldFail as a PROVABLE fragment (the exceptional analogue of closed-call evaluation): shouldFail(E) { m(consts) } is a ground claim — the callee body is inlined with the constant arguments, guards are decided by closed evaluation, and the unique execution path either reaches a throw of (a subtype of) E (verified silently) or refutes with the concrete reason ("completes normally, returning 4" / "throws X, not the expected Y"). Untyped shouldFail and direct throws work; supertype expectations match via the class hierarchy; anything outside the closed-witness fragment skips loudly — groovy-test still checks the claim at runtime, the graceful-degradation posture everywhere else. First step of the exceptional-contracts arc (next: the @ThrowsIf universal).'

    static final List<Map> CASES = [

        // ---------- Phase 212: shouldFail — the provable exceptional witness ----------
        [group: 'P212 shouldFail', name: 'closed witness verifies (guard-throw callee)', ok: true,
         src: tc('''class C {
                        static int inc(int n) {
                            if (n < 0) throw new IllegalArgumentException('negative')
                            return n + 1
                        }
                        static void demo() {
                            GroovyAssert.shouldFail(IllegalArgumentException) { inc(-1) }
                        }
                    }''')],
        [group: 'P212 shouldFail', name: 'never-throwing block refutes, naming the returned value', expect: 'the block completes normally (returning 4)',
         src: tc('''class C {
                        static int inc(int n) {
                            if (n < 0) throw new IllegalArgumentException('negative')
                            return n + 1
                        }
                        static void demo() {
                            GroovyAssert.shouldFail(IllegalArgumentException) { inc(3) }
                        }
                    }''')],
        [group: 'P212 shouldFail', name: 'wrong exception type refutes, naming both types', expect: 'throws IllegalArgumentException, not the expected IllegalStateException',
         src: tc('''class C {
                        static int inc(int n) {
                            if (n < 0) throw new IllegalArgumentException('negative')
                            return n + 1
                        }
                        static void demo() {
                            GroovyAssert.shouldFail(IllegalStateException) { inc(-1) }
                        }
                    }''')],
        [group: 'P212 shouldFail', name: 'supertype expectation verifies (IAE is a RuntimeException)', ok: true,
         src: tc('''class C {
                        static int inc(int n) {
                            if (n < 0) throw new IllegalArgumentException('negative')
                            return n + 1
                        }
                        static void demo() {
                            GroovyAssert.shouldFail(RuntimeException) { inc(-1) }
                        }
                    }''')],
        [group: 'P212 shouldFail', name: 'untyped shouldFail with a direct throw verifies (static import)', ok: true,
         src: tc('''class C {
                        static void demo() {
                            shouldFail { throw new IllegalStateException('boom') }
                        }
                    }''')],
        [group: 'P212 shouldFail', name: 'non-closed argument skips loudly (runtime still checks)', expect: 'Skipped shouldFail claim',
         src: tc('''class C {
                        static int inc(int n) {
                            if (n < 0) throw new IllegalArgumentException('negative')
                            return n + 1
                        }
                        static void demo(int k) {
                            GroovyAssert.shouldFail(IllegalArgumentException) { inc(k) }
                        }
                    }''')],
    ]
}
