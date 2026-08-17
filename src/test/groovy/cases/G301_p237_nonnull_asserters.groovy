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

/** 'P237 nonnull asserters' — 10 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G301_p237_nonnull_asserters {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Statement-position non-null asserters (Objects.requireNonNull, single-arg assertNotNull, assertThat().isNotNull()) narrow the target on the continuation — survival facts, program-point ordered and branch-scoped.'

    static final List<Map> CASES = [

        // ---------- Phase 237: statement-position non-null asserters (GROOVY-12250 parity) ----------
        // A bare `Objects.requireNonNull(x)` the program moved past is a guard-throw that didn't fire:
        // x != null on every continuing path (the Phase 222 survival argument at statement position).
        // The fact is program-point ordered — threaded as a Guard in the value-flow walk, asserted at
        // the LemmaCall step in the body proof, and replayed in region prefixes — so a deref BEFORE
        // the call, or in a path the call doesn't dominate, still refutes.
        [group: 'P237 nonnull asserters', name: 'requireNonNull narrows the later deref', ok: true,
         src: tc('''class C {
                        static int m(String s) {
                            Objects.requireNonNull(s)
                            return s.length()
                        }
                    }''')],
        [group: 'P237 nonnull asserters', name: 'requireNonNull with a message narrows too', ok: true,
         src: tc('''class C {
                        static int m(String s) {
                            Objects.requireNonNull(s, 'must not be null')
                            return s.length()
                        }
                    }''')],
        // Teeth — ordering: the deref BEFORE the asserter is not blessed by it.
        [group: 'P237 nonnull asserters', name: 'deref before requireNonNull still refutes', expect: 'Possible NullPointerException',
         src: tc('''class C {
                        static int m(String s) {
                            int n = s.length()
                            Objects.requireNonNull(s)
                            return n
                        }
                    }''')],
        // Teeth — the fact lands on the asserted variable, not the method.
        [group: 'P237 nonnull asserters', name: 'requireNonNull on a different variable still refutes', expect: 'Possible NullPointerException',
         src: tc('''class C {
                        static int m(String s, String t) {
                            Objects.requireNonNull(t)
                            return s.length()
                        }
                    }''')],
        // The JUnit spelling, matched by simple name (the NullChecker trust model). The helper is
        // local so the case is classpath-independent — and honest: it really throws.
        [group: 'P237 nonnull asserters', name: 'single-arg assertNotNull narrows', ok: true,
         src: tc('''class C {
                        static void assertNotNull(Object o) { if (o == null) throw new AssertionError('null') }
                        static int m(String s) {
                            assertNotNull(s)
                            return s.length()
                        }
                    }''')],
        // Teeth — the two-argument JUnit forms are deliberately NOT matched (JUnit 4 puts the message
        // first, JUnit 5 last — the target is ambiguous by name alone), so no fact is learned.
        [group: 'P237 nonnull asserters', name: 'two-arg assertNotNull is not matched (ambiguous target)', expect: 'Possible NullPointerException',
         src: tc('''class C {
                        static void assertNotNull(String msg, Object o) { if (o == null) throw new AssertionError(msg) }
                        static int m(String s) {
                            assertNotNull('required', s)
                            return s.length()
                        }
                    }''')],
        // The AssertJ/Truth chain spelling. The fluent helper class sits after the checked class, so
        // only C runs under the extension; the chain still narrows by shape.
        [group: 'P237 nonnull asserters', name: 'assertThat(x).isNotNull() narrows', ok: true,
         src: tc('''class C {
                        static Check assertThat(Object o) { new Check(o) }
                        static int m(String s) {
                            assertThat(s).isNotNull()
                            return s.length()
                        }
                    }
                    class Check {
                        final Object v
                        Check(Object v) { this.v = v }
                        Check isNotNull() { if (v == null) throw new AssertionError(); return this }
                    }''')],
        // Branch scoping: the fact holds where the call dominates …
        [group: 'P237 nonnull asserters', name: 'requireNonNull narrows inside its branch', ok: true,
         src: tc('''class C {
                        static int m(String s, boolean b) {
                            if (b) {
                                Objects.requireNonNull(s)
                                return s.length()
                            }
                            return 0
                        }
                    }''')],
        // … and does NOT escape the branch it ran in.
        [group: 'P237 nonnull asserters', name: 'the fact does not escape its branch', expect: 'Possible NullPointerException',
         src: tc('''class C {
                        static int m(String s, boolean b) {
                            if (b) { Objects.requireNonNull(s) }
                            return s.length()
                        }
                    }''')],
        // The GROOVY-12250 parity flagship: the survived asserter discharges a callee's @Requires.
        [group: 'P237 nonnull asserters', name: 'requireNonNull discharges the callee @Requires', ok: true,
         src: tc('''class C {
                        @Requires({ x != null })
                        static int len(String x) { x.length() }
                        static int m(String s) {
                            Objects.requireNonNull(s)
                            return len(s)
                        }
                    }''')],
    ]
}
