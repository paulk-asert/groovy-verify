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

/** 'P45 cross-class' — 7 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G168_p45_cross_class {

    static final List<Map> CASES = [

        // ---------- Phase 45: cross-class @Invariant call-site assumption ----------
        // Headline: a class-typed parameter c carries Counter's invariant into the calling method.
        // Reading c.count under that invariant yields result >= 0 without any caller-side guard.
        [group: 'P45 cross-class', name: 'foreign invariant assumed at entry: c.count >= 0', ok: true,
         src: tc('''@Invariant({ count >= 0 && count <= max })
                    class Counter { int count, max }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class Client {
                        @Requires({ c != null })
                        @Ensures({ result >= 0 })
                        static int read(Counter c) { c.count }
                    }''')],
        // Sub-fields independent: c.count and c.max are distinct SMT entities (receiver-qualified).
        [group: 'P45 cross-class', name: 'foreign invariant: c.count <= c.max verifies', ok: true,
         src: tc('''@Invariant({ count >= 0 && count <= max })
                    class Counter { int count, max }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class Client {
                        @Requires({ c != null })
                        @Ensures({ result <= c.max })
                        static int read(Counter c) { c.count }
                    }''')],
        // Soundness anchor: claiming c.count > 0 isn't supported by the invariant (allows 0).
        [group: 'P45 cross-class', name: 'foreign invariant: stronger claim refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''@Invariant({ count >= 0 && count <= max })
                    class Counter { int count, max }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class Client {
                        @Requires({ c != null })
                        @Ensures({ result > 0 })
                        static int read(Counter c) { c.count }
                    }''')],
        // Two class-typed receivers carry separate invariants and don't conflate.
        [group: 'P45 cross-class', name: 'two foreign receivers: invariants independent', ok: true,
         src: tc('''@Invariant({ count >= 0 })
                    class Counter { int count }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class Client {
                        @Requires({ a != null && b != null })
                        @Ensures({ result >= 0 })
                        static int sum(Counter a, Counter b) { a.count + b.count }
                    }''')],
        // Cross-class call effect: c.someVoid() havocs c's fields but reasserts the invariant,
        // so c.count >= 0 still holds afterwards.
        [group: 'P45 cross-class', name: 'after cross-class call: invariant still holds', ok: true,
         src: tc('''@Invariant({ count >= 0 && count <= max })
                    class Counter {
                        int count, max
                        @Requires({ count < max })
                        void incr() { count = count + 1 }
                    }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class Client {
                        @Requires({ c != null && c.count < c.max })
                        @Ensures({ result >= 0 })
                        static int useCounter(Counter c) {
                            c.incr()
                            c.count
                        }
                    }''')],
        // Cross-class @Requires discharge: caller must establish the callee's precondition under
        // receiver context. With c.count < c.max in the caller's @Requires, incr()'s @Requires
        // is discharged at the call site.
        [group: 'P45 cross-class', name: 'cross-class @Requires discharges from receiver context', ok: true,
         src: tc('''@Invariant({ count >= 0 && count <= max })
                    class Counter {
                        int count, max
                        @Requires({ count < max })
                        void incr() { count = count + 1 }
                    }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class Client {
                        @Requires({ c != null && c.count < c.max })
                        static int callIt(Counter c) {
                            c.incr()
                            0
                        }
                    }''')],
        // Soundness: without c.count < c.max in the caller's @Requires, the @Requires of
        // incr() can't be discharged — incr() is callable on a counter that's already at max.
        // The counterexample names the receiver-qualified fields: c$count = 0, c$max = 0.
        [group: 'P45 cross-class', name: 'cross-class @Requires without guard refutes',
         expect: 'Cannot prove precondition of incr',
         src: tc('''@Invariant({ count >= 0 && count <= max })
                    class Counter {
                        int count, max
                        @Requires({ count < max })
                        void incr() { count = count + 1 }
                    }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class Client {
                        @Requires({ c != null })
                        static int callIt(Counter c) {
                            c.incr()
                            0
                        }
                    }''')],
    ]
}
