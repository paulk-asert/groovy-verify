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

/** 'P115 monitor-invariant' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G230_p115_monitor_invariant {

    static final List<Map> CASES = [
        // ---------- P115 lock transforms: the monitor invariant ----------
        // Groovy's lock AST transforms (@WithReadLock/@WithWriteLock/@Synchronized) are transparent to the
        // verifier — the clean body is captured at CONVERSION, before the lock wraps it at CANONICALIZATION.
        // So the class @Invariant serves as the lock/monitor invariant: each critical section is verified to
        // preserve it (Chalice/Viper's "acquire inhales the invariant, release exhales it", sequentially). We
        // prove the per-critical-section obligation; mutual exclusion / race / deadlock freedom are NOT proven
        // (those need separation logic / permissions). A lock-guarded Account whose invariant is "no overdraft":
        [group: 'P115 monitor-invariant', name: 'lock-guarded account preserves balance >= 0', ok: true,
         src: tc('''@Invariant({ balance >= 0 })
                    class Account {
                        int balance
                        @Requires({ amount >= 0 })
                        @Ensures({ balance == old.balance + amount })
                        @groovy.transform.WithWriteLock
                        void deposit(int amount) { balance = balance + amount }
                        @Requires({ 0 <= amount && amount <= balance })
                        @Ensures({ balance == old.balance - amount })
                        @groovy.transform.WithWriteLock
                        void withdraw(int amount) { balance = balance - amount }
                        @Ensures({ result == balance })
                        @groovy.transform.WithReadLock
                        int currentBalance() { return balance }
                    }''')],
        // @Synchronized works too.
        [group: 'P115 monitor-invariant', name: 'synchronized release preserves count >= 0', ok: true,
         src: tc('''@Invariant({ count >= 0 })
                    class Latch {
                        int count
                        @Requires({ count > 0 })
                        @Ensures({ count == old.count - 1 })
                        @groovy.transform.Synchronized
                        void release() { count = count - 1 }
                    }''')],
        // A @Synchronized method with no @Requires also verifies (regression guard for GROOVY-12084: the
        // groovy-contracts SynchronizedStatement→BlockStatement crash that used to bite this exact shape).
        [group: 'P115 monitor-invariant', name: 'synchronized mutator without @Requires verifies', ok: true,
         src: tc('''@Invariant({ count >= 0 })
                    class Latch {
                        int count
                        @Ensures({ count == old.count + 1 })
                        @groovy.transform.Synchronized
                        void tick() { count = count + 1 }
                    }''')],
        // Refute: an unguarded withdraw (missing amount <= balance) lets a critical section break the lock
        // invariant — the verifier catches it, so the monitor invariant is genuinely checked through the lock.
        [group: 'P115 monitor-invariant', name: 'unguarded withdraw breaks the lock invariant', expect: 'Cannot prove class invariant',
         src: tc('''@Invariant({ balance >= 0 })
                    class Account {
                        int balance
                        @Requires({ amount >= 0 })
                        @groovy.transform.WithWriteLock
                        void withdraw(int amount) { balance = balance - amount }
                    }''')],
        // Refute (non-vacuity): a wrong @Ensures refutes through the lock — proving the body is modelled, not
        // skipped (the +amount body contradicts the +amount+1 claim).
        [group: 'P115 monitor-invariant', name: 'wrong ensures refutes through the lock', expect: 'Cannot prove postcondition',
         src: tc('''@Invariant({ balance >= 0 })
                    class Account {
                        int balance
                        @Requires({ amount >= 0 })
                        @Ensures({ balance == old.balance + amount + 1 })
                        @groovy.transform.WithWriteLock
                        void deposit(int amount) { balance = balance + amount }
                    }''')],
    ]
}
