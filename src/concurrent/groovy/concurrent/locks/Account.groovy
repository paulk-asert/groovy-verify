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
package concurrent.locks

import groovy.transform.CompileStatic
import groovy.transform.stc.POJO

/**
 * A thread-safe bank account — one shared domain class for two structural tests. The checker (rung 1) proves each
 * critical section preserves {@code balance >= 0} <em>given</em> mutual exclusion; it explicitly does NOT verify the
 * mutual exclusion itself ("no race on unlocked access"). Two rung-3 tests cover that assumed half on real bytecode:
 * <ul>
 *   <li><b>Lincheck</b> ({@code AccountLincheckTest}) — every method is a {@code synchronized} critical section
 *       (what {@code @WithWriteLock}/{@code @WithReadLock} weave), so {@code withdraw}'s guard-and-update is one
 *       atomic step. {@link RacyAccount} drops the locks; Lincheck shows the difference.</li>
 *   <li><b>Fray</b> ({@code BankTransferFrayTest}) — uses the {@code id} for a global lock order across two
 *       accounts, so an ordered transfer is deadlock-free while the naive one (lock in argument order) can
 *       deadlock.</li>
 * </ul>
 */
@CompileStatic
@POJO
class Account {
    /** A stable identity for lock ordering (the Fray transfer test); the monitor tests don't need it. */
    final int id
    private int balance

    Account(int id, int initial) { this.id = id; this.balance = initial }
    Account(int initial) { this(0, initial) }

    synchronized void deposit(int amount) { balance += amount }

    /** Check-and-debit as ONE atomic critical section — the monitor-invariant proof's premise. */
    synchronized boolean withdraw(int amount) {
        if (amount <= balance) { balance -= amount; return true }
        false
    }

    synchronized int balance() { balance }
}
