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
 * The README "Locks — the monitor invariant" {@code Account}, made into real concurrent code. The checker
 * (rung 1) proves each critical section preserves {@code balance >= 0} <em>given</em> mutual exclusion;
 * it explicitly does NOT verify the mutual exclusion itself ("no race on unlocked access"). This rung
 * tests exactly that assumed half: every method is a {@code synchronized} critical section (modelling what
 * {@code @WithWriteLock}/{@code @WithReadLock} weave), so the guard-and-update in {@code withdraw} is one
 * atomic step. {@link RacyAccount} drops the locks; Lincheck shows the difference.
 */
@CompileStatic
@POJO
class Account {
    private int balance

    Account(int initial) { balance = initial }

    synchronized void deposit(int amount) { balance += amount }

    /** Check-and-debit as ONE atomic critical section — the monitor-invariant proof's premise. */
    synchronized boolean withdraw(int amount) {
        if (amount <= balance) { balance -= amount; return true }
        false
    }

    synchronized int balance() { balance }
}
