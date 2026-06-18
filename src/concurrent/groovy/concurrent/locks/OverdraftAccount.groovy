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
 * The thread-safe-but-wrong account — the cell that makes "logic ⊥ concurrency" concrete. Every method is
 * {@code synchronized}, so each operation is atomic and Lincheck sees a perfectly linearizable structure
 * (no race). But {@code withdraw} drops the {@code amount <= balance} guard, so the *logic* overdraws past
 * {@code balance >= 0}. Lincheck is blind to that — it checks concurrent histories against the code's own
 * sequential behaviour, and a deterministic atomic-but-wrong withdraw is "concurrency-correct over wrong
 * logic", so it PASSES. groovy-verify (rung 1) REFUTES exactly this shape — the {@code @Invariant({ balance
 * >= 0 })} can't be preserved by an unguarded debit ("Cannot prove class invariant"). Each tool catches the
 * blind spot of the other: {@link RacyAccount} is the mirror (correct logic, no lock → checker ✓, Lincheck ✗).
 */
@CompileStatic
@POJO
class OverdraftAccount {
    private int balance

    OverdraftAccount(int initial) { balance = initial }

    synchronized void deposit(int amount) { balance += amount }

    /** Atomic (synchronized → no race) but logically wrong: no {@code amount <= balance} check, so it overdraws. */
    synchronized boolean withdraw(int amount) { balance -= amount; return true }

    synchronized int balance() { balance }
}
