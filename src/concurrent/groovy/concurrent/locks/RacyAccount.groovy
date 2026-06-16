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
 * The unlocked {@link Account} — the bug the monitor-invariant proof assumes away. With no mutual
 * exclusion, the read-modify-write in {@code deposit}/{@code withdraw} races: two operations can read the
 * same {@code balance} and one update is lost (and {@code withdraw}'s check-then-act can overdraw past
 * {@code balance >= 0}). Lincheck finds the interleaving and reports it as a linearizability violation —
 * the runtime evidence that the checker's "given mutual exclusion" caveat is load-bearing.
 */
@CompileStatic
@POJO
class RacyAccount {
    private int balance

    RacyAccount(int initial) { balance = initial }

    void deposit(int amount) { balance += amount }

    boolean withdraw(int amount) {
        if (amount <= balance) { balance -= amount; return true }
        false
    }

    int balance() { balance }
}
