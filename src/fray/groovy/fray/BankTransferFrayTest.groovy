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
package fray

import concurrent.locks.Account
import groovy.transform.CompileStatic
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.extension.ExtendWith
import org.pastalab.fray.junit.junit5.FrayTestExtension
import org.pastalab.fray.junit.junit5.annotations.FrayTest

/**
 * Fray on the README locks example — the DEADLOCK / lock-ordering half that section's checker proof
 * explicitly does not cover ("we do not verify ... no deadlock, no lock-ordering"). Where the Lincheck
 * spike checks a data structure's <em>operations</em>, Fray drives the real JVM scheduler over a
 * hand-threaded scenario: two threads transferring between two accounts in opposite directions.
 *
 * <p><strong>Groovy runtime + Fray.</strong> Fray seizes control of every thread in the JVM, so Groovy's
 * runtime daemon {@code PIC-Cleaner} thread ({@code org.codehaus.groovy.vmplugin.v8.CacheableCallSite}),
 * which parks forever on a queue, reads to Fray as a deadlock. The {@code frayCheck} task suppresses it with
 * {@code -Dgroovy.indy.callsite.cleaner.inline=true} (clean call sites inline; the static initializer then
 * skips starting the thread), so Fray sees only the application threads. {@code @CompileStatic @POJO} keeps
 * the bytecode clean.
 *
 * <p>{@code orderedTransfer} acquires the two monitors in a global id order, so no cycle can form and Fray
 * passes. {@code naiveTransfer} locks {@code from} then {@code to}, so opposite-direction transfers can
 * deadlock — enable {@link #naiveTransferCanDeadlock} to watch Fray report it (it FAILS by design), pointing
 * the two threads' stacks straight at {@code naiveTransfer}'s nested {@code synchronized}.
 *
 * <p>{@code ignoreTimedBlock = true} makes Fray treat a timed park as blocking: without it, a background
 * {@code ForkJoinPool} worker doing a timed park keeps looking schedulable while the application threads are
 * deadlocked, so Fray spins (an unbounded step explosion → OOM) instead of declaring the deadlock cleanly.
 */
@CompileStatic
@ExtendWith(FrayTestExtension)
class BankTransferFrayTest {

    // The bank account is the shared domain class (`concurrent.locks.Account`) — the same one the Lincheck
    // monitor-invariant test uses — with its `id` driving the lock order here. The transfer holds each account's
    // monitor (synchronized(account)) and moves money via the account's own synchronized debit/credit (reentrant).

    /** Lock `from` then `to` — opposite-direction transfers can deadlock (the lock-ordering bug). */
    private static void naiveTransfer(Account from, Account to, int amt) {
        synchronized (from) {
            synchronized (to) {
                from.withdraw(amt)
                to.deposit(amt)
            }
        }
    }

    /** Always lock the lower-id account first — a global lock order, so no cycle, so no deadlock. */
    private static void orderedTransfer(Account from, Account to, int amt) {
        Account first  = from.id <= to.id ? from : to
        Account second = from.id <= to.id ? to : from
        synchronized (first) {
            synchronized (second) {
                from.withdraw(amt)
                to.deposit(amt)
            }
        }
    }

    @FrayTest(iterations = 200, ignoreTimedBlock = true)
    void orderedTransferIsDeadlockFree() {
        Account a = new Account(1, 100)
        Account b = new Account(2, 100)
        Thread t1 = new Thread({ orderedTransfer(a, b, 10) } as Runnable)
        Thread t2 = new Thread({ orderedTransfer(b, a, 10) } as Runnable)
        t1.start(); t2.start()
        t1.join(); t2.join()
    }

    @FrayTest(iterations = 200, ignoreTimedBlock = true)
    @Disabled('Enable to watch Fray find the lock-ordering deadlock — it FAILS the test by design.')
    void naiveTransferCanDeadlock() {
        Account a = new Account(1, 100)
        Account b = new Account(2, 100)
        Thread t1 = new Thread({ naiveTransfer(a, b, 10) } as Runnable)
        Thread t2 = new Thread({ naiveTransfer(b, a, 10) } as Runnable)
        t1.start(); t2.start()
        t1.join(); t2.join()
    }
}
