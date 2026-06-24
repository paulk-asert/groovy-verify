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

import groovy.transform.CompileStatic
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.extension.ExtendWith
import org.pastalab.fray.junit.junit5.FrayTestExtension
import org.pastalab.fray.junit.junit5.annotations.FrayTest

/**
 * Dining philosophers — the <em>structural</em> half that pairs with the {@code P-philosophers} verifier proof.
 * groovy-verify proves the thread-local invariant (each philosopher acquires its two forks in increasing index
 * order, and the naive scheme violates it at the wrap-around philosopher i = N-1); Fray drives the real JVM
 * scheduler over N hand-threaded philosophers to confirm the <em>global</em> consequence — the ordered version
 * never deadlocks, the naive one can. The N-fork generalisation of {@link BankTransferFrayTest}'s two-account
 * lock ordering: deadlock-freedom by <strong>resource hierarchy</strong> (a global order on the locks ⇒ an
 * acyclic wait-for graph ⇒ no deadlock).
 *
 * <p>As in the bank test, Fray seizes every JVM thread, so Groovy's {@code PIC-Cleaner} daemon reads as a false
 * deadlock; the {@code frayCheck} task suppresses it with {@code -Dgroovy.indy.callsite.cleaner.inline=true}, and
 * {@code ignoreTimedBlock = true} makes a timed park count as blocking so a deadlock is declared cleanly.
 */
@CompileStatic
@ExtendWith(FrayTestExtension)
class DiningPhilosophersFrayTest {

    /** A small circle is enough to close the cycle: 3 philosophers, 3 forks. */
    private static final int N = 3

    private static Object[] newForks() {
        Object[] forks = new Object[N]
        for (int k = 0; k < N; k++) forks[k] = new Object()
        forks
    }

    /** Philosopher {@code i} eats by acquiring its two forks in INCREASING index order (resource hierarchy):
     *  every philosopher locks the lower-indexed fork of its pair first, so no cycle can form. */
    private static void eatOrdered(Object[] forks, int i) {
        int left = i, right = (i + 1) % forks.length
        int firstIdx = Math.min(left, right), secondIdx = Math.max(left, right)
        synchronized (forks[firstIdx]) {
            synchronized (forks[secondIdx]) {
                // hold both forks briefly — "eat"
            }
        }
    }

    /** Philosopher {@code i} grabs its LEFT fork then its RIGHT — the wrap-around philosopher (i = N-1) takes
     *  fork N-1 then fork 0, closing the cycle, so opposite ends can deadlock. */
    private static void eatNaive(Object[] forks, int i) {
        synchronized (forks[i]) {
            synchronized (forks[(i + 1) % forks.length]) {
                // hold both forks briefly — "eat"
            }
        }
    }

    @FrayTest(iterations = 50, ignoreTimedBlock = true)
    void resourceHierarchyIsDeadlockFree() {
        Object[] forks = newForks()
        Thread[] phils = new Thread[N]
        for (int i = 0; i < N; i++) {
            final int idx = i
            phils[i] = new Thread({ eatOrdered(forks, idx) } as Runnable)
        }
        for (Thread t : phils) t.start()
        for (Thread t : phils) t.join()
    }

    @FrayTest(iterations = 50, ignoreTimedBlock = true)
    @Disabled('Enable to watch Fray find the dining-philosophers deadlock — it FAILS by design, the wrap-around philosopher closing the cycle.')
    void naiveAcquisitionCanDeadlock() {
        Object[] forks = newForks()
        Thread[] phils = new Thread[N]
        for (int i = 0; i < N; i++) {
            final int idx = i
            phils[i] = new Thread({ eatNaive(forks, idx) } as Runnable)
        }
        for (Thread t : phils) t.start()
        for (Thread t : phils) t.join()
    }
}
