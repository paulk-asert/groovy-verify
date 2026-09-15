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

import groovy.concurrent.AsyncChannel
import groovy.transform.CompileStatic
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.extension.ExtendWith
import org.pastalab.fray.junit.junit5.FrayTestExtension
import org.pastalab.fray.junit.junit5.annotations.FrayTest

/**
 * Fray on the Kerridge gallery's <em>deadlock exercise</em> — two processes that each read from the other
 * before writing. The checker refutes it at COMPILE time, naming the circular wait
 * ({@code Process-network deadlock in 'deadlockExercise': circular wait: …}); nothing until now ever
 * <em>exhibited</em> the hang, so the refutation had no runtime counterpart.
 *
 * <p>This is a different deadlock mechanism from the bank-transfer case beside it, which is what earns it a
 * place at this rung: there the cycle is over two monitors and the fix is a global LOCK ORDER; here the cycle
 * is over two channels and the fix is a PRIMING SEND — one process writes before it reads, exactly the repair
 * the books teach and the gallery's primed-ring case verifies.
 *
 * <p>Both halves use the real {@code AsyncChannel}, with the two processes hand-threaded rather than run as
 * {@code async {}} tasks, so Fray schedules the application threads directly (the same shape the bank-transfer
 * test uses). {@code ignoreTimedBlock = true} for the reason recorded there: a background {@code ForkJoinPool}
 * worker's timed park would otherwise keep Fray spinning while the application threads are stuck.
 */
@CompileStatic
@ExtendWith(FrayTestExtension)
class ChannelCycleFrayTest {

    /** Read from one channel, then write to the other — a process that waits before it feeds anyone. */
    private static void readThenWrite(AsyncChannel<Integer> readFrom, AsyncChannel<Integer> writeTo) {
        int v = readFrom.first()
        writeTo.send(v)
    }

    /** Write first, then read — the priming send that breaks the cycle. */
    private static void writeThenRead(AsyncChannel<Integer> writeTo, AsyncChannel<Integer> readFrom) {
        writeTo.send(1)
        readFrom.first()
    }

    /** One process primes, so the other's receive is satisfied and the cycle never closes. */
    @FrayTest(iterations = 200, ignoreTimedBlock = true)
    void aPrimedCycleIsDeadlockFree() {
        AsyncChannel<Integer> aToB = AsyncChannel.create(1)
        AsyncChannel<Integer> bToA = AsyncChannel.create(1)
        Thread a = new Thread({ writeThenRead(aToB, bToA) } as Runnable)
        Thread b = new Thread({ readThenWrite(aToB, bToA) } as Runnable)
        a.start(); b.start()
        a.join(); b.join()
    }

    /** Both processes read before writing: nobody ever sends, so both receives wait for each other. */
    @FrayTest(iterations = 200, ignoreTimedBlock = true)
    @Disabled('Enable to watch Fray find the mutual-receive cycle — it FAILS the test by design.')
    void aMutualReceiveCycleDeadlocks() {
        AsyncChannel<Integer> aToB = AsyncChannel.create(1)
        AsyncChannel<Integer> bToA = AsyncChannel.create(1)
        Thread a = new Thread({ readThenWrite(bToA, aToB) } as Runnable)
        Thread b = new Thread({ readThenWrite(aToB, bToA) } as Runnable)
        a.start(); b.start()
        a.join(); b.join()
    }
}
