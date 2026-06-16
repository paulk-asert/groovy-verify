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
package concurrent

import groovy.transform.CompileStatic
import groovy.transform.stc.POJO
import org.jetbrains.kotlinx.lincheck.LinChecker
import org.jetbrains.kotlinx.lincheck.annotations.Operation
import org.jetbrains.kotlinx.lincheck.strategy.managed.modelchecking.ModelCheckingOptions
import org.junit.jupiter.api.Test

import static org.junit.jupiter.api.Assertions.assertThrows

/**
 * Rung 3 of the three-rung story (see {@code docs/README.md}): Lincheck model-checks the ACTUAL bytecode
 * of a lock-free buffer across interleavings, discharging the atomicity/ordering assumption the
 * compile-time checker (rung 1) and the TLA+ model (rung 2) leave open.
 *
 * <p>The operation-holder classes are {@code @CompileStatic} (like the buffers): they are what Lincheck
 * instruments and replays, so their bytecode must be dispatch-free. The outer JUnit driver is ordinary
 * Groovy — it just calls {@code LinChecker.check} once and never takes part in the explored execution.
 *
 * <p>The SPSC contract is pinned with {@code nonParallelGroup}: at most one producer ({@code offer}) and
 * one consumer ({@code poll}) at a time, but a producer and a consumer may interleave freely — the exact
 * rely/guarantee discipline the verified {@code Buffer} assumes. Lincheck then checks the result is always
 * linearizable: every polled value was offered, in FIFO order, none lost or torn.
 */
@CompileStatic
@POJO
class BufferLincheckTest {

    /** The correct buffer: writes the value, then publishes it. Expected linearizable. */
    @CompileStatic
    @POJO
    static class Correct {
        private final SpscBuffer b = new SpscBuffer(3)
        @Operation(nonParallelGroup = 'producer') boolean offer(int x) { b.offer(x) }
        @Operation(nonParallelGroup = 'consumer') Integer poll() { b.poll() }
    }

    /** The leaky buffer: publishes the slot before writing it. Expected NON-linearizable (the leak). */
    @CompileStatic
    @POJO
    static class Leaky {
        private final SpscBufferLeaky b = new SpscBufferLeaky(3)
        @Operation(nonParallelGroup = 'producer') boolean offer(int x) { b.offer(x) }
        @Operation(nonParallelGroup = 'consumer') Integer poll() { b.poll() }
    }

    private static ModelCheckingOptions opts() {
        new ModelCheckingOptions()
                .iterations(30)
                .threads(2)
                .actorsPerThread(3)
                .actorsBefore(1)
                .actorsAfter(0)
    }

    @Test
    void correctBufferIsLinearizable() {
        LinChecker.check(Correct, opts())        // passes: no interleaving breaks FIFO
    }

    @Test
    void leakyBufferIsCaught() {
        // Lincheck finds the publish-before-write window and reports it as a linearizability violation
        // (a poll returns a value that was never offered) — the runtime form of the §VII leak.
        assertThrows(AssertionError) { LinChecker.check(Leaky, opts()) }
    }
}
