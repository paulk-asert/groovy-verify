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
import org.jetbrains.lincheck.datastructures.Operation
import org.jetbrains.lincheck.datastructures.StressOptions
import org.junit.jupiter.api.Test

import static org.junit.jupiter.api.Assertions.assertThrows

/**
 * Rung 3 for Groovy 6 async/await: groovy-verify proves the *functional* half of {@link AsyncCompute} sequentially,
 * *assuming* the structural half — that the safe (pure-value) tasks complete and don't interfere. Lincheck checks
 * that assumption on the real bytecode. Because async runs on its own executor (not threads Lincheck's *managed*
 * strategy controls), this uses the **stress** strategy — many real concurrent executions — which is the right tool
 * for code with genuine internal parallelism: each operation fans out real tasks, and a deterministic result across
 * every interleaving is the linearizability witness.
 */
@CompileStatic
@POJO
class AsyncLincheckTest {

    /** Each call fans out three real parallel tasks and gathers them; the safe pattern is deterministic → 9. */
    @CompileStatic
    @POJO
    static class SafeGather {
        @Operation int gather() { AsyncCompute.safeGather(1, 2, 3) }
    }

    @Test
    void safeGatherIsDeterministic() {
        new StressOptions()
                .iterations(20)
                .threads(3)
                .actorsPerThread(2)
                .check(SafeGather)
    }

    /** The UNSAFE pattern the async docs warn against — async tasks mutating shared state. The three tasks
     *  read-modify-write {@code shared} with no synchronisation, so updates are lost and {@code bump} returns a value
     *  no sequential history explains. This is exactly the case groovy-verify's *safe-value* discipline excludes;
     *  Lincheck catches it. (Verus' HumanEval suite checks only overflow; here the race is the bug.) */
    @CompileStatic
    @POJO
    static class RacyGather {
        private int shared = 0
        @Operation
        int bump() {
            def t1 = async { shared = shared + 1; (Integer) 0 }
            def t2 = async { shared = shared + 1; (Integer) 0 }
            def t3 = async { shared = shared + 1; (Integer) 0 }
            await(t1, t2, t3)
            return shared
        }
    }

    @Test
    void racyBumpIsCaught() {
        // The unsynchronised shared mutation loses updates → a history no sequential order explains. Lincheck reports
        // a non-linearizable execution (an AssertionError) — the runtime confirmation that the safe discipline matters.
        assertThrows(AssertionError) {
            new StressOptions()
                    .iterations(50)
                    .threads(3)
                    .actorsPerThread(3)
                    .check(RacyGather)
        }
    }
}
