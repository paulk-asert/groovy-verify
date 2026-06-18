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
import org.jetbrains.kotlinx.lincheck.LinChecker
import org.jetbrains.kotlinx.lincheck.annotations.Operation
import org.jetbrains.kotlinx.lincheck.strategy.managed.modelchecking.ModelCheckingOptions
import org.junit.jupiter.api.Test

import static org.junit.jupiter.api.Assertions.assertThrows

/**
 * Lincheck on the README locks example — the MUTUAL-EXCLUSION / race half of what that section's checker
 * proof assumes, across three accounts that together make "logic ⊥ concurrency" concrete (the same matrix as
 * bmc4j's coroutines-and-Lincheck example, on synchronized Groovy):
 *
 * <pre>
 *   account             logic (groovy-verify, rung 1)   thread-safe (Lincheck, here)
 *   RacyAccount         ✓ proven                        ✗ race — lost update / overdraw
 *   OverdraftAccount    ✗ refuted (overdraws)           ✓ linearizable (synchronized ⇒ atomic)
 *   Account (Safe)      ✓ proven                        ✓ linearizable
 * </pre>
 *
 * Each tool is blind to the other's column — {@link OverdraftAccount} passes Lincheck on wrong logic, and
 * {@link RacyAccount} verifies in the checker while racing. Concurrency contract: any operation on any thread
 * (a monitor admits arbitrary concurrent callers), so no {@code nonParallelGroup} here — unlike the SPSC
 * buffer. (Deadlock / lock-ordering — the OTHER half this section disclaims — is the Fray spike.)
 */
class AccountLincheckTest {

    @CompileStatic
    @POJO
    static class Correct {
        private final Account a = new Account(5)
        @Operation void deposit(int amount) { a.deposit(amount) }
        @Operation boolean withdraw(int amount) { a.withdraw(amount) }
        @Operation int balance() { a.balance() }
    }

    @CompileStatic
    @POJO
    static class Racy {
        private final RacyAccount a = new RacyAccount(5)
        @Operation void deposit(int amount) { a.deposit(amount) }
        @Operation boolean withdraw(int amount) { a.withdraw(amount) }
        @Operation int balance() { a.balance() }
    }

    @CompileStatic
    @POJO
    static class Overdraft {
        private final OverdraftAccount a = new OverdraftAccount(5)
        @Operation void deposit(int amount) { a.deposit(amount) }
        @Operation boolean withdraw(int amount) { a.withdraw(amount) }
        @Operation int balance() { a.balance() }
    }

    private static ModelCheckingOptions opts() {
        new ModelCheckingOptions()
                .iterations(50)
                .threads(2)
                .actorsPerThread(3)
                .actorsBefore(1)
                .actorsAfter(1)
    }

    @Test
    void lockedAccountIsLinearizable() {
        LinChecker.check(Correct, opts())        // mutual exclusion holds -> every history linearizes
    }

    @Test
    void racyAccountIsCaught() {
        // No lock -> a read-modify-write race; Lincheck finds a history no sequential order explains.
        assertThrows(AssertionError) { LinChecker.check(Racy, opts()) }
    }

    @Test
    void overdraftAccountIsLinearizableDespiteWrongLogic() {
        // Synchronized -> every history linearizes, so Lincheck PASSES — even though `withdraw` overdraws past
        // `balance >= 0`. Lincheck checks concurrency against the code's OWN sequential behaviour, so it is blind
        // to the logic bug. groovy-verify's monitor-invariant proof (rung 1) refutes exactly this shape — the
        // "unguarded withdraw breaks the lock invariant" case. Logic ⊥ concurrency, each tool sees one column.
        LinChecker.check(Overdraft, opts())
    }
}
