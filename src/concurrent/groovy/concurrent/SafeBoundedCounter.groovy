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
import groovy.transform.WithWriteLock
import groovy.transform.stc.POJO
import groovy.contracts.Invariant

/**
 * The fix for {@link BoundedCounter}'s check-then-act race: {@code @WithWriteLock} makes {@code tryIncrement}
 * mutually exclusive, so the read and the write are one atomic step and {@code count == 2} can never occur.
 *
 * <p>The point of the pairing: groovy-verify proves the <b>same</b> {@code @Invariant({ count &lt;= 1 })} for this
 * class as for the racy one — the lock transform is captured at {@code CONVERSION}, before the lock is woven in, so
 * the checker sees the identical body and reasons above the memory model either way. <b>The proof cannot tell the
 * safe version from the broken one</b> — only the structural rung can: {@code BoundedCounterJCStress} observes
 * {@code count == 2} on {@link BoundedCounter} and never on this one. That is the rung-1 boundary in one example.
 */
@CompileStatic
@POJO
@Invariant({ count <= 1 })
class SafeBoundedCounter {
    int count = 0

    @WithWriteLock
    void tryIncrement() {
        if (count < 1) count = count + 1
    }
}
