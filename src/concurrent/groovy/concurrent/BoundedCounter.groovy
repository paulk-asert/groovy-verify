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
import groovy.contracts.Invariant

/**
 * A <b>check-then-act</b> bounded counter — the sharpest illustration of the rung-1 boundary. The body is
 * <i>sequentially</i> bulletproof: {@code if (count &lt; 1) count = count + 1} can only ever leave {@code count}
 * at 0 or 1, and groovy-verify <b>proves</b> exactly that — the {@code @Invariant({ count &lt;= 1 })} is preserved
 * by {@code tryIncrement} (drop the bound to {@code &lt;= 0} and it refutes). So this is not a hand-wave that it
 * "looks correct"; it is a machine-checked sequential fact.
 *
 * <p>And yet it is <b>not thread-safe</b>: two threads can both read {@code count == 0}, both pass the guard, and
 * both increment — leaving {@code count == 2}, violating the very invariant the checker proved. That is not
 * unsoundness: groovy-verify reasons <i>above</i> the memory model (rung 1), so the invariant it proves is a
 * <i>per-thread</i> property; whether it composes into a concurrent guarantee is the structural rung's question.
 * The check-then-act doesn't compose (the read and the write aren't atomic), and {@code BoundedCounterJCStress}
 * catches the {@code count == 2} outcome empirically. The fix — atomicity (a lock or a CAS) — restores composition;
 * see {@link SafeBoundedCounter}, whose body the checker proves with the <i>identical</i> {@code @Invariant} (the
 * lock is transparent to it), so only the rung tells the two apart. The companion to {@link SpscBuffer}: there the
 * thread-local proof composes (given the lock); here it doesn't, and rung 3 is why you can tell.
 */
@CompileStatic
@POJO
@Invariant({ count <= 1 })
class BoundedCounter {
    int count = 0

    /** Check-then-act: sequentially preserves {@code count <= 1}, but the read and the write are not atomic. */
    void tryIncrement() {
        if (count < 1) count = count + 1
    }
}
