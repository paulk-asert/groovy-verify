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

import java.util.concurrent.atomic.AtomicInteger

/**
 * The check-then-act bounded counter expressed with {@link AtomicInteger} — the form the "but I reached for an
 * <i>atomic</i> class, so surely it's safe" intuition produces, and the form that shows the intuition is wrong.
 * Each individual operation is atomic; the <i>pair</i> is not. {@link #tryIncrement} reads with {@code get()} and,
 * if the value is below 1, bumps it with {@code incrementAndGet()} — two atomic steps with a gap between them.
 * Two threads can both observe 0 in that gap, both pass the guard, and both increment, leaving 2. Atomicity of the
 * parts does not buy atomicity of the whole; only folding check-and-act into one step does.
 *
 * <p><b>The verifier models the atomic as a wrapped int.</b> groovy-verify treats an {@code AtomicInteger} field as
 * an int <i>cell</i>: {@code count.get()} reads it, {@code count.incrementAndGet()} / {@code set} / {@code addAndGet}
 * / {@code compareAndSet} write it. So {@code @Invariant({ count.get() &lt;= 1 })} over {@link #tryIncrement} is
 * <b>proved</b> exactly as the plain-{@code int} {@link BoundedCounter}'s is (drop the bound to {@code &lt;= 0} and it
 * refutes) — atomicity is rung-1-transparent, so the <i>sequential</i> invariant is identical. That proof lives in the
 * {@code P-check-then-act} cases and {@code SpscBufferVerifyTest}.
 *
 * <p><b>Why this class carries no {@code @Invariant} annotation.</b> Not because the verifier can't reach the bound —
 * it can — but because {@link #casIncrement}'s retry {@code while} loop is outside the straight-line fragment the
 * checker models, so an annotation here would loud-skip on that method. The class therefore stands on the empirical
 * rung ({@code AtomicBoundedCounterJCStress}); the verifiable half of the very same get()/incrementAndGet() shape is
 * proved in the harness cases instead.
 *
 * <p>{@link #casIncrement} is the fix: a single {@code compareAndSet} folds the read and the write into one atomic
 * transition, retrying on contention, so the value never exceeds 1. jcstress observes {@code 2} from
 * {@code tryIncrement} and never from {@code casIncrement}.
 */
@CompileStatic
@POJO
class AtomicBoundedCounter {
    private final AtomicInteger count = new AtomicInteger(0)

    /** Check-then-act: two individually-atomic ops with a gap between — the read and the write don't compose. */
    void tryIncrement() {
        if (count.get() < 1) count.incrementAndGet()
    }

    /** The fix: one CAS folds check-and-act into a single atomic transition, retrying on contention; never exceeds 1. */
    boolean casIncrement() {
        while (true) {
            int current = count.get()
            if (current >= 1) return false                       // guard limit reached — leave it at 1
            if (count.compareAndSet(current, current + 1)) return true
        }
    }

    /** The live value, for the jcstress arbiter to tally. */
    int get() { count.get() }
}
