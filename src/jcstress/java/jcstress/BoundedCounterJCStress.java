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
package jcstress;

import concurrent.BoundedCounter;
import concurrent.SafeBoundedCounter;
import org.openjdk.jcstress.annotations.Actor;
import org.openjdk.jcstress.annotations.Arbiter;
import org.openjdk.jcstress.annotations.JCStressTest;
import org.openjdk.jcstress.annotations.Outcome;
import org.openjdk.jcstress.annotations.State;
import org.openjdk.jcstress.infra.results.I_Result;

import static org.openjdk.jcstress.annotations.Expect.ACCEPTABLE;
import static org.openjdk.jcstress.annotations.Expect.ACCEPTABLE_INTERESTING;
import static org.openjdk.jcstress.annotations.Expect.FORBIDDEN;

/**
 * jcstress on the <b>check-then-act</b> bounded counter — the empirical half of the rung-1 boundary that
 * groovy-verify proves the thread-local half of (the {@code P-check-then-act} cases). The body
 * {@code if (count < 1) count = count + 1} keeps {@code count <= 1} <em>sequentially</em> (the checker proves it),
 * yet two actors can both pass the guard and both increment — {@code count == 2}. jcstress runs the two actors
 * billions of times and tallies the final value.
 *
 * <p>The proof can't tell {@code Racy} from {@code Safe} — it proves the identical {@code @Invariant} for both
 * (the lock is transparent to it). Only this rung can: {@link BoundedCounter} produces {@code 2}, the
 * {@code @WithWriteLock} {@link SafeBoundedCounter} never does. Inspired by jcstress's own check-then-act samples;
 * the code (and the Groovy domain) is our own.
 */
public class BoundedCounterJCStress {

    /** The unguarded counter: two threads can both read 0 and both increment → 2 (the race jcstress catches). */
    @JCStressTest
    @State
    @Outcome(id = "1", expect = ACCEPTABLE, desc = "One increment won, the other saw count == 1 and skipped.")
    @Outcome(id = "2", expect = ACCEPTABLE_INTERESTING, desc = "THE RACE: both read 0, both passed the guard, both incremented.")
    public static class Racy {
        final BoundedCounter counter = new BoundedCounter();

        @Actor public void actor1() { counter.tryIncrement(); }
        @Actor public void actor2() { counter.tryIncrement(); }
        @Arbiter public void arbiter(I_Result r) { r.r1 = counter.getCount(); }
    }

    /** The @WithWriteLock counter: the check-then-act is one atomic step, so count == 2 is impossible. */
    @JCStressTest
    @State
    @Outcome(id = "1", expect = ACCEPTABLE, desc = "One increment won, the other saw count == 1 and skipped.")
    @Outcome(id = "2", expect = FORBIDDEN, desc = "count == 2 would mean the lock failed — never observed.")
    public static class Safe {
        final SafeBoundedCounter counter = new SafeBoundedCounter();

        @Actor public void actor1() { counter.tryIncrement(); }
        @Actor public void actor2() { counter.tryIncrement(); }
        @Arbiter public void arbiter(I_Result r) { r.r1 = counter.getCount(); }
    }
}
