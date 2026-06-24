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

import concurrent.AtomicBoundedCounter;
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
 * jcstress on the <b>AtomicInteger</b> check-then-act counter — the "but I used an atomic class!" variant of
 * {@link BoundedCounterJCStress}. Each step ({@code get()}, {@code incrementAndGet()}) is atomic, yet
 * {@link AtomicBoundedCounter#tryIncrement() tryIncrement} composes two of them with a gap, so two actors can both
 * read 0, both pass the guard, and both increment — {@code count == 2}. jcstress runs the actors billions of times
 * and tallies the final value.
 *
 * <p>Unlike the plain-{@code int} pair, groovy-verify cannot prove (or refute) a bound here — an
 * {@code AtomicInteger} is outside its modelled fragment, so it loud-skips. This rung is therefore the <em>only</em>
 * witness for this counter: {@code Racy} produces {@code 2}, and the single-CAS {@code Safe} never does. The fix is
 * one atomic transition ({@code compareAndSet}), not a second atomic operation. Inspired by jcstress's own
 * check-then-act samples; the code (and the Groovy domain) is our own.
 */
public class AtomicBoundedCounterJCStress {

    /** Check-then-act over AtomicInteger: two atomic ops, non-atomic pair → two threads can both reach 2. */
    @JCStressTest
    @State
    @Outcome(id = "1", expect = ACCEPTABLE, desc = "One increment won, the other saw count == 1 and skipped.")
    @Outcome(id = "2", expect = ACCEPTABLE_INTERESTING, desc = "THE RACE: both read 0, both passed the guard, both incremented.")
    public static class Racy {
        final AtomicBoundedCounter counter = new AtomicBoundedCounter();

        @Actor public void actor1() { counter.tryIncrement(); }
        @Actor public void actor2() { counter.tryIncrement(); }
        @Arbiter public void arbiter(I_Result r) { r.r1 = counter.get(); }
    }

    /** Single-CAS increment: the check and the act are one atomic transition, so count == 2 is impossible. */
    @JCStressTest
    @State
    @Outcome(id = "1", expect = ACCEPTABLE, desc = "One CAS won the 0→1 transition, the other saw count == 1 and stopped.")
    @Outcome(id = "2", expect = FORBIDDEN, desc = "count == 2 would mean both CASes from 0 succeeded — impossible.")
    public static class Safe {
        final AtomicBoundedCounter counter = new AtomicBoundedCounter();

        @Actor public void actor1() { counter.casIncrement(); }
        @Actor public void actor2() { counter.casIncrement(); }
        @Arbiter public void arbiter(I_Result r) { r.r1 = counter.get(); }
    }
}
