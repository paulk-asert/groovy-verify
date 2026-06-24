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

import concurrent.SpscBuffer;
import concurrent.SpscBufferLeaky;
import org.openjdk.jcstress.annotations.Actor;
import org.openjdk.jcstress.annotations.JCStressTest;
import org.openjdk.jcstress.annotations.Outcome;
import org.openjdk.jcstress.annotations.State;
import org.openjdk.jcstress.infra.results.I_Result;

import static org.openjdk.jcstress.annotations.Expect.ACCEPTABLE;
import static org.openjdk.jcstress.annotations.Expect.ACCEPTABLE_INTERESTING;
import static org.openjdk.jcstress.annotations.Expect.FORBIDDEN;

/**
 * jcstress on the SPSC buffer — the <em>memory-model publication</em> grain none of the other rungs reach.
 * groovy-verify (rung 1) proves the buffer's {@code @Invariant} thread-locally; Lincheck (rung 3) model-checks the
 * operations for linearizability; Fray drives the scheduler for deadlock. jcstress is the <strong>empirical
 * stress</strong> rung: it runs the two actors billions of times across real JIT/hardware and tallies which
 * <em>outcomes</em> occur — the canonical Java-Memory-Model test, here on the <em>same</em> Groovy {@code @CompileStatic}
 * {@code @POJO} buffer ({@link SpscBuffer}). Inspired by jcstress's own samples (we wrote our own; theirs is GPL),
 * named after the {@code Correct}/{@code Leaky} pair from {@code BufferLincheckTest}.
 *
 * <p>The actors are a producer offering {@code 1} and a consumer polling. The slot's array default is {@code 0},
 * so the observed value separates three worlds:
 * <ul>
 *   <li>{@code -1} — the consumer ran first; the buffer was empty.</li>
 *   <li>{@code 1}  — the consumer saw the fully published value.</li>
 *   <li>{@code 0}  — the consumer saw {@code tail} advanced but read the slot <em>before the value was written</em>:
 *       the publication race. The correct buffer writes the slot then publishes via the {@code volatile tail}, so
 *       {@code 0} is <strong>impossible</strong>; the leaky one publishes first, so jcstress <strong>observes</strong> it.</li>
 * </ul>
 */
public class SpscBufferJCStress {

    /** Correct: write the value, THEN publish ({@code tail++}). {@code 0} is forbidden — and never observed. */
    @JCStressTest
    @State
    @Outcome(id = "-1", expect = ACCEPTABLE, desc = "Consumer ran first — buffer empty.")
    @Outcome(id = "1", expect = ACCEPTABLE, desc = "Consumer saw the fully published value.")
    @Outcome(id = "0", expect = FORBIDDEN, desc = "Publication race — impossible for the correct buffer (volatile publish after write).")
    public static class Correct {
        final SpscBuffer buffer = new SpscBuffer(1);

        @Actor
        public void producer() {
            buffer.offer(1);
        }

        @Actor
        public void consumer(I_Result r) {
            Integer v = buffer.poll();
            r.r1 = (v == null) ? -1 : v;
        }
    }

    /** Leaky: publish ({@code tail++}) BEFORE writing the slot. jcstress catches the {@code 0} leak (marked
     *  INTERESTING so the demo run stays green while reporting the race was observed). */
    @JCStressTest
    @State
    @Outcome(id = "-1", expect = ACCEPTABLE, desc = "Consumer ran first — buffer empty.")
    @Outcome(id = "1", expect = ACCEPTABLE, desc = "Consumer saw the fully published value.")
    @Outcome(id = "0", expect = ACCEPTABLE_INTERESTING, desc = "THE LEAK: tail advanced before the slot was written; the consumer read the un-written default 0.")
    public static class Leaky {
        final SpscBufferLeaky buffer = new SpscBufferLeaky(1);

        @Actor
        public void producer() {
            buffer.offer(1);
        }

        @Actor
        public void consumer(I_Result r) {
            Integer v = buffer.poll();
            r.r1 = (v == null) ? -1 : v;
        }
    }
}
