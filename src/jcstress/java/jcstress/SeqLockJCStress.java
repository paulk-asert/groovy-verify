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

import concurrent.SeqLock;
import concurrent.SeqLockLeaky;
import java.util.List;
import org.openjdk.jcstress.annotations.Actor;
import org.openjdk.jcstress.annotations.JCStressTest;
import org.openjdk.jcstress.annotations.Outcome;
import org.openjdk.jcstress.annotations.State;
import org.openjdk.jcstress.infra.results.II_Result;

import static org.openjdk.jcstress.annotations.Expect.ACCEPTABLE;
import static org.openjdk.jcstress.annotations.Expect.ACCEPTABLE_INTERESTING;
import static org.openjdk.jcstress.annotations.Expect.FORBIDDEN;

/**
 * jcstress on the <b>seqlock</b> — the <em>torn read</em> bug class, the read-side mirror of {@link SpscBufferJCStress}'s
 * publication race. The third rung of the seqlock story (see {@code CONCURRENCY.md}): groovy-verify (rung 1) proves a
 * successful {@code tryRead} returns a consistent snapshot; Lincheck (rung 3a) model-checks the operations for
 * linearizability; jcstress is the <strong>empirical stress</strong> rung — it runs a writer and a reader billions of
 * times across real JIT/hardware and tallies the {@code (x, y)} pair the reader observed, on the <em>same</em> Groovy
 * {@code @CompileStatic @POJO} {@link SeqLock} the other rungs use. Inspired by jcstress's own samples (we wrote our
 * own; theirs is GPL).
 *
 * <p>One actor writes the record {@code (1, 1)}; the other reads the two halves. The record's default is {@code (0, 0)},
 * so the observed pair separates the worlds:
 * <ul>
 *   <li>{@code 0, 0} — the reader ran before the write committed.</li>
 *   <li>{@code 1, 1} — the reader saw the fully published, consistent record.</li>
 *   <li>{@code -1, -1} — (correct only) the read was contended, so the validating {@code tryRead} returned
 *       {@code null}; a real reader would retry.</li>
 *   <li>{@code 1, 0} / {@code 0, 1} — <strong>THE TORN READ</strong>: the reader saw one half of the new record and
 *       one half of the old. The correct seqlock's parity-and-unchanged guard rejects any snapshot taken during a
 *       write, so this is <strong>forbidden</strong>; the leaky reader skips that guard, so jcstress
 *       <strong>observes</strong> it.</li>
 * </ul>
 */
public class SeqLockJCStress {

    /** Correct: tryRead validates the sequence, so a torn pair is forbidden — and never observed. */
    @JCStressTest
    @State
    @Outcome(id = "0, 0", expect = ACCEPTABLE, desc = "Reader ran before the write committed.")
    @Outcome(id = "1, 1", expect = ACCEPTABLE, desc = "Reader saw the fully published, consistent record.")
    @Outcome(id = "-1, -1", expect = ACCEPTABLE, desc = "Contended — the validating tryRead returned null (a real reader retries).")
    @Outcome(expect = FORBIDDEN, desc = "A torn read (x != y) — impossible for the validating seqlock.")
    public static class Correct {
        final SeqLock sl = new SeqLock();

        @Actor
        public void writer() {
            sl.write(1);
        }

        @Actor
        public void reader(II_Result r) {
            List<Integer> snap = sl.tryRead();
            if (snap == null) { r.r1 = -1; r.r2 = -1; }
            else { r.r1 = snap.get(0); r.r2 = snap.get(1); }
        }
    }

    /** Leaky: tryRead skips the sequence guard, so jcstress catches the torn {@code 1, 0} / {@code 0, 1} pairs
     *  (marked INTERESTING so the demo run stays green while reporting the race was observed). */
    @JCStressTest
    @State
    @Outcome(id = "0, 0", expect = ACCEPTABLE, desc = "Reader ran before the write committed.")
    @Outcome(id = "1, 1", expect = ACCEPTABLE, desc = "Reader saw the fully published, consistent record.")
    @Outcome(id = "1, 0", expect = ACCEPTABLE_INTERESTING, desc = "THE TORN READ: saw the new x but the old y.")
    @Outcome(id = "0, 1", expect = ACCEPTABLE_INTERESTING, desc = "THE TORN READ: saw the old x but the new y.")
    public static class Leaky {
        final SeqLockLeaky sl = new SeqLockLeaky();

        @Actor
        public void writer() {
            sl.write(1);
        }

        @Actor
        public void reader(II_Result r) {
            List<Integer> snap = sl.tryRead();
            r.r1 = snap.get(0);
            r.r2 = snap.get(1);
        }
    }
}
