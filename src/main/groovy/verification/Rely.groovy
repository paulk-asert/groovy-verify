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
package verification

import java.lang.annotation.Documented
import java.lang.annotation.ElementType
import java.lang.annotation.Retention
import java.lang.annotation.RetentionPolicy
import java.lang.annotation.Target

/**
 * Phase L1 (rely/guarantee well-formedness) — marks a pure boolean method as a thread's <b>rely</b> condition: a
 * two-state predicate over the shared state, constraining how the <i>environment</i> (other threads) may change
 * it between this thread's steps (Smith §IV). {@code value} names the thread.
 *
 * <p>The two states are the method's parameters split in half: the first half is the pre-state, the second half
 * the matching post-state. So {@code @Rely('Consumer') boolean rc(int oldHead, int oldTail, int head, int tail)}
 * {@code { head == oldHead && oldTail <= tail }} says the consumer relies on its environment not moving
 * {@code head} and only growing {@code tail}.
 *
 * <p>Given the relies and {@link Guarantee}s a class declares, the verifier discharges the
 * rely/guarantee <b>compatibility</b> obligations automatically (the paper's lemmas): each rely is reflexive and
 * transitive, each guarantee reflexive, and every thread's guarantee implies every <i>other</i> thread's rely
 * ({@code G_i ⟹ R_j}, {@code i ≠ j}) — the conditions under which the per-thread proofs compose. An incompatible
 * or ill-formed set refutes. This checks the rely/guarantee <i>conditions</i>; it does <b>not</b> prove the
 * threads' code respects them (the interleaving proof — havoc-under-rely between statements — is a non-goal).
 */
@Retention(RetentionPolicy.RUNTIME)
@Target([ElementType.METHOD])
@Documented
@interface Rely {
    /** The thread this rely condition belongs to. */
    String value()
}
