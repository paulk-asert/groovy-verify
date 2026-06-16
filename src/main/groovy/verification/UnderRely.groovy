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
 * Declares that a method's body runs <b>under one or more rely-steps</b> — the *declarative* form of a
 * hand-written rely-step call, as {@code @WithWriteLock} is to a manual {@code lock()}. Each named method is a
 * <i>rely-step</i>: an (empty-bodied) method carrying {@code @Modifies} (the shared frame the environment may
 * change) and {@code @Ensures} over {@code old} (the relation it promises — the neighbour thread's
 * {@code @Guarantee}). The {@code ContractExpansionTransform} prepends a call to each named rely-step at the start
 * of the body, so the verifier's caller-side framing havocs the shared frame and assumes the rely — exactly as if
 * the call were written by hand — while the body stays pure logic.
 *
 * <p>So instead of opening each method with {@code relyOnWriter()}, the developer declares the rely once (as a
 * rely-step method) and tags the consuming methods:
 * <pre>
 *   {@literal @}Requires({ head &lt; tail })
 *   {@literal @}UnderRely('relyOnWriter')
 *   int read() { int v = values[head]; head = head + 1; return v }
 * </pre>
 *
 * <p><b>Soundness scope.</b> A single rely-step is prepended at body entry, which models the method as an
 * <i>atomic critical section</i> that runs after one environment step — the same atomicity assumption the lock /
 * actor examples already make. It is the developer's responsibility to apply {@code @UnderRely} only to such
 * critical sections; a long method with several independent shared interactions would need a rely-step before
 * each (a later slice), not just one at entry.
 *
 * <p>Prototype (this project): the transform inserts the call; it does not yet <i>synthesise</i> the rely-step
 * method from a {@code @Rely} predicate (so the rely is still written once, as a contract-only method).
 */
@Retention(RetentionPolicy.RUNTIME)
@Target([ElementType.METHOD])
@Documented
@interface UnderRely {
    /** The name(s) of the rely-step method(s) to call at the start of the body, in order. */
    String[] value()
}
