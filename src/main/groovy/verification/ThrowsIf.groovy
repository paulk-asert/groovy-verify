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
import java.lang.annotation.Repeatable
import java.lang.annotation.ElementType
import java.lang.annotation.Retention
import java.lang.annotation.RetentionPolicy
import java.lang.annotation.Target

/**
 * Phase 213/214 — an <b>exceptional contract</b> (prototype; the {@code verification}-owned reference
 * implementation ahead of an upstream groovy-contracts conversation — JML's {@code exceptional_behavior}
 * and SPARK's {@code Exceptional_Cases} are the prior art):
 *
 * <pre>
 *   {@literal @}ThrowsIf(value = { x == null }, exception = NullPointerException)
 *   {@literal @}ThrowsIf(value = { y == null }, exception = NullPointerException, woven = false)
 *   static def myMethod(x, y) { Objects.requireNonNull(y) }
 * </pre>
 *
 * asserts the method throws (an instance of) {@code exception} <b>exactly when</b> the condition holds
 * at entry. Three modes per instance ({@code @Repeatable} — multiple arms compose, JML-signals-style):
 * <ul>
 *   <li><b>{@code woven} (default)</b> — the guard-throw is <i>inserted</i> at method entry
 *       (generatively, Lombok-{@code @NonNull}-style; here by {@link ContractExpansionTransform} as the
 *       reference weaving until groovy-contracts adopts the annotation). Because the insertion happens
 *       before static type checking, the verifier simply proves the post-weave body — no special
 *       casing. Weaving requires an explicit {@code exception} type (it must be constructed).</li>
 *   <li><b>{@code woven = false}</b> — the body already implements the throw (a hand-written guard,
 *       an {@code Objects.requireNonNull}); nothing is inserted, and the verifier proves the full iff
 *       against the body: <i>must-throw</i> (no normal return while the condition holds) and
 *       <i>only-when</i> (no matching throw while it fails), refuting with concrete witnesses.</li>
 *   <li><b>{@code trusted = true}</b> — specification only (the throw originates in a third-party
 *       call): not woven, not proved — no skip-warning either; the condition still gets the vacuity
 *       check, call sites still assume the contract, and the runtime rung still monitors it
 *       reflectively (a declared throw under a true condition is a positive cross-validation;
 *       violations in either direction fail the run).</li>
 * </ul>
 *
 * <p>The condition is a groovy-contracts-style closure over the method's parameters
 * ({@code { x == null }}); the transform normalises it to a typed-parameter closure pre-STC, so the
 * bare spelling type-checks in every compile environment.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target([ElementType.METHOD])
@Repeatable(ThrowsIfConditions)
@Documented
@interface ThrowsIf {
    /** The entry-state condition — a closure over the method's parameters ({@code { n < 0 }}). */
    Class value()

    /** The exception (super)type thrown when the condition holds. Required for woven instances. */
    Class exception() default Throwable

    /** False when the body itself implements the guard-throw (nothing inserted; the iff is proved). */
    boolean woven() default true

    /** True for specification-only instances (documented third-party behaviour): not woven, not
     *  proved (and not warned about) — still assumed by callers and monitored by the runtime rung. */
    boolean trusted() default false

    /**
     * {@code true} (default): the arm-set is an <b>iff</b> — the listed conditions are the ONLY
     * reasons a matching exception is thrown, and the only-when direction is verified.
     * {@code false}: a one-directional (JML {@code signals}-style) arm — the condition is
     * <i>sufficient</i> for the throw but the set makes no exhaustiveness claim (the method may
     * throw the same exception for other, unlisted reasons). The must-throw direction is still
     * verified; the only-when check is skipped for the whole arm-set. This is what admits specs
     * like {@code Integer.parseInt} whose full throw condition is outside the fragment.
     *
     * <p><b>Consumption gating.</b> The two directions are consumed separately, and consumers gate on
     * the right one. <i>Survival facts</i> (a call the program moved past did not throw, so no arm's
     * condition held — Phase 222) use only the must-throw direction and are valid in both modes.
     * <i>Catch-block reasoning</i> ("caught E, therefore some matching arm's condition held" —
     * Phase 223) consumes the only-when / JML-{@code signals} direction and IS gated on the matching
     * arms being fully exhaustive: one {@code exhaustive = false} arm yields no catch fact.
     * Note also what neither mode claims in general: {@code @ThrowsIf} is exhaustive (at most) over
     * the <i>conditions for the types it mentions</i>, never over exception <i>types</i> — there is
     * no JML-{@code signals_only} claim on user methods, and an undeclared exception type is
     * unconstrained. And no claim, however exhaustive, reasons about VM resource conditions: an
     * {@code OutOfMemoryError} or {@code StackOverflowError} is outside contract semantics — the
     * verifier's model has no resource limits (its termination reasoning, {@code @Decreases}, is a
     * separate mechanism), and the runtime rung never judges a {@code VirtualMachineError} against
     * the arms. The ONE deliberate exception: catch-reachability reads a <b>registry
     * skeleton's</b> arm types as its complete throw-type story (the implicit {@code signals_only}
     * of an external spec — true of every shipped skeleton and monitored by the rung's spec-throw
     * category); a spec file that lists arms is read as the whole exceptional contract, type-wise.
     */
    boolean exhaustive() default true
}
