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
}
