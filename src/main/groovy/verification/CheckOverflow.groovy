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
 * Phase 44 — opt-in marker that turns on **32-bit integer overflow checks** for the annotated
 * method (or every method of the annotated class). Each binary {@code +}, {@code -}, {@code *}
 * on Int-sorted operands becomes an implicit obligation alongside the existing bounds /
 * divide-by-zero / null-deref checks: the operation's mathematical result must satisfy
 * {@code Integer.MIN_VALUE <= result <= Integer.MAX_VALUE}, otherwise the build refutes with a
 * concrete failing input.
 *
 * <p>The encoder still uses Z3's mathematical {@code Int} sort to represent values — the
 * overflow check is an *additional* obligation discharged in the same site/replay machinery as
 * bounds and null. So a method without {@code @CheckOverflow} behaves exactly as before
 * (math-int reasoning, current test suite); a method with it gets Verus-style precision over the
 * machine-integer interpretation, but without forcing the typed-narrow ergonomic Verus relies
 * on.
 *
 * <p>Annotating a class enables the check for every method of that class (including
 * constructors); a method-level annotation overrides individual methods.
 *
 * <p>Sub-expressions are checked individually: {@code (a + b) * c} emits three obligations —
 * one for {@code a + b}, one for the outer product, and one for any further composition.
 *
 * <p>Practical guidance: a {@code for (int i = 0; i < n; i++)} loop under {@code @CheckOverflow}
 * will refute on the {@code i++} unless {@code @Requires({ n < Integer.MAX_VALUE })} bounds
 * {@code n}. This is the inherent tax of machine-integer precision; the trade-off is detection
 * of real overflow bugs in arithmetic-heavy code.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target([ElementType.METHOD, ElementType.CONSTRUCTOR, ElementType.TYPE])
@Documented
@interface CheckOverflow {
}
