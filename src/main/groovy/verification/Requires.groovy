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
import org.codehaus.groovy.transform.GroovyASTTransformationClass

/**
 * Hoare-logic precondition. The annotated method may only be called
 * in contexts where the closure body — evaluated over the formal
 * parameters of the method and the actual arguments at the call site —
 * is provably true under {@link VerifyChecker}'s fragment:
 * linear integer arithmetic, equality/inequality, and boolean ops.
 *
 * <pre>
 *   {@code @Requires}({ x >= 0 })
 *   static int isqrt(int x) { ... }
 * </pre>
 *
 * Why a bespoke annotation rather than {@code groovy.contracts.Requires}?
 * groovy-contracts compiles its closure into a generated class — great
 * for the runtime check it performs, but the closure body's source is
 * gone by the time a consumer's type checker sees the method. This
 * annotation's {@code contract} string member is populated at producer-
 * compile-time by {@link RequiresTransformation}: it captures the
 * closure body's source text so the contract crosses the compile
 * boundary in re-parseable form, which is exactly what the SMT-backed
 * checker needs.
 *
 * Anything outside the fragment yields a "skipped: outside fragment"
 * warning rather than a silent pass, in the spirit of OpenJML's ESC
 * mode and Dafny's verifier.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target([ElementType.METHOD, ElementType.CONSTRUCTOR])
@Documented
@GroovyASTTransformationClass(['verification.RequiresTransformation'])
@interface Requires {
    /** The contract as a Groovy closure literal. Becomes a synthetic class. */
    Class value()
    /** Populated by RequiresTransformation with the closure body's source text. */
    String contract() default ""
}
