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
 * Hoare-logic postcondition. The annotated method must, on every
 * return path, leave its result satisfying the closure body — proven
 * under {@link VerifyChecker}'s fragment (linear integer arithmetic,
 * comparisons, booleans). The closure may use the special name
 * {@code result}, which {@link VerifyChecker} binds to the returned
 * expression on each path.
 *
 * <pre>
 *   {@code @Ensures}({ result >= a && result >= b })
 *   static int max(int a, int b) { if (a > b) a else b }
 * </pre>
 *
 * Unlike {@link Requires} (checked at the caller), a postcondition is
 * checked against the method's *own body*, so the declaring class must
 * be compiled under
 * {@code @TypeChecked(extensions = 'verification.VerifyChecker')}.
 *
 * Because that body is `@TypeChecked`, the static checker would
 * otherwise reject the names inside the contract closure as undeclared.
 * {@link EnsuresTransformation} captures the closure's source text into
 * the {@code contract} member at SEMANTIC_ANALYSIS and replaces the
 * closure value with a harmless class literal, so type checking never
 * sees the closure.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target([ElementType.METHOD])
@Documented
@GroovyASTTransformationClass(['verification.EnsuresTransformation'])
@interface Ensures {
    /** The contract as a Groovy closure literal. Neutralised after text capture. */
    Class value()
    /** Populated by EnsuresTransformation with the closure body's source text. */
    String contract() default ""
}
