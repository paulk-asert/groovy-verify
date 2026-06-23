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
 * A <b>String-valued</b> postcondition — the Java-friendly twin of groovy-contracts' {@code @Ensures({ … })}.
 * The condition is a Groovy boolean expression written as a {@code String} ({@code @Ensures('result == n')}),
 * over {@code result} and the parameters, so it is a legal Java annotation value and can ride on a
 * {@code .java} file (see {@link Requires} for the full rationale). Captured verbatim and verified under
 * Groovy semantics through the usual {@code ContractExpansionTransform} pipeline.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target([ElementType.METHOD, ElementType.CONSTRUCTOR])
@Documented
@interface Ensures {
    String value()
}
