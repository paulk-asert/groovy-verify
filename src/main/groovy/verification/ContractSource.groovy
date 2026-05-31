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
 * RUNTIME-retained carrier for the verbatim source text of a method's
 * {@code groovy.contracts} preconditions/postconditions.
 *
 * Users write plain {@code @groovy.contracts.Requires}/{@code @Ensures}; they
 * get the runtime checks groovy-contracts generates as usual. Separately,
 * {@link ContractExpansionTransform} runs at {@code CONVERSION} — while the
 * contract closures are still present, before groovy-contracts erases them into
 * generated closure classes at {@code SEMANTIC_ANALYSIS} — captures each
 * closure's verbatim source and attaches it here.
 *
 * Why a separate RUNTIME annotation rather than reading the closure AST? The
 * closure body's source is gone from the compiled artifact: the built-in
 * contracts annotation only retains a {@code Class} reference to a generated
 * closure whose body is bytecode. A RUNTIME annotation member, by contrast,
 * survives into the class file and is readable from a decompiled
 * {@link org.codehaus.groovy.ast.ClassNode} at a downstream consumer's compile
 * time — which is exactly what {@link VerifyChecker} needs to discharge a
 * precondition at a cross-module call site.
 *
 * A single instance carries both kinds; either member may be empty.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target([ElementType.METHOD, ElementType.CONSTRUCTOR])
@Documented
@interface ContractSource {
    /** Verbatim precondition text, e.g. "x >= 0" (empty if none). */
    String requires() default ''
    /** Verbatim postcondition text, e.g. "result >= 0" (empty if none). */
    String ensures() default ''
}
