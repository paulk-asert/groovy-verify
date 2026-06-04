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
 * RUNTIME-retained carrier for the verbatim source text of a class's
 * {@code groovy.contracts.@Invariant} object invariants (Phase 15a).
 *
 * The class-level companion of {@link ContractSource}: users write plain
 * {@code @groovy.contracts.Invariant} on the class, get the runtime
 * before/after-method checks groovy-contracts generates as usual, and
 * {@link ContractExpansionTransform} (CONVERSION phase) captures each
 * invariant closure's verbatim source here. {@code VerifyChecker} reads
 * the text back and re-parses it, the same way it handles method-level
 * pre/postconditions.
 *
 * The annotation is a separate carrier rather than an extension of
 * {@link ContractSource} because the latter targets METHOD/CONSTRUCTOR
 * and broadening its target would conflate per-method and per-class state.
 *
 * Multiple invariants per class are supported (groovy-contracts'
 * {@code @Invariant} is {@code @Repeatable}); each invariant's text
 * appears as one element of {@link #invariants()} and the conjunction
 * is the class invariant.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.TYPE)
@Documented
@interface ClassInvariantSource {
    /** Verbatim class-invariant texts (logically AND'd); empty if none. */
    String[] invariants() default []
}
