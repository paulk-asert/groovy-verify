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
 * A <b>String-valued</b> precondition — the Java-friendly twin of groovy-contracts'
 * {@code @Requires({ … })}. The condition is a Groovy boolean expression written as a {@code String}
 * ({@code @Requires('x >= 0')}) rather than a closure, which matters for <i>Java source</i>: a closure
 * literal is not a legal Java annotation value (javac rejects {@code @Requires({ x > 0 })} — "annotation
 * value not of an allowable type"), but a {@code String} constant is. So a {@code .java} file can carry
 * these contracts, be compiled by {@code javac} (the annotation is inert metadata there), and be verified
 * separately by compiling the same source as Groovy under {@code VerifyChecker}.
 *
 * <p>The {@code ContractExpansionTransform} captures the {@code String} verbatim and feeds it into exactly
 * the same reparse → encode → prove pipeline as a captured closure, so the expression is parsed with
 * <b>Groovy</b> semantics (a {@code ==} is value-equality, a {@code /} is {@code BigDecimal} division). It
 * reaches loop-free and recursive methods; loop invariants stay out of scope because Java forbids
 * annotating a statement (so there is nowhere to hang a per-loop {@code @Invariant}).
 */
@Retention(RetentionPolicy.RUNTIME)
@Target([ElementType.METHOD, ElementType.CONSTRUCTOR])
@Documented
@interface Requires {
    String value()
}
