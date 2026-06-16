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
 * Marks an <b>expression-bodied</b> method whose body <i>is</i> its postcondition — a *self-specifying*
 * declarative function (FizzBuzz's {@code spec}, an equational combiner like {@code add(a,b){a+b}}, a getter).
 * Writing {@code @Ensures({ result == E })} on a method {@code { E }} duplicates {@code E}; {@code @SelfEnsures}
 * lifts the body into exactly that postcondition, so it is written once.
 *
 * <p>Prototype (this project): the {@code ContractExpansionTransform} desugars {@code @SelfEnsures} into a
 * captured {@code @Ensures({ result == <body> })} at CONVERSION, so everything downstream — the postcondition
 * proof, the equational-combiner machinery that reads {@code result == E} — sees an ordinary ensures and needs no
 * special casing. The method must have a single-expression body ({@code { E }} or {@code { return E }}); anything
 * else is a loud error (there's no single expression to lift).
 *
 * <p>Honest note: when the body <i>is</i> the spec, proving {@code result == body} is <b>vacuous</b> — the real
 * assurance is the body's <i>totality</i> (its bounds/null/division obligations) and that the expression is in the
 * supported fragment, plus exporting the body as a contract callers and tools can read. {@code @SelfEnsures}
 * deliberately gives up the (weak) double-accounting of writing spec and body independently; reserve a separate
 * {@code @Ensures} for methods whose spec and implementation are genuinely different descriptions.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target([ElementType.METHOD])
@Documented
@interface SelfEnsures {
}
