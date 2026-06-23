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
 * A <b>String-valued</b> termination measure for a <i>recursive method</i> — the Java-friendly twin of a
 * method-level groovy-contracts {@code @Decreases({ … })}. The measure is a Groovy integer expression written
 * as a {@code String} ({@code @Decreases('n')}); it must be {@code >= 0} and strictly decrease at each
 * recursive call, which lets the method's own {@code @Ensures} be assumed at the recursive call (proof by
 * induction). Being a {@code String} it is a legal Java annotation value (see {@link Requires}).
 *
 * <p>This is the method-level (recursion) form only. A <i>loop</i>'s {@code @Decreases} is a statement
 * annotation, which Java does not permit — so iterative termination stays out of the Java-source path.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target([ElementType.METHOD, ElementType.CONSTRUCTOR])
@Documented
@interface Decreases {
    String value()
}
