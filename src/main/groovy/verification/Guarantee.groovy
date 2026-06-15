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
 * Phase L1 (rely/guarantee well-formedness) — marks a pure boolean method as a thread's <b>guarantee</b>
 * condition: a two-state predicate over the shared state, constraining how <i>this</i> thread may change it on
 * each of its own steps (Smith §IV). {@code value} names the thread. The two states are the parameters split in
 * half (pre-state, then post-state), exactly as for {@link Rely}.
 *
 * <p>The verifier discharges the compatibility obligations a guarantee participates in: it must be reflexive,
 * and it must imply every <i>other</i> thread's rely ({@code G_i ⟹ R_j}, {@code i ≠ j}). See {@link Rely} for the
 * full picture and the honest scope (this checks the rely/guarantee <i>conditions</i> are well-formed and
 * compatible, not that the threads' code respects them).
 */
@Retention(RetentionPolicy.RUNTIME)
@Target([ElementType.METHOD])
@Documented
@interface Guarantee {
    /** The thread this guarantee condition belongs to. */
    String value()
}
