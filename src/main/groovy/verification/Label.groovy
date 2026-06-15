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
 * Phase L1 — a static security classification for a parameter, method result, or field, drawn from a
 * user-defined security lattice (the {@code enum} the class's {@code leq}/{@code join}/{@code meet} pure
 * functions range over — see the {@code PL0 lattice} cases). {@code @Label('High')} on a parameter names
 * the security level of the data it carries; {@code @Label('Low')} on a method declares the classification
 * of its result (a sink).
 *
 * <p>Given these labels, the verifier discharges the noninterference (no-leak) obligation of an
 * information-flow analysis: for each {@code return e}, the security level of {@code e}
 * ({@code ΓE(e) = ⊔_v meet(Γ_v, L_v)} over the labelled sources flowing into it) must not exceed the
 * result's classification — {@code leq(ΓE(e), L(result))} — proved at compile time by the same Z3 backend
 * that discharges the contracts. A high value reaching a low result refutes with an "information leak"
 * diagnostic naming the offending return.
 *
 * <p>This is the static-label core (Slice 1) of the approach in Smith, <i>A Dafny-based approach to
 * thread-local information flow analysis</i>, §III. Value-dependent classifications, control variables,
 * array element labels, and declassification are later slices; an unlabelled or unsupported source skips
 * loudly rather than passing silently.
 *
 * <p>The {@code value} is the name of a constant of the lattice enum (e.g. {@code 'Low'} / {@code 'High'}).
 */
@Retention(RetentionPolicy.RUNTIME)
@Target([ElementType.PARAMETER, ElementType.METHOD, ElementType.FIELD])
@Documented
@interface Label {
    String value()
}
