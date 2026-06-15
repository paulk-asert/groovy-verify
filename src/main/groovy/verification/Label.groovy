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
 *
 * <p><b>Value-dependent classification.</b> Instead of a constant level, a parameter may carry
 * {@code @Label(by = 'm')}, naming a pure classification method {@code m(…)} that returns the lattice level
 * <i>as a function of program state</i> (Smith §III-A — the {@code L_x()} of the paper). The method's parameters
 * are matched by name to the variables in scope at the use site, so {@code L classifyData(boolean authed) }
 * {@code { authed ? L.Low : L.High }} makes {@code data}'s classification depend on the {@code authed} control
 * variable. The no-leak obligation is then discharged <i>under the path conditions</i>: {@code if (authed) }
 * {@code return data} verifies (there {@code authed} holds, so {@code L(data) == Low}), while an unguarded
 * {@code return data} refutes. This is the capability dataflow taint cannot express — a classification that
 * evolves with the state — and it falls out of the same SMT backend.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target([ElementType.PARAMETER, ElementType.METHOD, ElementType.FIELD])
@Documented
@interface Label {
    /** A constant lattice level name (e.g. {@code 'Low'}); empty when {@link #by} is used. */
    String value() default ''
    /** The name of a pure classification method giving a value-dependent level; empty for a constant {@link #value}. */
    String by() default ''
}
