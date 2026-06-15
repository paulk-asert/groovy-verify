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

/**
 * Phase L1 — an explicit <b>declassification</b> point: the controlled release of classified information
 * (Smith §III-E). {@code Declassify.to('Low', expr)} marks {@code expr} as released at security level
 * {@code 'Low'} (a constant of the program's lattice), so the information-flow analysis treats the marked
 * expression as that level regardless of the secrets it draws on. A password checker returning
 * {@code Declassify.to('Low', password == guess)} releases the single equality bit — permitted — while the same
 * method returning {@code password} (or the equality without the marker) refutes.
 *
 * <p>This is the unconditional ("predicate true") form of the paper's mechanism, in the spirit of Mantel &amp;
 * Sands: every release is <b>explicit and localized</b> — you can grep for {@code Declassify.to} and audit every
 * point where classified information leaves the lattice — which is the whole point versus an invisible
 * {@code @untainted}-style cast. The <i>predicate-gated</i> form (a two-state predicate relating the released
 * value to the program's initial state, so only the specified function of the secret may escape) needs
 * {@code old}-state tracking and is a later slice.
 *
 * <p>At runtime the call is the identity on its value, so it does not change program behaviour.
 */
class Declassify {
    /** Release {@code value} at security level {@code level} (a lattice constant name). Identity at runtime. */
    static <T> T to(String level, T value) { value }
}
