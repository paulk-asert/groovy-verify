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

import groovy.transform.CompileStatic

/**
 * The bounded-universal quantifier helper the verifier recognises in
 * {@code @Requires}/{@code @Ensures} contracts (roadmap Phase 6):
 *
 * <pre>
 *   {@literal @}Requires({ Forall.range(0, a.length) { i {@literal ->} a[i] >= 0 } })
 * </pre>
 *
 * The predicate is a one-argument closure binding the index; the bound variable
 * is whatever the closure names it. (This relies on the patched 6.0.0-SNAPSHOT
 * groovy-contracts, which allows a parameterised closure nested inside a contract
 * closure — earlier builds rejected both a declared parameter and {@code it}.)
 *
 * It stays executable so the groovy-contracts *runtime* check still works:
 * {@link #range} evaluates the predicate over the range. At compile time
 * {@code Encoder} recognises the {@code Forall.range(lo, hi, pred)} shape and
 * rewrites it to a Z3 {@code mkForall} over an integer constrained
 * {@code lo <= i < hi}, with the closure body as the matrix — rather than
 * iterating.
 *
 * The method-call surface is the spike form; a closer-to-idiom spelling is a
 * Phase 9 question, once the quantifier shape settles.
 */
@CompileStatic
class Forall {

    /** True iff {@code pred} holds for every integer {@code i} with {@code lo <= i < hi}. */
    static boolean range(int lo, int hi, Closure<Boolean> pred) {
        for (int i = lo; i < hi; i++) {
            if (!pred.call(i)) return false
        }
        true
    }
}
