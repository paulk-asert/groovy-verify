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
package cases

import static cases.CaseDsl.*

/** 'P177 sam-shorthand' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G265_p177_sam_shorthand {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'SAM call-operator shorthand f(x) for a Function-typed formal, modelled identically to f.apply(x). Groovy\'s v(args)->v.call(args)->apply rewrite is a resolution-phase step, but contracts are re-parsed at CONVERSION (ContractExpansionTransform), pre-resolution, so f(x) reaches the encoder as an implicit-this call this.f(x); the encoder now recognises that shape when the name is a Function formal and routes it to the same apply$f uninterpreted function as f.apply(x), so the two spellings unify. Teeth: a false claim over the shorthand refutes (genuinely modelled, not skipped). Diagnosed as groovy-verify-internal — Groovy and groovy-contracts both resolve f(x) correctly at runtime.'

    static final List<Map> CASES = [

        // ---------- Phase 177: SAM call-operator shorthand `f(x)` for a Function-typed formal ----------
        // Groovy's `v(args)` -> `v.call(args)` -> SAM `apply` rewrite is a resolution-phase step, but contracts are
        // re-parsed at CONVERSION (ContractExpansionTransform), pre-resolution, so `f(x)` arrives at the encoder as an
        // implicit-`this` call `this.f(x)`. The encoder now recognises that shape when `f` is a Function-typed formal
        // and models it as the SAME `apply$f` uninterpreted function as `f.apply(x)`, so the two spellings unify.
        // (Diagnosed as a groovy-verify-internal limitation — Groovy and groovy-contracts both resolve `f(x)` fine;
        // only the verifier's CONVERSION-phase contract re-parse dropped it.)
        [group: 'P177 sam-shorthand', name: 'f(x) shorthand unifies with f.apply(x)', ok: true,
         src: tc('''class Sam {
                        @Requires({ f.apply(n) == 7 })
                        @Ensures({ f(n) == 7 })
                        static void unify(Function<Integer,Integer> f, int n) {}
                    }''')],
        // Teeth: the shorthand is genuinely modelled (not vacuously skipped) — a false claim over it refutes.
        [group: 'P177 sam-shorthand', name: 'f(x) shorthand refutes a false claim', expect: 'Cannot prove postcondition',
         src: tc('''class SamBad {
                        @Requires({ f(n) == 7 })
                        @Ensures({ f(n) == 8 })
                        static void bad(Function<Integer,Integer> f, int n) {}
                    }''')],
    ]
}
