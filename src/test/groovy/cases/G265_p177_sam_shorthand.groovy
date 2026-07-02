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

/** 'P177 sam-shorthand' — SAM call-operator shorthand in contracts and bodies; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G265_p177_sam_shorthand {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'SAM call-operator shorthand f(x) for a Function-typed formal, modelled identically to f.apply(x), in both contracts and bodies. Groovy\'s v(args)->v.call(args)->apply rewrite is a resolution-phase step, so the two positions present differently: a CONTRACT is re-parsed at CONVERSION (pre-resolution) and f(x) arrives as an implicit-this call this.f(x) — canonicalised to f.apply(x) by ContractNormalizer (Phase 181, the one home for re-parse artifacts) before the encoder sees it, including inside quantifier closures; a BODY is resolved AST where f(x) arrives as f.call(x) — recognised by the encoder directly, gated on a known Function formal so an ordinary Closure.call() is never hijacked. Teeth: a false claim over either position refutes (genuinely modelled, not skipped). Diagnosed as groovy-verify-internal — Groovy and groovy-contracts both resolve f(x) correctly at runtime.'

    static final List<Map> CASES = [

        // ---------- Phase 177/181: SAM call-operator shorthand `f(x)` for a Function-typed formal ----------
        // Groovy's `v(args)` -> `v.call(args)` -> SAM `apply` rewrite is a resolution-phase step, so the two
        // positions present differently, and each has its own canonicalisation:
        //   - CONTRACTS are re-parsed at CONVERSION (pre-resolution), so `f(x)` arrives as an implicit-`this`
        //     call `this.f(x)` — rewritten to `f.apply(x)` by ContractNormalizer (the one home for re-parse
        //     artifacts) before the encoder ever sees it, including inside quantifier closure bodies.
        //   - BODIES are resolved AST, where `f(x)` arrives as `f.call(x)` — the encoder recognises that as
        //     the SAM application directly, gated on a known Function-typed formal (a plain Closure.call()
        //     is never hijacked).
        // Both routes land on the SAME `apply$f` uninterpreted function as an explicit `f.apply(x)`, so all
        // three spellings unify. (Diagnosed as a groovy-verify-internal limitation — Groovy and
        // groovy-contracts both resolve `f(x)` fine; only the pre-resolution contract re-parse dropped it.)
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
        // The shorthand inside a quantifier closure — the normaliser must descend into closure bodies (a plain
        // ExpressionTransformer stops at the closure boundary); the P174 frame lemmas rely on exactly this.
        [group: 'P177 sam-shorthand', name: 'shorthand inside a quantifier closure normalises', ok: true,
         src: tc('''class SamQuant {
                        @Requires({ n <= u && (n..<u).every { int i -> f(i + 1) == f(i) } })
                        @Ensures({ f.apply(u) == f.apply(u) })
                        static void quant(Function<Integer,Integer> f, int n, int u) {}
                    }''')],
        // BODY-side: the resolved `f.call(n)` spelling. The body computes f(n); with the precondition pinning
        // f.apply(n) == 7, the postcondition result == 7 verifies only if the body's `f.call(n)` lands on the
        // same apply$f term — proving the encoder models the resolved shorthand, not just the contract form.
        [group: 'P177 sam-shorthand', name: 'body-side shorthand (resolved f.call) is modelled', ok: true,
         src: tc('''class SamBody {
                        @Requires({ f != null && f.apply(n) == 7 })
                        @Ensures({ result == 7 })
                        static int g(Function<Integer,Integer> f, int n) { return f(n) }
                    }''')],
        // Teeth for the body side: a wrong claimed result refutes (a skip would compile clean instead).
        [group: 'P177 sam-shorthand', name: 'body-side shorthand refutes a wrong result', expect: 'Cannot prove postcondition',
         src: tc('''class SamBodyBad {
                        @Requires({ f != null && f.apply(n) == 7 })
                        @Ensures({ result == 8 })
                        static int g(Function<Integer,Integer> f, int n) { return f(n) }
                    }''')],
    ]
}
