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

/** 'P-maybe' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G217_p_maybe {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A two-case Some|None @Monadic carrier: Vavr-style auto-proves all laws, Optional-style (@NonNull content) auto-refutes functor composition.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — abstract-carrier laws: higher-order/monadic shapes beyond the grid'

    static final List<Map> CASES = [

        // Phase M-C — a two-case @Monadic carrier (Some(value) | None) is recognised and modelled as a two-constructor
        // datatype: `some(x).value == x` and `some(x) != none()` hold by datatype theory (carrier-rooted, no bare param).
        [group: 'P-maybe', name: 'two-case carrier: some/none/content round-trips', rung: 'run', ok: true,
         src: tc('''@groovy.transform.Monadic(bind = 'flatMap', map = 'map')
                    class Maybe {
                        final boolean present
                        final Object value
                        private Maybe(boolean present, Object value) { this.present = present; this.value = value }
                        static Maybe some(Object v) { new Maybe(true, v) }
                        static Maybe none() { new Maybe(false, null) }
                        @Ensures({ some(m.value).value == m.value })
                        static void contentRoundTrip(Maybe m) { }
                        @Ensures({ some(m.value) != none() })
                        static void someDistinctFromNone(Maybe m) { } }''')],
        // Phase M-E — auto-synthesis for two-case carriers. @Monadic alone carries the verdict: a Vavr-style Maybe
        // (no lemmas) auto-proves all five laws; an Optional-style Maybe auto-REFUTES functor composition.
        [group: 'P-maybe', name: 'Vavr-style @Monadic Maybe: all laws auto-prove (no lemmas)', ok: true,
         src: tc('''@groovy.transform.Monadic(bind = 'flatMap', map = 'map')
                    class Maybe {
                        final boolean present
                        final Object value
                        private Maybe(boolean present, Object value) { this.present = present; this.value = value }
                        static Maybe some(Object v) { new Maybe(true, v) }
                        static Maybe none() { new Maybe(false, null) }
                        @Requires({ f != null }) Maybe flatMap(java.util.function.Function f) { present ? (Maybe) f.apply(value) : this }
                        @Requires({ g != null }) Maybe map(java.util.function.Function g) { present ? some(g.apply(value)) : this } }''')],
        // Optional-style with @NonNull content (Optional's real contract: Some never holds null). NullChecker
        // enforces it / groovy-verify assumes it (per param), so functor IDENTITY holds and the sole refutation is
        // functor COMPOSITION — the faithful "Optional is not a lawful functor", auto-derived from @Monadic.
        [group: 'P-maybe', name: 'Optional-style @Monadic Maybe (@NonNull content): auto-refutes functor composition', expect: 'Cannot prove @Monadic functor composition',
         src: HDR + NONNULL_ANN + tc('''@groovy.transform.Monadic(bind = 'flatMap', map = 'map')
                    class Maybe {
                        final boolean present
                        @NonNull final Object value
                        private Maybe(boolean present, Object value) { this.present = present; this.value = value }
                        static Maybe some(Object v) { new Maybe(true, v) }
                        static Maybe none() { new Maybe(false, null) }
                        @Requires({ f != null }) Maybe flatMap(java.util.function.Function f) { present ? (Maybe) f.apply(value) : this }
                        @Requires({ g != null }) Maybe map(java.util.function.Function g) { present ? (g.apply(value) == null ? none() : some(g.apply(value))) : this } }''')],

        // Phase M-D — case-split flatMap/map. The core result: functor composition PROVES for Vavr-style map
        // (always Some(g(v))) and REFUTES for Optional-style map (collapses a null result to None).
        [group: 'P-maybe', name: 'Vavr-style functor composition proves', ok: true,
         src: tc('''@groovy.transform.Monadic(bind = 'flatMap', map = 'map')
                    class Maybe {
                        final boolean present
                        final Object value
                        private Maybe(boolean present, Object value) { this.present = present; this.value = value }
                        static Maybe some(Object v) { new Maybe(true, v) }
                        static Maybe none() { new Maybe(false, null) }
                        @Requires({ f != null }) Maybe flatMap(java.util.function.Function f) { present ? (Maybe) f.apply(value) : this }
                        @Requires({ g != null }) Maybe map(java.util.function.Function g) { present ? some(g.apply(value)) : this }
                        @Ensures({ m.map(p).map(q) == m.map({ x -> q.apply(p.apply(x)) }) })
                        static void functorComposition(Maybe m, java.util.function.Function<Object, Object> p, java.util.function.Function<Object, Object> q) { } }''')],
        [group: 'P-maybe', name: 'Optional-style functor composition REFUTES (null collapse)', expect: 'Cannot prove postcondition',
         src: tc('''@groovy.transform.Monadic(bind = 'flatMap', map = 'map')
                    class Maybe {
                        final boolean present
                        final Object value
                        private Maybe(boolean present, Object value) { this.present = present; this.value = value }
                        static Maybe some(Object v) { new Maybe(true, v) }
                        static Maybe none() { new Maybe(false, null) }
                        @Requires({ f != null }) Maybe flatMap(java.util.function.Function f) { present ? (Maybe) f.apply(value) : this }
                        @Requires({ g != null }) Maybe map(java.util.function.Function g) { present ? (g.apply(value) == null ? none() : some(g.apply(value))) : this }
                        @Ensures({ m.map(p).map(q) == m.map({ x -> q.apply(p.apply(x)) }) })
                        static void functorComposition(Maybe m, java.util.function.Function<Object, Object> p, java.util.function.Function<Object, Object> q) { } }''')],
        [group: 'P-maybe', name: 'two-case monad laws (left identity + associativity) prove', ok: true,
         src: tc('''@groovy.transform.Monadic(bind = 'flatMap', map = 'map')
                    class Maybe {
                        final boolean present
                        final Object value
                        private Maybe(boolean present, Object value) { this.present = present; this.value = value }
                        static Maybe some(Object v) { new Maybe(true, v) }
                        static Maybe none() { new Maybe(false, null) }
                        @Requires({ f != null }) Maybe flatMap(java.util.function.Function f) { present ? (Maybe) f.apply(value) : this }
                        @Requires({ g != null }) Maybe map(java.util.function.Function g) { present ? some(g.apply(value)) : this }
                        @Ensures({ some(a).flatMap(f) == f.apply(a) })
                        static void leftIdentity(Object a, java.util.function.Function<Object, Maybe> f) { }
                        @Ensures({ m.flatMap(f).flatMap(g) == m.flatMap({ x -> f.apply(x).flatMap(g) }) })
                        static void associativity(Maybe m, java.util.function.Function<Object, Maybe> f, java.util.function.Function<Object, Maybe> g) { } }''')],
    ]
}
