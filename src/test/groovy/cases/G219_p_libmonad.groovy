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

/** 'P-libmonad' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G219_p_libmonad {

    static final List<Map> CASES = [

        // The three real-world Maybe/Option flavors, as the full five-law set written out by hand (the README's
        // "what the implicit @Monadic contracts are equivalent to" forms). The *actual* library types are bytecode —
        // out of source-level reach — so these are source carriers replicating each library's semantics AND naming:
        // Vavr's `io.vavr.control.Option` and Functional Java's `fj.data.Option` genuinely use `some`/`none` factories
        // (recognised by default), while java.util.Optional uses `of`/`empty` — named faithfully here via the
        // `@Monadic(unit = 'of')` member (published in the snapshot). Vavr (flatMap/map) and Functional Java (bind/map)
        // are lawful monads, so all five laws prove; Optional's null-collapsing map (modelled with its real @NonNull
        // content contract) keeps the four monad/functor laws but breaks functor composition — "Optional is not a
        // lawful functor", machine-checked. The of-named Optional also confirms `unit=` is honored: it is recognised
        // as a carrier *only* because the verifier reads the `unit` member (no `some` factory exists).
        [group: 'P-libmonad', name: 'Vavr Option equivalent (flatMap/map): all five monad+functor laws prove', ok: true,
         src: tc('''@groovy.transform.Monadic(bind = 'flatMap', map = 'map')
                    class VavrOption {
                        final boolean present
                        final Object value
                        private VavrOption(boolean present, Object value) { this.present = present; this.value = value }
                        static VavrOption some(Object v) { new VavrOption(true, v) }
                        static VavrOption none() { new VavrOption(false, null) }
                        @Requires({ f != null }) VavrOption flatMap(java.util.function.Function f) { present ? (VavrOption) f.apply(value) : this }
                        @Requires({ g != null }) VavrOption map(java.util.function.Function g) { present ? some(g.apply(value)) : this }
                        @Ensures({ some(a).flatMap(f) == f.apply(a) })
                        static void leftIdentity(Object a, java.util.function.Function<Object, VavrOption> f) { }
                        @Ensures({ m.flatMap({ x -> some(x) }) == m })
                        static void rightIdentity(VavrOption m) { }
                        @Ensures({ m.flatMap(f).flatMap(g) == m.flatMap({ x -> f.apply(x).flatMap(g) }) })
                        static void associativity(VavrOption m, java.util.function.Function<Object, VavrOption> f, java.util.function.Function<Object, VavrOption> g) { }
                        @Ensures({ m.map({ x -> x }) == m })
                        static void functorIdentity(VavrOption m) { }
                        @Ensures({ m.map(p).map(q) == m.map({ x -> q.apply(p.apply(x)) }) })
                        static void functorComposition(VavrOption m, java.util.function.Function<Object, Object> p, java.util.function.Function<Object, Object> q) { } }''')],
        // Functional Java's Option names bind `bind` (Vavr/Optional use `flatMap`) — so this also exercises the
        // @Monadic(bind = 'bind') member-name path for a two-case carrier, not just the flatMap default.
        [group: 'P-libmonad', name: 'Functional Java Option equivalent (bind/map): all five laws prove', ok: true,
         src: tc('''@groovy.transform.Monadic(bind = 'bind', map = 'map')
                    class FjOption {
                        final boolean present
                        final Object value
                        private FjOption(boolean present, Object value) { this.present = present; this.value = value }
                        static FjOption some(Object v) { new FjOption(true, v) }
                        static FjOption none() { new FjOption(false, null) }
                        @Requires({ f != null }) FjOption bind(java.util.function.Function f) { present ? (FjOption) f.apply(value) : this }
                        @Requires({ g != null }) FjOption map(java.util.function.Function g) { present ? some(g.apply(value)) : this }
                        @Ensures({ some(a).bind(f) == f.apply(a) })
                        static void leftIdentity(Object a, java.util.function.Function<Object, FjOption> f) { }
                        @Ensures({ m.bind({ x -> some(x) }) == m })
                        static void rightIdentity(FjOption m) { }
                        @Ensures({ m.bind(f).bind(g) == m.bind({ x -> f.apply(x).bind(g) }) })
                        static void associativity(FjOption m, java.util.function.Function<Object, FjOption> f, java.util.function.Function<Object, FjOption> g) { }
                        @Ensures({ m.map({ x -> x }) == m })
                        static void functorIdentity(FjOption m) { }
                        @Ensures({ m.map(p).map(q) == m.map({ x -> q.apply(p.apply(x)) }) })
                        static void functorComposition(FjOption m, java.util.function.Function<Object, Object> p, java.util.function.Function<Object, Object> q) { } }''')],
        // java.util.Optional: faithfully named `of`/`empty` (the `of` factory via @Monadic(unit = 'of')), @NonNull
        // content (Some never holds null — its real contract, which makes functor IDENTITY hold) + null-collapsing map.
        // The four lawful laws are written out below and all PROVE; the @Monadic auto-synthesis additionally checks
        // functor COMPOSITION and refutes it — the sole failure, so the expected diagnostic names composition
        // specifically (had a lawful law also failed, the message would differ). This is "Optional keeps the monad
        // laws and functor identity but is not a lawful functor", written out in full.
        [group: 'P-libmonad', name: 'java.util.Optional equivalent (of/empty via unit, @NonNull): four lawful laws prove, functor composition refutes',
         expect: 'Cannot prove @Monadic functor composition for carrier OptionOf',
         src: HDR + NONNULL_ANN + tc('''@groovy.transform.Monadic(bind = 'flatMap', map = 'map', unit = 'of')
                    class OptionOf {
                        final boolean present
                        @NonNull final Object value
                        private OptionOf(boolean present, Object value) { this.present = present; this.value = value }
                        static OptionOf of(Object v) { new OptionOf(true, v) }
                        static OptionOf empty() { new OptionOf(false, null) }
                        @Requires({ f != null }) OptionOf flatMap(java.util.function.Function f) { present ? (OptionOf) f.apply(value) : this }
                        @Requires({ g != null }) OptionOf map(java.util.function.Function g) { present ? (g.apply(value) == null ? empty() : of(g.apply(value))) : this }
                        @Ensures({ of(a).flatMap(f) == f.apply(a) })
                        static void leftIdentity(Object a, java.util.function.Function<Object, OptionOf> f) { }
                        @Ensures({ m.flatMap({ x -> of(x) }) == m })
                        static void rightIdentity(OptionOf m) { }
                        @Ensures({ m.flatMap(f).flatMap(g) == m.flatMap({ x -> f.apply(x).flatMap(g) }) })
                        static void associativity(OptionOf m, java.util.function.Function<Object, OptionOf> f, java.util.function.Function<Object, OptionOf> g) { }
                        @Ensures({ m.map({ x -> x }) == m })
                        static void functorIdentity(OptionOf m) { } }''')],
    ]
}
