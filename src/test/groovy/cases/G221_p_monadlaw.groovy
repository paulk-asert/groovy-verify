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

/** 'P-monadlaw' — 7 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G221_p_monadlaw {

    static final List<Map> CASES = [

        // Phase C (Tier-1 law) — left identity `unit(a).chain(f) == f.apply(a)` discharged over the carrier
        // datatype (Phase B) + uninterpreted apply (Phase A), with bind modelled from its verified Identity body.
        [group: 'P-monadlaw', name: 'left identity proves', ok: true,
         src: tc('''@groovy.transform.Monadic(bind = 'chain', map = 'transform')
                    class Res {
                        final Object v
                        Res(Object v) { this.v = v }
                        @Requires({ f != null }) Res chain(java.util.function.Function f) { (Res) f.apply(v) }
                        @Requires({ f != null }) Res transform(java.util.function.Function f) { new Res(f.apply(v)) }
                        @Ensures({ new Res(a).chain(f) == f.apply(a) })
                        static void leftIdentity(Object a, java.util.function.Function<Object, Res> f) { } }''')],
        [group: 'P-monadlaw', name: 'CONTROL bind not forced equal to a different application refutes', expect: 'Cannot prove postcondition',
         src: tc('''@groovy.transform.Monadic(bind = 'chain', map = 'transform')
                    class Res {
                        final Object v
                        Res(Object v) { this.v = v }
                        @Requires({ f != null }) Res chain(java.util.function.Function f) { (Res) f.apply(v) }
                        @Requires({ f != null }) Res transform(java.util.function.Function f) { new Res(f.apply(v)) }
                        @Ensures({ new Res(a).chain(f) == f.apply(b) })
                        static void bogus(Object a, Object b, java.util.function.Function<Object, Res> f) { } }''')],
        // Right identity `m.chain(unit) == m` and functor identity `m.transform(id) == m` — the unit/identity
        // functions arrive as closure literals, beta-reduced to `unit(content(m))`, then the datatype round-trip.
        [group: 'P-monadlaw', name: 'right identity proves', ok: true,
         src: tc('''@groovy.transform.Monadic(bind = 'chain', map = 'transform')
                    class Res {
                        final Object v
                        Res(Object v) { this.v = v }
                        @Requires({ f != null }) Res chain(java.util.function.Function f) { (Res) f.apply(v) }
                        @Requires({ f != null }) Res transform(java.util.function.Function f) { new Res(f.apply(v)) }
                        @Ensures({ m.chain({ x -> new Res(x) }) == m })
                        static void rightIdentity(Res m) { } }''')],
        [group: 'P-monadlaw', name: 'functor identity proves', ok: true,
         src: tc('''@groovy.transform.Monadic(bind = 'chain', map = 'transform')
                    class Res {
                        final Object v
                        Res(Object v) { this.v = v }
                        @Requires({ f != null }) Res chain(java.util.function.Function f) { (Res) f.apply(v) }
                        @Requires({ f != null }) Res transform(java.util.function.Function f) { new Res(f.apply(v)) }
                        @Ensures({ m.transform({ x -> x }) == m })
                        static void functorIdentity(Res m) { } }''')],
        [group: 'P-monadlaw', name: 'CONTROL functor identity does not collapse distinct carriers', expect: 'Cannot prove postcondition',
         src: tc('''@groovy.transform.Monadic(bind = 'chain', map = 'transform')
                    class Res {
                        final Object v
                        Res(Object v) { this.v = v }
                        @Requires({ f != null }) Res chain(java.util.function.Function f) { (Res) f.apply(v) }
                        @Requires({ f != null }) Res transform(java.util.function.Function f) { new Res(f.apply(v)) }
                        @Ensures({ m.transform({ x -> x }) == n })
                        static void bogus2(Res m, Res n) { } }''')],
        // Phase D — associativity `m.chain(f).chain(g) == m.chain(x -> f(x).chain(g))`: the constructed closure's
        // body itself binds; the nested receivers (`m.chain(f)`, `f.apply(x)`) resolve to the carrier.
        [group: 'P-monadlaw', name: 'associativity proves', ok: true,
         src: tc('''@groovy.transform.Monadic(bind = 'chain', map = 'transform')
                    class Res {
                        final Object v
                        Res(Object v) { this.v = v }
                        @Requires({ f != null }) Res chain(java.util.function.Function f) { (Res) f.apply(v) }
                        @Requires({ f != null }) Res transform(java.util.function.Function f) { new Res(f.apply(v)) }
                        @Ensures({ m.chain(f).chain(g) == m.chain({ x -> f.apply(x).chain(g) }) })
                        static void associativity(Res m, java.util.function.Function<Object, Res> f, java.util.function.Function<Object, Res> g) { } }''')],
        [group: 'P-monadlaw', name: 'CONTROL bind order is not commutative refutes', expect: 'Cannot prove postcondition',
         src: tc('''@groovy.transform.Monadic(bind = 'chain', map = 'transform')
                    class Res {
                        final Object v
                        Res(Object v) { this.v = v }
                        @Requires({ f != null }) Res chain(java.util.function.Function f) { (Res) f.apply(v) }
                        @Requires({ f != null }) Res transform(java.util.function.Function f) { new Res(f.apply(v)) }
                        @Ensures({ m.chain(f).chain(g) == m.chain(g).chain(f) })
                        static void bogus3(Res m, java.util.function.Function<Object, Res> f, java.util.function.Function<Object, Res> g) { } }''')],
    ]
}
