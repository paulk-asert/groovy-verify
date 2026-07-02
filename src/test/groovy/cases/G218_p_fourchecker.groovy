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

/** 'P-fourchecker' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G218_p_fourchecker {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'One Maybe class under four checkers (Null/Monadic/Purity/Verify) with a live DO-comprehension: Vavr-style auto-proves the laws, Optional-style refutes functor composition.'

    static final List<Map> CASES = [

        // The headline four-checker example: NullChecker + MonadicChecker + PurityChecker + VerifyChecker on one
        // class, with a real DO-comprehension so MonadicChecker actually fires (it checks comprehension use-sites).
        // A Vavr-style Maybe is lawful — all four quiet (VerifyChecker auto-proves the laws, MonadicChecker
        // shape-checks the DO); the Optional-style (null-collapsing map) compiles under the other three but
        // VerifyChecker REFUTES functor composition. "Optional is not a lawful functor", machine-checked, four
        // checkers composing.
        [group: 'P-fourchecker', name: 'Vavr Maybe: all four checkers + DO-comprehension, clean (laws auto-prove)', ok: true,
         src: HDR + '@groovy.transform.Monadic(bind = \'flatMap\', map = \'map\')\n' +
              "@TypeChecked(extensions = ['groovy.typecheckers.NullChecker', 'groovy.typecheckers.MonadicChecker', 'groovy.typecheckers.PurityChecker', 'verification.VerifyChecker'])\n" + '''class Maybe {
                        final boolean present
                        final Object value
                        private Maybe(boolean present, Object value) { this.present = present; this.value = value }
                        @Pure static Maybe some(Object v) { new Maybe(true, v) }
                        @Pure static Maybe none() { new Maybe(false, null) }
                        @Requires({ f != null }) Maybe flatMap(java.util.function.Function f) { present ? (Maybe) f.apply(value) : this }
                        @Requires({ g != null }) Maybe map(java.util.function.Function g) { present ? some(g.apply(value)) : this }
                        static Maybe addPair() { DO(a in some(2), b in some(3)) { some(((Integer) a) + ((Integer) b)) } } }'''],
        [group: 'P-fourchecker', name: 'Optional Maybe: all four checkers, VerifyChecker refutes functor composition', expect: 'Cannot prove @Monadic functor composition',
         src: HDR + NONNULL_ANN + '@groovy.transform.Monadic(bind = \'flatMap\', map = \'map\')\n' +
              "@TypeChecked(extensions = ['groovy.typecheckers.NullChecker', 'groovy.typecheckers.MonadicChecker', 'groovy.typecheckers.PurityChecker', 'verification.VerifyChecker'])\n" + '''class Maybe {
                        final boolean present
                        @NonNull final Object value
                        private Maybe(boolean present, Object value) { this.present = present; this.value = value }
                        @Pure static Maybe some(Object v) { new Maybe(true, v) }
                        @Pure static Maybe none() { new Maybe(false, null) }
                        @Requires({ f != null }) Maybe flatMap(java.util.function.Function f) { present ? (Maybe) f.apply(value) : this }
                        @Requires({ g != null }) Maybe map(java.util.function.Function g) { present ? (g.apply(value) == null ? none() : some(g.apply(value))) : this } }'''],
        [group: 'P-fourchecker', name: 'README: Maybe under four checkers + DO', ok: true,
         src: HDR + 'import groovy.transform.Monadic\n' + '''@Monadic(bind = 'flatMap', map = 'map')
@TypeChecked(extensions = ['groovy.typecheckers.NullChecker', 'groovy.typecheckers.MonadicChecker',
                           'groovy.typecheckers.PurityChecker', 'verification.VerifyChecker'])
class Maybe {                                              // a hand-rolled Some(value) | None
    final boolean present
    final Object value
    private Maybe(boolean present, Object value) { this.present = present; this.value = value }
    @Pure static Maybe some(Object v) { new Maybe(true, v) }   // unit
    @Pure static Maybe none()         { new Maybe(false, null) }

    @Requires({ f != null }) Maybe flatMap(Function f) { present ? (Maybe) f.apply(value) : this }
    @Requires({ g != null }) Maybe map(Function g)     { present ? some(g.apply(value)) : this }   // Vavr-style

    static Maybe addPair() { DO(a in some(2), b in some(3)) { some(((Integer) a) + ((Integer) b)) } }
}'''],
    ]
}
