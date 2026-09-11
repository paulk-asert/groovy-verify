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

/** 'P291 monoid value' — Phase 291: library-style Monoid/Semigroup VALUES built from a visible lambda. */
class G341_p291_monoid_values {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A Monoid/Semigroup value built from a visible lambda (Functional Java style) has its laws proven: the subtraction monoid and a wrong zero refute, CombinerChecker accepts the carrier either way.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — abstract-carrier laws: higher-order/monadic shapes beyond the grid'

    // Functional Java's carrier shapes, as source stubs (the real `fj.Monoid` is bytecode — out of source-level
    // reach, like G219's FjOption): `Monoid.monoid(F2, zero)`, `Semigroup.semigroup(F2)`, and a library constant.
    // They FOLLOW the checked class, so only that class carries the @TypeChecked extensions.
    static final String FJ = '''
        interface F2<A, B, C> { C f(A a, B b) }
        class Semigroup<A> {
            final F2<A, A, A> op
            Semigroup(F2<A, A, A> op) { this.op = op }
            static <A> Semigroup<A> semigroup(F2<A, A, A> op) { new Semigroup<A>(op) }
            A sum(A a, A b) { op.f(a, b) }
        }
        class Monoid<A> {
            final F2<A, A, A> op
            final A zero
            Monoid(F2<A, A, A> op, A zero) { this.op = op; this.zero = zero }
            static <A> Monoid<A> monoid(F2<A, A, A> op, A zero) { new Monoid<A>(op, zero) }
            A sum(A a, A b) { op.f(a, b) }
            static final Monoid<Integer> intAdditionMonoid = monoid({ int a, int b -> a + b } as F2<Integer, Integer, Integer>, 0)
        }
        '''

    static String both(String cls) {
        tcExt(['groovy.typecheckers.CombinerChecker', 'verification.VerifyChecker'], cls.stripIndent() + FJ.stripIndent())
    }

    static final List<Map> CASES = [
        // CombinerChecker classifies `add::sum` by its owner's simple name (Monoid) and accepts it as "an assertion
        // carrier, not a proof"; groovy-verify now proves what the carrier asserts, from the lambda at the site.
        [group: 'P291 monoid value', name: 'Monoid.monoid(add, 0): associativity + identity prove (both checkers)', ok: true,
         src: both('''class Sums {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Monoid<Integer> add = Monoid.monoid({ int a, int b -> a + b } as F2<Integer, Integer, Integer>, 0)
                            xs.sumParallel(add::sum)
                        }
                    }''')],
        [group: 'P291 monoid value', name: 'Semigroup.semigroup(max): associativity proves (both checkers)', ok: true,
         src: both('''class Maxes {
                        @Requires({ xs != null })
                        static int biggest(List<Integer> xs) {
                            Semigroup<Integer> max = Semigroup.semigroup({ int a, int b -> a >= b ? a : b } as F2<Integer, Integer, Integer>)
                            xs.sumParallel(max::sum)
                        }
                    }''')],
        [group: 'P291 monoid value', name: 'string concat monoid with zero \'\' proves', ok: true,
         src: both('''class Glue {
                        @Requires({ xs != null })
                        static String all(List<String> xs) {
                            Monoid<String> cat = Monoid.monoid({ String a, String b -> a + b } as F2<String, String, String>, '')
                            xs.sumParallel(cat::sum)
                        }
                    }''')],
        // The canonical lying instance: type-checks in FJ, Haskell and Cats, and CombinerChecker accepts the carrier.
        [group: 'P291 monoid value', name: 'the subtraction monoid refutes associativity (CombinerChecker accepts the carrier)',
         expect: 'Cannot prove Monoid associativity for combiner sub', refute: '__',
         src: both('''class Diffs {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Monoid<Integer> sub = Monoid.monoid({ int a, int b -> a - b } as F2<Integer, Integer, Integer>, 0)
                            xs.sumParallel(sub::sum)
                        }
                    }''')],
        [group: 'P291 monoid value', name: 'a wrong zero (1 for sum) refutes identity',
         expect: 'Cannot prove Monoid identity for combiner add', refute: '__',
         src: both('''class Sums {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Monoid<Integer> add = Monoid.monoid({ int a, int b -> a + b } as F2<Integer, Integer, Integer>, 1)
                            xs.sumParallel(add::sum)
                        }
                    }''')],
        // Floating-point addition is not associative, so a `double` sum monoid is a lie the checker now names.
        [group: 'P291 monoid value', name: 'a double sum monoid refutes associativity (IEEE rounding)',
         expect: 'Cannot prove Monoid associativity for combiner fsum', refute: '__',
         src: both('''class FSums {
                        @Requires({ xs != null })
                        static double total(List<Double> xs) {
                            Monoid<Double> fsum = Monoid.monoid({ double a, double b -> a + b } as F2<Double, Double, Double>, 0.0d)
                            xs.sumParallel(fsum::sum)
                        }
                    }''')],
        // A static field initialised from a visible lambda is the same site, one level up.
        [group: 'P291 monoid value', name: 'a static-field Semigroup built from subtraction refutes',
         expect: 'Cannot prove Semigroup associativity for combiner SUB', refute: '__',
         src: both('''class Fields {
                        static final Semigroup<Integer> SUB = Semigroup.semigroup({ int a, int b -> a - b } as F2<Integer, Integer, Integer>)
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) { xs.sumParallel(SUB::sum) }
                    }''')],
        // An untyped lambda takes its parameter type from the carrier's type argument (Monoid<Integer> → int).
        [group: 'P291 monoid value', name: 'an untyped lambda is typed from Monoid<Integer> and refutes',
         expect: 'Cannot prove Monoid associativity for combiner sub', refute: '__',
         src: both('''class Untyped {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Monoid<Integer> sub = Monoid.monoid({ a, b -> a - b } as F2<Integer, Integer, Integer>, 0)
                            xs.sumParallel(sub::sum)
                        }
                    }''')],
        // What stays loud: a visible body outside the fragment skips exactly as an impure @Reducer does …
        [group: 'P291 monoid value', name: 'a lambda calling unmodelled code skips loudly',
         expect: 'Skipped verification of postcondition for mx (the Semigroup combiner is not an equational lambda',
         src: both('''class Unmodelled {
                        @Requires({ xs != null })
                        static int biggest(List<Integer> xs) {
                            Semigroup<Integer> mx = Semigroup.semigroup({ int a, int b -> Math.max(a, b) } as F2<Integer, Integer, Integer>)
                            xs.sumParallel(mx::sum)
                        }
                    }''')],
        // … and so does an identity element the verifier cannot read as a literal.
        [group: 'P291 monoid value', name: 'a non-literal zero skips the identity law loudly',
         expect: 'identity element is not a literal',
         src: both('''class NonLiteral {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs, int z) {
                            Monoid<Integer> add = Monoid.monoid({ int a, int b -> a + b } as F2<Integer, Integer, Integer>, z)
                            xs.sumParallel(add::sum)
                        }
                    }''')],
    ]
}
