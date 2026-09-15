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
        interface F<A, B> { B f(A a) }
        interface F2<A, B, C> { C f(A a, B b) }
        class Semigroup<A> {
            final F2<A, A, A> op
            Semigroup(F2<A, A, A> op) { this.op = op }
            static <A> Semigroup<A> semigroup(F2<A, A, A> op) { new Semigroup<A>(op) }
            static <A> Semigroup<A> semigroup(F<A, F<A, A>> op) { new Semigroup<A>({ A a, A b -> op.f(a).f(b) } as F2<A, A, A>) }
            A sum(A a, A b) { op.f(a, b) }
        }
        class Monoid<A> {
            final F2<A, A, A> op
            final A zero
            Monoid(F2<A, A, A> op, A zero) { this.op = op; this.zero = zero }
            static <A> Monoid<A> monoid(F2<A, A, A> op, A zero) { new Monoid<A>(op, zero) }
            static <A> Monoid<A> monoid(F<A, F<A, A>> op, A zero) { new Monoid<A>({ A a, A b -> op.f(a).f(b) } as F2<A, A, A>, zero) }
            A sum(A a, A b) { op.f(a, b) }
            static final Monoid<Integer> intAdditionMonoid = monoid({ int a, int b -> a + b } as F2<Integer, Integer, Integer>, 0)
        }
        '''

    static String both(String cls) {
        tcExt(['groovy.typecheckers.CombinerChecker', 'verification.VerifyChecker'], cls.stripIndent() + FJ.stripIndent())
    }

    // Palatable lambda (com.jnape.palatable.lambda): Semigroup<A> extends Fn2<A, A, A> is a FUNCTIONAL interface —
    // a lambda IS a Semigroup — and Monoid.monoid(Semigroup<A>, A identity) has a lazy Fn0<A> identity overload.
    static final String PALATABLE = '''
        interface Fn0<A> { A checkedApply() }
        interface Fn2<A, B, C> {
            C checkedApply(A a, B b)
            default C apply(A a, B b) { checkedApply(a, b) }
        }
        interface Semigroup<A> extends Fn2<A, A, A> { }
        interface Monoid<A> extends Semigroup<A> {
            A identity()
            static <A> Monoid<A> monoid(Semigroup<A> semigroup, A identity) { new PMonoid<A>(semigroup, { -> identity } as Fn0<A>) }
            static <A> Monoid<A> monoid(Semigroup<A> semigroup, Fn0<A> identityFn0) { new PMonoid<A>(semigroup, identityFn0) }
        }
        class PMonoid<A> implements Monoid<A> {
            final Semigroup<A> s
            final Fn0<A> z
            PMonoid(Semigroup<A> s, Fn0<A> z) { this.s = s; this.z = z }
            A identity() { z.checkedApply() }
            A checkedApply(A a, A b) { s.checkedApply(a, b) }
        }
        '''

    // Purefun (com.github.tonivade.purefun.typeclasses): Semigroup<T> is a functional interface over `combine`, and
    // Monoid.of(T zero, Operator2<T> combinator) takes the zero FIRST; Monoid.integer() is a library constant.
    static final String PUREFUN = '''
        interface Operator2<T> { T apply(T t1, T t2) }
        interface Semigroup<T> { T combine(T t1, T t2) }
        interface Monoid<T> extends Semigroup<T> {
            T zero()
            static <T> Monoid<T> of(T zero, Operator2<T> combinator) { new FMonoid<T>(zero, combinator) }
            static Monoid<Integer> integer() { of(0, { Integer a, Integer b -> a + b } as Operator2<Integer>) }
        }
        class FMonoid<T> implements Monoid<T> {
            final T z
            final Operator2<T> op
            FMonoid(T z, Operator2<T> op) { this.z = z; this.op = op }
            T zero() { z }
            T combine(T t1, T t2) { op.apply(t1, t2) }
        }
        '''

    static String palatable(String cls) {
        tcExt(['groovy.typecheckers.CombinerChecker', 'verification.VerifyChecker'], cls.stripIndent() + PALATABLE.stripIndent())
    }

    static String purefun(String cls) {
        tcExt(['groovy.typecheckers.CombinerChecker', 'verification.VerifyChecker'], cls.stripIndent() + PUREFUN.stripIndent())
    }

    static final List<Map> CASES = [
        // CombinerChecker classifies `add::sum` by its owner's simple name (Monoid) and accepts it as "an assertion
        // carrier, not a proof"; groovy-verify now proves what the carrier asserts, from the lambda at the site.
        [group: 'P291 monoid value', name: 'Monoid.monoid(add, 0): associativity + identity prove (both checkers)', ok: true,
         untrusted: 'opaque carrier',
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
         expect: 'Cannot prove Semigroup associativity for combiner SUB', refute: '__', untrusted: 'opaque carrier',
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

        // FJ's curried spelling — `Monoid.monoid(F<A, F<A, A>> sum, A zero)`, the combiner `a -> b -> E` — is the same
        // anonymous combiner with its formals taken from the two nested lambdas.
        [group: 'P291 monoid value', name: 'curried Monoid.monoid(a -> b -> a + b, 0) proves', ok: true,
         untrusted: 'opaque carrier',
         src: both('''class Curried {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Monoid<Integer> add = Monoid.monoid({ int a -> { int b -> a + b } as F<Integer, Integer> } as F<Integer, F<Integer, Integer>>, 0)
                            xs.sumParallel(add::sum)
                        }
                    }''')],
        [group: 'P291 monoid value', name: 'the curried subtraction monoid refutes associativity',
         expect: 'Cannot prove Monoid associativity for combiner sub', refute: '__',
         src: both('''class CurriedDiffs {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Monoid<Integer> sub = Monoid.monoid({ int a -> { int b -> a - b } as F<Integer, Integer> } as F<Integer, F<Integer, Integer>>, 0)
                            xs.sumParallel(sub::sum)
                        }
                    }''')],
        [group: 'P291 monoid value', name: 'a curried Semigroup with a wrong claim refutes (max vs min mixed)',
         expect: 'Cannot prove Semigroup associativity for combiner mix', refute: '__',
         src: both('''class CurriedMix {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Semigroup<Integer> mix = Semigroup.semigroup({ int a -> { int b -> a >= b ? b - 1 : a } as F<Integer, Integer> } as F<Integer, F<Integer, Integer>>)
                            xs.sumParallel(mix::sum)
                        }
                    }''')],
        [group: 'P291 monoid value', name: 'an untyped curried lambda is typed from Monoid<Integer> and refutes a wrong zero',
         expect: 'Cannot prove Monoid identity for combiner add', refute: '__',
         src: both('''class CurriedUntyped {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Monoid<Integer> add = Monoid.monoid({ a -> { b -> a + b } as F<Integer, Integer> } as F<Integer, F<Integer, Integer>>, 1)
                            xs.sumParallel(add::sum)
                        }
                    }''')],
        // The inner lambda without its own coercion: STC must accept the nested Closure as the F result.
        [group: 'P291 monoid value', name: 'curried form with an uncast inner lambda refutes subtraction',
         expect: 'Cannot prove Monoid associativity for combiner sub', refute: '__',
         src: both('''class CurriedBare {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Monoid<Integer> sub = Monoid.monoid({ int a -> { int b -> a - b } } as F<Integer, F<Integer, Integer>>, 0)
                            xs.sumParallel(sub::sum)
                        }
                    }''')],

        // Slice 2 — a carrier with no body in sight stays trusted, but VISIBLY: an `opaque carrier` ledger entry at
        // the parallel reduction that relies on it (the harness `trusted:` key reads this compile's records).
        [group: 'P291 monoid value', name: 'a parameter carrier is ledgered as an opaque carrier', ok: true,
         trusted: '[opaque carrier] Params#total — m (a Monoid) at sumParallel',
         src: both('''class Params {
                        @Requires({ xs != null && m != null })
                        static int total(List<Integer> xs, Monoid<Integer> m) {
                            xs.sumParallel(m::sum)
                        }
                    }''')],
        [group: 'P291 monoid value', name: 'a library constant carrier is ledgered as an opaque carrier', ok: true,
         trusted: 'Monoid.intAdditionMonoid (a Monoid) at sumParallel',
         src: both('''class Library {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            xs.sumParallel(Monoid.intAdditionMonoid::sum)
                        }
                    }''')],
        // CombinerChecker's other carrier form: a thin closure delegating to the carrier's method. (Seedless: a
        // seeded injectParallel over a Semigroup is a CombinerChecker error — there is no identity to match the seed.)
        [group: 'P291 monoid value', name: 'a thin delegating closure over an opaque Semigroup is ledgered', ok: true,
         trusted: 's (a Semigroup) at sumParallel: its combiner has no visible body, so its associativity is assumed',
         src: both('''class Delegating {
                        @Requires({ xs != null && s != null })
                        static int total(List<Integer> xs, Semigroup<Integer> s) {
                            xs.sumParallel { Integer a, Integer b -> s.sum(a, b) }
                        }
                    }''')],
        // Built from a lambda, then possibly replaced by an opaque one: the site cannot rely on the proof.
        [group: 'P291 monoid value', name: 'a lambda-built local that is reassigned from a parameter is ledgered', ok: true,
         trusted: 'add (a Monoid) at sumParallel',
         src: both('''class Reassigned {
                        @Requires({ xs != null && m != null })
                        static int total(List<Integer> xs, Monoid<Integer> m, boolean other) {
                            Monoid<Integer> add = Monoid.monoid({ int a, int b -> a + b } as F2<Integer, Integer, Integer>, 0)
                            if (other) add = m
                            xs.sumParallel(add::sum)
                        }
                    }''')],

        // Palatable lambda's spellings — a Semigroup lambda handed to Monoid.monoid, a bare lambda AS the Semigroup
        // (a functional interface: no factory call at all), and the lazy Fn0 identity.
        [group: 'P291 monoid value', name: 'Palatable Monoid.monoid(semigroup lambda, 0) proves', ok: true,
         untrusted: 'opaque carrier',
         src: palatable('''class PSums {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Monoid<Integer> add = Monoid.monoid({ int a, int b -> a + b } as Semigroup<Integer>, 0)
                            xs.sumParallel(add::apply)
                        }
                    }''')],
        [group: 'P291 monoid value', name: 'the Palatable subtraction monoid refutes associativity',
         expect: 'Cannot prove Monoid associativity for combiner sub', refute: '__',
         src: palatable('''class PDiffs {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Monoid<Integer> sub = Monoid.monoid({ int a, int b -> a - b } as Semigroup<Integer>, 0)
                            xs.sumParallel(sub::apply)
                        }
                    }''')],
        [group: 'P291 monoid value', name: 'a Palatable Semigroup that IS a lambda (no factory) refutes',
         expect: 'Cannot prove Semigroup associativity for combiner sub', refute: '__', untrusted: 'opaque carrier',
         src: palatable('''class PBare {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Semigroup<Integer> sub = { int a, int b -> a - b } as Semigroup<Integer>
                            xs.sumParallel(sub::apply)
                        }
                    }''')],
        [group: 'P291 monoid value', name: 'a Palatable lazy identity { -> 1 } for a sum refutes identity',
         expect: 'Cannot prove Monoid identity for combiner add', refute: '__',
         src: palatable('''class PLazy {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Monoid<Integer> add = Monoid.monoid({ int a, int b -> a + b } as Semigroup<Integer>, { -> 1 } as Fn0<Integer>)
                            xs.sumParallel(add::apply)
                        }
                    }''')],
        // Groovy's native lambda syntax, assigned to the functional-interface type with no cast at all.
        [group: 'P291 monoid value', name: 'a native Groovy lambda typed as a Palatable Semigroup refutes',
         expect: 'Cannot prove Semigroup associativity for combiner sub', refute: '__',
         src: palatable('''class PNative {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Semigroup<Integer> sub = (int a, int b) -> a - b
                            xs.sumParallel(sub::apply)
                        }
                    }''')],

        // Composition is chased: a Monoid built from a Semigroup VARIABLE resolves through the variable's initialiser.
        // Associativity belongs to the lambda — discharged once, at sg's own site, under sg's name — and identity to
        // the Monoid, anchored on its call. Neither site is ledgered: every law the reduction relies on was checked.
        [group: 'P291 monoid value', name: 'a Palatable Monoid composed from a Semigroup local: sg refutes, m is not ledgered',
         expect: 'Cannot prove Semigroup associativity for combiner sg', refute: ['__', 'Monoid associativity'],
         untrusted: 'opaque carrier',
         src: palatable('''class PComposed {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Semigroup<Integer> sg = { int a, int b -> a - b } as Semigroup<Integer>
                            Monoid<Integer> m = Monoid.monoid(sg, 0)
                            xs.sumParallel(m::apply)
                        }
                    }''')],
        [group: 'P291 monoid value', name: 'a composed Palatable sum monoid proves (both laws, no ledger entry)', ok: true,
         untrusted: 'opaque carrier',
         src: palatable('''class PComposedOk {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Semigroup<Integer> sg = { int a, int b -> a + b } as Semigroup<Integer>
                            Monoid<Integer> m = Monoid.monoid(sg, 0)
                            xs.sumParallel(m::apply)
                        }
                    }''')],
        [group: 'P291 monoid value', name: 'a composed monoid with a wrong zero refutes identity under the Monoid\'s name',
         expect: 'Cannot prove Monoid identity for combiner m', refute: '__',
         src: palatable('''class PComposedZero {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Semigroup<Integer> sg = { int a, int b -> a + b } as Semigroup<Integer>
                            Monoid<Integer> m = Monoid.monoid(sg, 1)
                            xs.sumParallel(m::apply)
                        }
                    }''')],
        // What the chase will not follow: a Semigroup parameter, or a local reassigned from one.
        [group: 'P291 monoid value', name: 'a Monoid composed from a Semigroup parameter is still ledgered', ok: true,
         trusted: 'm (a Monoid) at sumParallel',
         src: palatable('''class PComposedParam {
                        @Requires({ xs != null && sg != null })
                        static int total(List<Integer> xs, Semigroup<Integer> sg) {
                            Monoid<Integer> m = Monoid.monoid(sg, 0)
                            xs.sumParallel(m::apply)
                        }
                    }''')],
        [group: 'P291 monoid value', name: 'a Monoid composed from a reassigned Semigroup local is ledgered', ok: true,
         trusted: 'm (a Monoid) at sumParallel',
         src: palatable('''class PComposedReassigned {
                        @Requires({ xs != null && other != null })
                        static int total(List<Integer> xs, Semigroup<Integer> other, boolean swap) {
                            Semigroup<Integer> sg = { int a, int b -> a + b } as Semigroup<Integer>
                            if (swap) sg = other
                            Monoid<Integer> m = Monoid.monoid(sg, 0)
                            xs.sumParallel(m::apply)
                        }
                    }''')],
        // A plain function local (FJ's F2 is not a carrier) has no site of its own that discharges anything, so the
        // Monoid built from it owes BOTH laws — associativity is reported at the Monoid, under its name.
        [group: 'P291 monoid value', name: 'an FJ Monoid composed from an F2 function local refutes at the Monoid',
         expect: 'Cannot prove Monoid associativity for combiner m', refute: '__',
         src: both('''class FjComposed {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            F2<Integer, Integer, Integer> f = { int a, int b -> a - b } as F2<Integer, Integer, Integer>
                            Monoid<Integer> m = Monoid.monoid(f, 0)
                            xs.sumParallel(m::sum)
                        }
                    }''')],

        // Purefun's spellings — Monoid.of with the zero FIRST, a Semigroup lambda field, and a library constant.
        [group: 'P291 monoid value', name: 'Purefun Monoid.of(0, add) proves (zero first)', ok: true,
         untrusted: 'opaque carrier',
         src: purefun('''class FSums {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Monoid<Integer> add = Monoid.of(0, { int a, int b -> a + b } as Operator2<Integer>)
                            xs.sumParallel(add::combine)
                        }
                    }''')],
        [group: 'P291 monoid value', name: 'Purefun Monoid.of(1, add) refutes identity',
         expect: 'Cannot prove Monoid identity for combiner add', refute: '__',
         src: purefun('''class FWrongZero {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Monoid<Integer> add = Monoid.of(1, { int a, int b -> a + b } as Operator2<Integer>)
                            xs.sumParallel(add::combine)
                        }
                    }''')],
        [group: 'P291 monoid value', name: 'a Purefun Semigroup lambda field refutes',
         expect: 'Cannot prove Semigroup associativity for combiner SUB', refute: '__', untrusted: 'opaque carrier',
         src: purefun('''class FField {
                        static final Semigroup<Integer> SUB = { int a, int b -> a - b } as Semigroup<Integer>
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) { xs.sumParallel(SUB::combine) }
                    }''')],
        [group: 'P291 monoid value', name: 'the Purefun library constant Monoid.integer() is ledgered as an opaque carrier', ok: true,
         trusted: 'Monoid.integer() (a Monoid) at sumParallel',
         src: purefun('''class FLibrary {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) { xs.sumParallel(Monoid.integer()::combine) }
                    }''')],

        // Surfacing the ledger to a consumer's build: VERIFY_TRUST (the harness `trustMode:` key sets it for one
        // compile). `deny` turns every trusted fact into a compile error — an opaque carrier fails, a proven one
        // compiles clean, and the other ledger kinds are covered by the same switch.
        [group: 'P291 monoid value', name: 'VERIFY_TRUST=deny: an opaque carrier fails the compile', trustMode: 'deny',
         // anchored at the SITE — the combiner handed to sumParallel (`Monoid.integer()::combine`), not the class
         expect: ['Trusted without proof (VERIFY_TRUST=deny): [opaque carrier] FDenied#total — Monoid.integer() (a Monoid) at sumParallel',
                  '@ line 5, column 77.'],
         src: purefun('''class FDenied {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) { xs.sumParallel(Monoid.integer()::combine) }
                    }''')],
        [group: 'P291 monoid value', name: 'VERIFY_TRUST=deny: a proven carrier compiles clean', trustMode: 'deny', ok: true,
         src: purefun('''class FProvenDeny {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) {
                            Monoid<Integer> add = Monoid.of(0, { int a, int b -> a + b } as Operator2<Integer>)
                            xs.sumParallel(add::combine)
                        }
                    }''')],
        // One fact reached from two sites fails at BOTH — the pending records dedupe by fact AND site.
        [group: 'P291 monoid value', name: 'VERIFY_TRUST=deny: an opaque carrier used twice fails at both sites', trustMode: 'deny',
         expect: ['Trusted without proof (VERIFY_TRUST=deny): [opaque carrier] FTwice#twice — m (a Monoid) at sumParallel',
                  '@ line 6, column 52.', '@ line 7, column 52.'],
         src: purefun('''class FTwice {
                        @Requires({ xs != null && m != null })
                        static int twice(List<Integer> xs, Monoid<Integer> m) {
                            int a = xs.sumParallel(m::combine)
                            int b = xs.sumParallel(m::combine)
                            a + b
                        }
                    }''')],
        // The per-kind filter: `deny:carrier` fails only opaque carriers; other kinds stay in the ledger.
        [group: 'P291 monoid value', name: 'VERIFY_TRUST=deny:carrier fails an opaque carrier', trustMode: 'deny:carrier',
         expect: 'Trusted without proof (VERIFY_TRUST=deny): [opaque carrier] FDeniedKind#total',
         src: purefun('''class FDeniedKind {
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) { xs.sumParallel(Monoid.integer()::combine) }
                    }''')],
        [group: 'P291 monoid value', name: 'VERIFY_TRUST=deny:carrier lets an in-place @ThrowsIf through (still ledgered)',
         trustMode: 'deny:carrier', ok: true, trusted: '[in-place @ThrowsIf] ParserKind#parse',
         src: tc('''class ParserKind {
                        @ThrowsIf(value = { s == null }, exception = NullPointerException, woven = false, direct = false)
                        static Object parse(Object s) { return helper(s) }
                        static Object helper(Object s) { s }
                    }''')],
        // Clauses combine, first match deciding: deny the @ThrowsIf, report (not deny) the carrier.
        [group: 'P291 monoid value', name: 'VERIFY_TRUST=deny:throwsif;report denies only the @ThrowsIf fact',
         trustMode: 'deny:throwsif;report',
         expect: 'Trusted without proof (VERIFY_TRUST=deny): [in-place @ThrowsIf] FMixed#parse',
         refute: 'Trusted without proof (VERIFY_TRUST=deny): [opaque carrier]',
         src: purefun('''class FMixed {
                        @ThrowsIf(value = { s == null }, exception = NullPointerException, woven = false, direct = false)
                        static Object parse(Object s) { return helper(s) }
                        static Object helper(Object s) { s }
                        @Requires({ xs != null })
                        static int total(List<Integer> xs) { xs.sumParallel(Monoid.integer()::combine) }
                    }''')],
        // A typo must not read as "strict": a kind token naming no kind fails the compile, whatever it contains.
        [group: 'P291 monoid value', name: 'a malformed VERIFY_TRUST value fails loudly', trustMode: 'deny:carriers',
         expect: "VERIFY_TRUST value 'deny:carriers' is not recognised",
         src: tc('''class Plain {
                        @Ensures({ result == a })
                        static int id(int a) { a }
                    }''')],
        [group: 'P291 monoid value', name: 'VERIFY_TRUST=deny also covers an in-place trusted @ThrowsIf', trustMode: 'deny',
         // anchored at the SITE — the trusted condition `{ s == null }` in the @ThrowsIf, not the class
         expect: ['Trusted without proof (VERIFY_TRUST=deny): [in-place @ThrowsIf] Parser#parse',
                  '@ line 4, column 43.'],
         src: tc('''class Parser {
                        @ThrowsIf(value = { s == null }, exception = NullPointerException, woven = false, direct = false)
                        static Object parse(Object s) { return helper(s) }
                        static Object helper(Object s) { s }
                    }''')],
    ]
}
