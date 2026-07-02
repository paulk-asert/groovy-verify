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

/** 'P116 monoid' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G229_p116_monoid {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A two-checker compile (CombinerChecker + VerifyChecker) over a real injectParallel site: the shape is checked and the monoid laws + reduce==sum proven.'

    static final List<Map> CASES = [
        // ---------- P116 monoids/semigroups: checked AND proven (composition with CombinerChecker) ----------
        // A genuine two-checker compile under one @TypeChecked(extensions=[...]). `groovy.typecheckers.Combiner-
        // Checker` checks a combiner's *shape* — that the operation handed to a parallel reduction (`inject-
        // Parallel`/`sumParallel`) is associative — and for a method reference it TRUSTS the @Associative/@Reducer
        // annotation. groovy-verify proves the *semantics* on the SAME class: the combiner's defining equation,
        // the monoid laws (associativity / identity), and — via Phase-116 combiner inlining — that the sequential
        // reduction calling the combiner gives the right aggregate (which CombinerChecker does not attempt). The
        // synergy mirrors the PurityChecker case: CombinerChecker relies on @Associative/@Reducer, groovy-verify
        // proves it warranted. Sum is a *monoid* (identity 0), so it carries @Reducer(zero='0'); the seedless
        // `sumParallel(Sum::add)` (a `::` method reference) is the simplest call form, and CombinerChecker certifies
        // it from the @Reducer. (Largest, a semigroup with no identity, stays @Associative.) A full Sum monoid:
        [group: 'P116 monoid', name: 'Sum monoid: add + identity + associativity + reduce == sum (both checkers)', ok: true,
         src: tcExt(['groovy.typecheckers.CombinerChecker', 'verification.VerifyChecker'], '''class Sum {
                        @groovy.transform.Reducer(zero = '0')
                        @Ensures({ result == a + b })
                        static int add(int a, int b) { a + b }
                        @Ensures({ result })
                        static boolean identity(int a) {
                            int l = Sum.add(a, 0)
                            int r = Sum.add(0, a)
                            return l == a && r == a
                        }
                        @Ensures({ result })
                        static boolean associative(int a, int b, int c) {
                            int ab = Sum.add(a, b)
                            int left = Sum.add(ab, c)
                            int bc = Sum.add(b, c)
                            int right = Sum.add(a, bc)
                            return left == right
                        }
                        @Requires({ xs != null && xs.length > 0 })
                        @Ensures({ result == xs.sum() })
                        static int reduce(int[] xs) {
                            int acc = xs[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= xs.length && acc == xs[0..<i].sum() })
                            @Decreases({ xs.length - i })
                            while (i < xs.length) { acc = Sum.add(acc, xs[i]); i = i + 1 }
                            return acc
                        }
                        // CombinerChecker certifies this seedless call site (Sum::add is @Reducer); the laws prove it.
                        static void parallelReduce() {
                            [1, 2, 3, 4].sumParallel(Sum::add)
                        }
                    }''')],
        // The @Reducer(zero='0') buys CombinerChecker a seed check: when you *do* seed (injectParallel), a seed
        // that contradicts the declared identity is flagged — the seed is still required (no seedless inject).
        [group: 'P116 monoid', name: 'CombinerChecker rejects an injectParallel seed that contradicts @Reducer(zero)', ok: false, expect: 'does not match',
         src: tcExt(['groovy.typecheckers.CombinerChecker', 'verification.VerifyChecker'], '''class Sum {
                        @groovy.transform.Reducer(zero = '0')
                        @Ensures({ result == a + b })
                        static int add(int a, int b) { a + b }
                        static void parallelReduce() {
                            [1, 2, 3, 4].injectParallel(5, Sum.&add)
                        }
                    }''')],
        // A Largest semigroup (associative, no identity) — the witnessed-extremum reduction gives the max, and a
        // sumParallel call site exercises CombinerChecker on the @Associative `max`.
        [group: 'P116 monoid', name: 'Largest semigroup: max + associativity + reduce == max (both checkers)', ok: true,
         src: tcExt(['groovy.typecheckers.CombinerChecker', 'verification.VerifyChecker'], '''class Largest {
                        @groovy.transform.Associative
                        @Ensures({ result == (a >= b ? a : b) })
                        static int max(int a, int b) { a >= b ? a : b }
                        @Ensures({ result })
                        static boolean associative(int a, int b, int c) {
                            int ab = Largest.max(a, b)
                            int left = Largest.max(ab, c)
                            int bc = Largest.max(b, c)
                            int right = Largest.max(a, bc)
                            return left == right
                        }
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ result == a.max() })
                        static int reduce(int[] a) {
                            int acc = a[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= a.length &&
                                Forall.range(0, i) { int k -> a[k] <= acc } &&
                                (0..<i).any { int k -> a[k] == acc } })
                            @Decreases({ a.length - i })
                            while (i < a.length) { acc = Largest.max(acc, a[i]); i = i + 1 }
                            return acc
                        }
                        static void parallelReduce() {
                            [1, 2, 3, 4].sumParallel(Largest.&max)
                        }
                    }''')],
        // CombinerChecker's channel: a non-associative *inline* combiner (`a - b`) passed to injectParallel is
        // flagged by static shape analysis, in any mode — groovy-verify never sees it (no contract).
        [group: 'P116 monoid', name: 'CombinerChecker rejects a non-associative inline combiner', ok: false, expect: 'CombinerChecker',
         src: tcExt(['groovy.typecheckers.CombinerChecker', 'verification.VerifyChecker'], '''class Bad {
                        static void parallelReduce() {
                            [1, 2, 3, 4].injectParallel(0) { int a, int b -> a - b }
                        }
                    }''')],
        // groovy-verify's channel — and the deeper synergy: subtraction is wrongly annotated @Associative, so
        // CombinerChecker TRUSTS it and stays silent at the `Minus.&sub` call site — but groovy-verify REFUTES
        // the associativity law `(a-b)-c == a-(b-c)`, catching the false annotation CombinerChecker cannot.
        [group: 'P116 monoid', name: 'a false @Associative is refuted by groovy-verify (CombinerChecker trusts it)', ok: false, expect: 'Cannot prove postcondition',
         src: tcExt(['groovy.typecheckers.CombinerChecker', 'verification.VerifyChecker'], '''class Minus {
                        @groovy.transform.Associative
                        @Ensures({ result == a - b })
                        static int sub(int a, int b) { a - b }
                        @Ensures({ result })
                        static boolean associative(int a, int b, int c) {
                            int ab = Minus.sub(a, b)
                            int left = Minus.sub(ab, c)
                            int bc = Minus.sub(b, c)
                            int right = Minus.sub(a, bc)
                            return left == right
                        }
                        static void parallelReduce() {
                            [1, 2, 3, 4].injectParallel(0, Minus.&sub)
                        }
                    }''')],
    ]
}
