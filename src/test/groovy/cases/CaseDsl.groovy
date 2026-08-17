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

/**
 * The shared case-authoring surface for the per-group case files ({@code cases/G*.groovy}): the
 * standard import header ({@code HDR}) and the {@code @TypeChecked} wrapper helpers ({@code tc},
 * {@code tcStr}, {@code tci}, {@code tcs}, {@code tcExt}) plus the reusable source fragments
 * (PRODUCER, UOM, …), split out of VerifyHarness so each group file static-imports one small DSL.
 * VerifyHarness re-exposes this surface for external consumers (RuntimeRung reads HDR).
 */
class CaseDsl {

    static final String HDR = '''
        import groovy.transform.TypeChecked
        import groovy.transform.Pure
        import groovy.contracts.Requires
        import groovy.contracts.Ensures
        import groovy.contracts.Invariant
        import groovy.contracts.Decreases
        import groovy.contracts.Modifies
        import groovy.contracts.ThrowsIf
        import jakarta.validation.constraints.*
        import groovy.test.GroovyAssert
        import static groovy.test.GroovyAssert.shouldFail
        import verification.Forall
                import verification.Sets
        import verification.Sorted
        import verification.Fib
        import verification.Trib
        import verification.Tetra
        import verification.Gcd
        import verification.Lcm
        import verification.Fact
        import verification.Binom
        import verification.Bezout
        import verification.CheckOverflow
        import verification.Declassify
        import verification.Label
        import verification.SelfEnsures
        import verification.Rely
        import verification.Guarantee
        import verification.UnderRely
        import java.util.function.Function
    '''.stripIndent()

    /** A contracted producer reused by the cross-call precondition cases. */
    static final String PRODUCER = '''
        class P {
            @Requires({ x >= 0 })
            static int sq(int x) { (int) Math.sqrt((double) x) }
        }
    '''.stripIndent()

    /** A producer whose precondition is reference nullity — exercises the cross-boundary nullity oracle. */
    static final String NULLITY_PRODUCER = '''
        class N {
            @Requires({ s != null })
            static int len(String s) { s.length() }
        }
    '''.stripIndent()

    /** A producer whose precondition is collection size — exercises the cross-boundary size oracle. */
    static final String SIZE_PRODUCER = '''
        class L {
            @Requires({ xs.size() > 0 })
            static int first(List xs) { 0 }
        }
    '''.stripIndent()

    /** A user-defined @NonNull marker (matched by simple name, like NullChecker) for the implicit-invariant slice. */
    static final String NONNULL_ANN = '''
        @java.lang.annotation.Retention(java.lang.annotation.RetentionPolicy.RUNTIME)
        @java.lang.annotation.Target([java.lang.annotation.ElementType.FIELD,
                                      java.lang.annotation.ElementType.METHOD,
                                      java.lang.annotation.ElementType.PARAMETER])
        @interface NonNull {}
    '''.stripIndent()

    /**
     * A {@code TYPE_USE}-only @NonNull marker — the JSpecify / Checker Framework spelling, as opposed to
     * {@link #NONNULL_ANN}'s declaration targets. Groovy keeps a TYPE_USE annotation in the ClassNode's
     * separate {@code getTypeAnnotations()} list, so this is what the Phase 233 cases use to exercise the
     * type-annotation reading path.
     */
    static final String NONNULL_TYPEUSE_ANN = '''
        @java.lang.annotation.Retention(java.lang.annotation.RetentionPolicy.RUNTIME)
        @java.lang.annotation.Target([java.lang.annotation.ElementType.TYPE_USE])
        @interface NonNull {}
    '''.stripIndent()

    /** The TYPE_USE @Nullable twin (Phase 239 — the nullable-wins veto cases compose it with the above). */
    static final String NULLABLE_TYPEUSE_ANN = '''
        @java.lang.annotation.Retention(java.lang.annotation.RetentionPolicy.RUNTIME)
        @java.lang.annotation.Target([java.lang.annotation.ElementType.TYPE_USE])
        @interface Nullable {}
    '''.stripIndent()

    /** JSR 385 imports for the dimensional-analysis (Phase 131) cases — the unit-api jar is a test dependency. */
    static final String UOM = 'import javax.measure.Quantity\nimport javax.measure.quantity.*\n'

    /** JSR 385 + Indriya imports for the value/scale (Phase 132) cases — construction, prefixes, conversion. */
    static final String UOM2 = 'import tech.units.indriya.quantity.Quantities\n' +
                               'import static tech.units.indriya.unit.Units.*\n' +
                               'import static javax.measure.MetricPrefix.*\n'

    /** Wrap a class body in the @TypeChecked verification extension + the standard imports. */
    static String tc(String classText) {
        HDR + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" + classText.stripIndent()
    }

    /** Like {@link #tc} but with this project's String-valued contract annotations (the Java-friendly
     *  {@code verification.Requires}/{@code Ensures}/{@code Decreases}, e.g. {@code @Requires('n >= 0')})
     *  instead of groovy-contracts' closures — so the header deliberately does NOT pull in groovy.contracts. */
    static String tcStr(String classText) {
        'import groovy.transform.TypeChecked\n' +
            'import verification.Requires\nimport verification.Ensures\nimport verification.Decreases\n' +
            "@TypeChecked(extensions = 'verification.VerifyChecker')\n" + classText.stripIndent()
    }

    /** Like {@link #tc} but opts into loop-invariant inference via the parameterised extension syntax
     *  ({@code VerifyChecker(inferLoops: true)}) — the same mechanism NullChecker uses for {@code strict}. */
    static String tci(String classText) {
        HDR + "@TypeChecked(extensions = 'verification.VerifyChecker(inferLoops: true)')\n" + classText.stripIndent()
    }

    /** Like {@link #tc} but also imports {@code java.util.stream.Stream} (Phase 75 infinite-stream cases). */
    static String tcs(String classText) {
        HDR + 'import java.util.stream.Stream\n' +
            "@TypeChecked(extensions = 'verification.VerifyChecker')\n" + classText.stripIndent()
    }

    /** Like {@link #tc} but with a custom ordered extension list, to exercise composition of VerifyChecker
     *  with sibling groovy-typecheckers extensions (RegexChecker, NullChecker, …) in one @TypeChecked. */
    static String tcExt(List<String> extensions, String classText) {
        String exts = extensions.collect { "'" + it + "'" }.join(', ')
        HDR + "@TypeChecked(extensions = [" + exts + "])\n" + classText.stripIndent()
    }
}
