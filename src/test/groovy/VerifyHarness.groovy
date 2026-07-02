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
import org.codehaus.groovy.control.MultipleCompilationErrorsException
import org.codehaus.groovy.control.messages.ExceptionMessage
import org.codehaus.groovy.control.messages.SyntaxErrorMessage
import verification.Z3Backend
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import static org.junit.jupiter.api.DynamicTest.dynamicTest

/**
 * Standalone self-test for the verification engine: compiles a battery of
 * annotated snippets on the fly and asserts what VerifyChecker does to each.
 *
 *   - PASS (ok)    : the snippet must compile cleanly (every obligation discharged).
 *   - PASS (error) : the snippet must FAIL to compile with a diagnostic containing
 *                    the expected substring (the checker caught the bug).
 *
 * This replaces the blog repo's per-case demo scripts with one runnable check, so
 * the engine is verifiable in its own repo without the companion demos. Run with:
 *
 *   ./gradlew verify
 */
class VerifyHarness {

    // ── The case corpus ─────────────────────────────────────────────────────────────────────────
    // Cases live in per-group files under src/test/groovy/cases/ (G###_<group>.groovy, one static
    // CASES list each, numbered in the original group order), with the shared import header and
    // @TypeChecked wrappers in cases.CaseDsl. Per-group files keep every list literal far under the
    // JVM's 64KB per-method bytecode limit (the old in-class tables needed manual casesPartN
    // splitting), make a group locally editable, and leave this class as the runner. The DSL
    // surface is re-exposed below for external consumers (RuntimeRung reads HDR).
    static final String HDR = cases.CaseDsl.HDR
    static final String PRODUCER = cases.CaseDsl.PRODUCER
    static final String NULLITY_PRODUCER = cases.CaseDsl.NULLITY_PRODUCER
    static final String SIZE_PRODUCER = cases.CaseDsl.SIZE_PRODUCER
    static final String NONNULL_ANN = cases.CaseDsl.NONNULL_ANN
    static final String UOM = cases.CaseDsl.UOM
    static final String UOM2 = cases.CaseDsl.UOM2

    static String tc(String classText) { cases.CaseDsl.tc(classText) }
    static String tcStr(String classText) { cases.CaseDsl.tcStr(classText) }
    static String tci(String classText) { cases.CaseDsl.tci(classText) }
    static String tcs(String classText) { cases.CaseDsl.tcs(classText) }
    static String tcExt(List<String> extensions, String classText) { cases.CaseDsl.tcExt(extensions, classText) }

    static final List<Map> CASES = loadCases()

    /** The per-group case classes (cases/G*.groovy), in filename order (the G### prefix preserves the
     *  original group order, so case numbering in reports stays stable). Shared with Harvester, which
     *  also reads each class's co-located {@code DESCRIPTION}. */
    static List<Class> caseClasses() {
        File dir = new File('src/test/groovy/cases')
        List<String> names = (dir.listFiles() ?: new File[0])*.name
            .findAll { it ==~ /G\d{3}_.*\.groovy/ }.sort()
        assert names : "case corpus not found under ${dir.absolutePath} — run from the project root"
        names.collect { String n -> Class.forName('cases.' + (n - '.groovy')) }
    }

    /** Concatenate every case file's CASES. */
    private static List<Map> loadCases() {
        List<Map> all = []
        caseClasses().each { Class c -> all.addAll((List<Map>) c.CASES) }
        all
    }

    static List<String> compile(String name, String src) {
        def gcl = new GroovyClassLoader(Thread.currentThread().contextClassLoader)
        try {
            gcl.parseClass(src, "${name}.groovy")
            return null   // compiled cleanly
        } catch (MultipleCompilationErrorsException e) {
            return e.errorCollector.errors.collect { err ->
                if (err instanceof SyntaxErrorMessage) return err.cause.message
                if (err instanceof ExceptionMessage) {
                    def ex = err.cause
                    def sw = new StringWriter()
                    ex.printStackTrace(new PrintWriter(sw))
                    return "${ex.class.simpleName}: ${ex.message}\n${sw}"
                }
                err.toString()
            }
        } finally {
            try { gcl.close() } catch (ignored) {}
        }
    }

    /**
     * Compile one case and judge it against its {@code ok} / {@code expect} / {@code refute} spec.
     * Returns {@code [ok: boolean, detail: String, errors: List<String>]}. The single source of
     * truth for "did this case behave?", shared by {@link #main} (compact console runner) and the
     * {@link #verificationCases} JUnit factory (per-test IDE/CI reporting) — no duplicated judging.
     */
    static Map evaluate(Map c, String name) {
        List<String> errors = compile(name, (String) c.src)
        boolean wantOk = c.ok == true
        boolean ok
        String detail
        if (wantOk) {
            ok = (errors == null)
            detail = ok ? '' : "expected clean compile, got:\n      ${errors?.join('\n      ')}"
        } else {
            String all = errors?.join('\n') ?: ''
            ok = errors != null && all.contains((String) c.expect)
            detail = ok ? '' : (errors == null
                ? "expected error containing '${c.expect}', but compiled cleanly"
                : "expected '${c.expect}', got:\n      ${all.replaceAll('\n', '\n      ')}")
            // Optional `refute`: assert a substring is ABSENT from the diagnostic (e.g. an
            // internal/synthetic name that must not leak into a user-facing counterexample).
            if (ok && c.refute && all.contains((String) c.refute)) {
                ok = false
                detail = "diagnostic should NOT contain '${c.refute}', but did:\n      ${all.replaceAll('\n', '\n      ')}"
            }
        }
        [ok: ok, detail: detail, errors: errors]
    }

    /**
     * JUnit 6 dynamic-test view of the same {@link #CASES}: one individually-named, individually-runnable
     * test per case (display name {@code "group :: name"}) — so an IDE / CI sees ~860 tests, not one
     * pass/fail, and `./gradlew test` / the IDE gutter can run a single case. The data list is untouched.
     * Filter from the CLI with {@code -Dverify.only=<substring>} (matched against {@code "group :: name"},
     * case-insensitive), e.g. {@code ./gradlew test -Dverify.only='matrix sum'}.
     */
    @TestFactory
    List<DynamicTest> verificationCases() {
        String only = (System.getProperty('verify.only') ?: '').trim().toLowerCase()
        List<DynamicTest> tests = []
        CASES.eachWithIndex { Map c, int i ->
            String label = "${c.group} :: ${c.name}"
            if (only && !label.toLowerCase().contains(only)) return
            tests << dynamicTest(label) {
                Map r = evaluate(c, "Case${i}")
                Assertions.assertTrue((boolean) r.ok, (String) r.detail)
            }
        }
        tests
    }

    static void main(String[] args) {
        int passed = 0, failed = 0
        String currentGroup = null
        CASES.eachWithIndex { Map c, int i ->
            if (c.group != currentGroup) {
                currentGroup = c.group
                println "\n── ${currentGroup} ${'─' * (60 - currentGroup.size())}"
            }
            Map r = evaluate(c, "Case${i}")
            if (r.ok) {
                passed++
                println "  [PASS] ${c.name}"
                // VERIFY_VERBOSE=1 ./gradlew verify  → show the diagnostic text of refuted cases
                if (System.getenv('VERIFY_VERBOSE') && c.ok != true && r.errors) {
                    println "         ${((List) r.errors).join('\n').replaceAll('\n', '\n         ')}"
                }
            } else {
                failed++
                println "  [FAIL] ${c.name}\n      ${r.detail}"
            }
        }
        println "\n${'═' * 64}"
        println "${passed} passed, ${failed} failed, ${CASES.size()} total"
        if (System.getenv('VERIFY_CACHE_STATS') == '1') {
            long hits   = Z3Backend.vcCacheHits()
            long misses = Z3Backend.vcCacheMisses()
            long total  = hits + misses
            int  size   = Z3Backend.vcCacheSize()
            String pct  = total == 0 ? '—' : sprintf('%.1f%%', 100.0d * hits / total)
            println "VC cache: ${hits} hits / ${misses} misses (${pct} hit rate), ${size} entries"
        }
        if (failed > 0) System.exit(1)
    }
}
