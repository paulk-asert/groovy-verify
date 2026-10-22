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
import org.codehaus.groovy.control.CompilationUnit
import org.codehaus.groovy.control.CompilerConfiguration
import org.codehaus.groovy.control.MultipleCompilationErrorsException
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

import static org.junit.jupiter.api.Assertions.*

/**
 * Phase 364 — relied skeletons across two compilation units, as a library and an app are built: unit 1, a library
 * checked with {@code closedWorld: true}, is compiled to a classes directory and writes the contracts its proofs relied
 * on to {@code META-INF/groovy-verify/relied/}; unit 2 is compiled against that directory, and its checked overrides
 * are held to them (Phase 363). The case harness compiles one source in memory, so this is a JUnit test.
 */
class ReliedSkeletonTest {

    static final String HDR = 'import groovy.transform.TypeChecked\nimport groovy.contracts.*\n'
    static final String CHECKED = "@TypeChecked(extensions = 'verification.VerifyChecker')\n"

    static final String LIBRARY = '''package lib
        import groovy.transform.TypeChecked
        import groovy.contracts.*
        @TypeChecked(extensions = 'verification.VerifyChecker(closedWorld: true)')
        class Stats {
            @Requires({ c != null && c.count == 0 && c.total == 7 })
            @Ensures({ c.total == 7 })
            static void bump(Counter c) { c.incr() }
        }
        @TypeChecked(extensions = 'verification.VerifyChecker(closedWorld: true)')
        class Base {
            int get() { 0 }
            @Ensures({ result == 0 })
            int foo() { get() }
        }
        @TypeChecked(extensions = 'verification.VerifyChecker(closedWorld: true)')
        class Folded {
            int get() { int x = 0; return x }
            @Ensures({ result == 0 })
            int foo() { get() }
        }
        class Counter { int count; int total; void incr() { count = count + 1 } }
        '''.stripIndent()

    static File libClasses

    static List<String> compile(File out, List<File> classpath, String name, String src) {
        CompilerConfiguration cfg = new CompilerConfiguration()
        cfg.targetDirectory = out
        cfg.classpathList = classpath*.path
        GroovyClassLoader gcl = new GroovyClassLoader(Thread.currentThread().contextClassLoader, cfg)
        CompilationUnit cu = new CompilationUnit(cfg, null, gcl)
        cu.addSource(name, src)
        try {
            cu.compile()
            return []
        } catch (MultipleCompilationErrorsException e) {
            return e.errorCollector.errors.collect { err ->
                err instanceof org.codehaus.groovy.control.messages.SyntaxErrorMessage ? err.cause.message : err.toString()
            }
        } finally {
            gcl.close()
        }
    }

    @BeforeAll
    static void buildLibrary() {
        libClasses = File.createTempDir('verify-lib', '')
        List<String> errors = compile(libClasses, [], 'Library.groovy', LIBRARY)
        assertEquals([], errors, 'the closed-world library verifies')
    }

    static String relied(String fqn) {
        File f = new File(libClasses, "META-INF/groovy-verify/relied/${fqn}.groovy")
        assertTrue(f.isFile(), "a relied skeleton is written for ${fqn}")
        f.getText('UTF-8')
    }

    static List<String> app(String name, String src) {
        compile(File.createTempDir('verify-app', ''), [libClasses], name + '.groovy', src)
    }

    @Test
    void theLibraryWritesWhatItsProofsReliedOn() {
        String counter = relied('lib.Counter')
        assertTrue(counter.contains('@Modifies({ [this.count] }) void incr() {}'), counter)
        assertTrue(counter.contains('@Ensures({ result == (total) }) @Modifies({ [] }) int getTotal() {}'), counter)
        String base = relied('lib.Base')
        assertTrue(base.contains('@Ensures({ result == (0) }) @Modifies({ [] }) int get() {}'), base)
        assertFalse(new File(libClasses, 'META-INF/groovy-verify/relied/lib.Stats.groovy').exists(),
            'nothing relied on Stats: no file')
    }

    @Test
    void anOverrideWritingMoreIsAnError() {
        List<String> errors = app('Noisy', HDR + CHECKED + 'class Noisy extends lib.Counter { void incr() { total = total + 1; count = count + 1 } }')
        assertTrue(errors.any { it.contains("Method 'incr' writes 'total', which is not in its @Modifies clause [count]") &&
            it.contains('inherited from the skeleton of lib.Counter#incr') }, errors.join('\n'))
    }

    @Test
    void anOverrideWithinTheFrameCompiles() {
        assertEquals([], app('Ok', HDR + CHECKED + 'class Ok extends lib.Counter { void incr() { count = count + 2 } }'))
    }

    @Test
    void anOverrideChangingAReliedValueIsAnError() {
        List<String> errors = app('Offset', HDR + CHECKED + 'class Offset extends lib.Base { int get() { 1 } }')
        assertTrue(errors.any { it.contains('Cannot prove postcondition of get') }, errors.join('\n'))
    }

    @Test
    void aGetterShadowingAReliedFieldIsAnError() {
        List<String> errors = app('Shadow', HDR + CHECKED + 'class Shadow extends lib.Counter { int getTotal() { 42 } }')
        assertTrue(errors.any { it.contains('Cannot prove postcondition of getTotal') }, errors.join('\n'))
    }

    @Test
    void aValueNoExpressionStatesIsNoOverride() {
        String folded = relied('lib.Folded')
        assertTrue(folded.contains('@NoOverride @Modifies({ [] }) int get() {}'), folded)
        List<String> errors = app('Changed', HDR + CHECKED + 'class Changed extends lib.Folded { int get() { 1 } }')
        assertTrue(errors.any { it.contains("Method 'get' overrides lib.Folded#get, whose body verified code compiled with closedWorld: true used as its value") },
            errors.join('\n'))
        assertEquals([], app('Delegating', HDR + CHECKED + 'class Delegating extends lib.Folded { int get() { super.get() } }'))
    }

    /** The residual: a subclass compiled WITHOUT the checker is not held to anything — the reliance is ledgered in the
     *  library's build and stated in its relied skeleton, but nothing enforces it here. */
    @Test
    void anUncheckedSubclassIsNotChecked() {
        assertEquals([], app('Loose', HDR + 'class Loose extends lib.Counter { void incr() { total = total + 1 } }'))
    }
}
