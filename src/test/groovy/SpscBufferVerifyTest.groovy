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
import org.junit.jupiter.api.Test

import static org.junit.jupiter.api.Assertions.assertTrue
import static org.junit.jupiter.api.Assertions.fail

/**
 * Proves the "same source" claim: the EXACT bytes of {@code src/concurrent/.../SpscBuffer.groovy} — the buffer
 * Lincheck model-checks — also verify under groovy-verify. The only change is enabling the extension on the
 * {@code @CompileStatic} already present (the Lincheck build leaves it plain; here we add the checker). The class's
 * {@code @Invariant} is then proved at compile time (`items[t % capacity]` in bounds, the occupancy invariant
 * preserved by offer/poll, established by the constructor). The Lincheck build instruments the same file with
 * groovy-contracts' assertions disabled ({@code -da}); see {@code examples/concurrency/README.md}.
 */
class SpscBufferVerifyTest {

    private static String withChecker(String src) {
        // The file carries a bare `@CompileStatic` (clean bytecode for Lincheck); here we apply the verifier.
        src.replace('@CompileStatic\n', "@CompileStatic(extensions = 'verification.VerifyChecker')\n")
    }

    private static void compile(String src, String name) {
        def gcl = new GroovyClassLoader(SpscBufferVerifyTest.class.classLoader)
        try {
            gcl.parseClass(src, name)
        } finally {
            try { gcl.close() } catch (ignored) {}
        }
    }

    @Test
    void theActualSpscBufferSourceVerifies() {
        File f = new File('src/concurrent/groovy/concurrent/SpscBuffer.groovy')
        assertTrue(f.exists(), "expected $f to exist")
        try {
            compile(withChecker(f.getText('UTF-8')), 'SpscBuffer.groovy')
        } catch (MultipleCompilationErrorsException e) {
            fail("SpscBuffer.groovy did not verify under groovy-verify:\n" + e.message)
        }
    }

    @Test
    void theActualBufferSourceVerifies() {
        // The §VII rely/guarantee + info-flow Buffer, the same file Lincheck model-checks: groovy-verify proves the
        // bounds @Invariant under each thread's @UnderRely interference AND the no-leak info-flow discipline.
        File f = new File('src/concurrent/groovy/concurrent/Buffer.groovy')
        assertTrue(f.exists(), "expected $f to exist")
        try {
            compile(withChecker(f.getText('UTF-8')), 'Buffer.groovy')
        } catch (MultipleCompilationErrorsException e) {
            fail("Buffer.groovy did not verify under groovy-verify:\n" + e.message)
        }
    }

    @Test
    void refuteControl_brokenInvariantIsRejected() {
        // Same annotations/shape, but an unguarded mutator overflows the occupancy invariant — must refute, proving
        // the checker really ran on this @CompileStatic class (a clean compile would mean it silently did nothing).
        String broken = '''
            import groovy.transform.CompileStatic
            import groovy.contracts.Invariant
            @CompileStatic(extensions = 'verification.VerifyChecker')
            @Invariant({ capacity > 0 && items.length == capacity && 0 <= head && head <= tail && tail - head <= capacity })
            class Broken {
                private final int[] items = new int[1]
                private final int capacity = 1
                private volatile int head = 0
                private volatile int tail = 0
                void bump() { tail = tail + 1 }
            }'''
        try {
            compile(broken, 'Broken.groovy')
            fail('expected the broken invariant to refute, but it compiled cleanly')
        } catch (MultipleCompilationErrorsException e) {
            assertTrue(e.message.contains('Cannot prove class invariant'),
                "expected a class-invariant refutation, got:\n" + e.message)
        }
    }
}
