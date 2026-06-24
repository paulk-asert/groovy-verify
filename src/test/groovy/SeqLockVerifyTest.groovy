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
 * Rung 1 of the seqlock's three-rung story (see {@code CONCURRENCY.md}). The EXACT bytes of
 * {@code src/concurrent/.../SeqLock.groovy} — the source Lincheck model-checks and jcstress stress-runs — also verify
 * under groovy-verify. The class's implication-guarded {@code @Invariant({ seq % 2 == 0 ==> x == y })} is the novel
 * piece: {@code write} re-establishes {@code x == y} before republishing, and a successful {@code tryRead} returns a
 * consistent snapshot. The refute cases below give the proof teeth — break the protocol and it must NOT compile.
 */
class SeqLockVerifyTest {

    private static String withChecker(String src) {
        // The file carries a bare `@CompileStatic` (clean bytecode for Lincheck/jcstress); here we apply the verifier.
        src.replace('@CompileStatic\n', "@CompileStatic(extensions = 'verification.VerifyChecker')\n")
    }

    private static void compile(String src, String name) {
        def gcl = new GroovyClassLoader(SeqLockVerifyTest.class.classLoader)
        try {
            gcl.parseClass(src, name)
        } finally {
            try { gcl.close() } catch (ignored) {}
        }
    }

    @Test
    void theActualSeqLockSourceVerifies() {
        // The same file the runtime rungs run: groovy-verify discharges the writer protocol — the implication-guarded
        // class @Invariant({ seq % 2 == 0 ==> x == y }) — over this exact source (write re-establishes x == y before
        // it republishes). The reader's result-bearing @Ensures can't ride this bare runtime compile, so it is proved
        // over tryRead's same body in readerConsistentSnapshotVerifies below.
        File f = new File('src/concurrent/groovy/concurrent/SeqLock.groovy')
        assertTrue(f.exists(), "expected $f to exist")
        try {
            compile(withChecker(f.getText('UTF-8')), 'SeqLock.groovy')
        } catch (MultipleCompilationErrorsException e) {
            fail("SeqLock.groovy did not verify under groovy-verify:\n" + e.message)
        }
    }

    @Test
    void readerConsistentSnapshotVerifies() {
        // The reader obligation, over the EXACT body of SeqLock.tryRead: a successful optimistic read (seq unchanged
        // and even) returns a consistent snapshot. The proof leans on the guarded class @Invariant — under the guard
        // `s1 == s2 && s1 % 2 == 0` the entry invariant gives x == y, so result[0] == result[1].
        String reader = '''
            import groovy.transform.CompileStatic
            import groovy.transform.stc.POJO
            import groovy.contracts.Invariant
            import groovy.contracts.Ensures
            @CompileStatic(extensions = 'verification.VerifyChecker')
            @POJO
            @Invariant({ seq % 2 == 0 ==> x == y })
            class SeqLockReader {
                private volatile int seq = 0
                private int x = 0
                private int y = 0
                @Ensures({ result == null || result[0] == result[1] })
                List<Integer> tryRead() {
                    int s1 = seq
                    int rx = x
                    int ry = y
                    int s2 = seq
                    if (s1 == s2 && s1 % 2 == 0) return [rx, ry]
                    return null
                }
            }'''
        try {
            compile(reader, 'SeqLockReader.groovy')
        } catch (MultipleCompilationErrorsException e) {
            fail("the consistent-snapshot reader did not verify:\n" + e.message)
        }
    }

    @Test
    void writerThatSkipsRepublishConsistencyRefutes() {
        // Teeth, writer side: republish (bump seq back to even) WITHOUT restoring x == y. The guarded invariant
        // `seq even ==> x == y` must refute — a clean compile would mean the field write was silently dropped.
        String broken = '''
            import groovy.transform.CompileStatic
            import groovy.transform.stc.POJO
            import groovy.contracts.Invariant
            @CompileStatic(extensions = 'verification.VerifyChecker')
            @POJO
            @Invariant({ seq % 2 == 0 ==> x == y })
            class SeqLockBadWriter {
                private volatile int seq = 0
                private int x = 0
                private int y = 0
                void write(int v) {
                    seq = seq + 1
                    x = v
                    // BUG: forgot `y = v` — the record is left torn when seq goes back to even
                    seq = seq + 1
                }
            }'''
        try {
            compile(broken, 'SeqLockBadWriter.groovy')
            fail('expected the un-restored writer to refute, but it compiled cleanly (field write ignored?)')
        } catch (MultipleCompilationErrorsException e) {
            assertTrue(e.message.contains('Cannot prove class invariant'),
                "expected a class-invariant refutation, got:\n" + e.message)
        }
    }

    @Test
    void readerThatSkipsParityCheckRefutes() {
        // Teeth, reader side: validate only that seq is UNCHANGED (s1 == s2) but NOT that it is even. A caller can
        // then observe a snapshot taken while a write was in progress (seq odd), where x and y need not agree — so
        // the consistent-snapshot @Ensures must refute.
        String broken = '''
            import groovy.transform.CompileStatic
            import groovy.transform.stc.POJO
            import groovy.contracts.Invariant
            import groovy.contracts.Ensures
            @CompileStatic(extensions = 'verification.VerifyChecker')
            @POJO
            @Invariant({ seq % 2 == 0 ==> x == y })
            class SeqLockBadReader {
                private volatile int seq = 0
                private int x = 0
                private int y = 0
                @Ensures({ result == null || result[0] == result[1] })
                List<Integer> tryRead() {
                    int s1 = seq
                    int rx = x
                    int ry = y
                    int s2 = seq
                    if (s1 == s2) return [rx, ry]   // BUG: dropped the `s1 % 2 == 0` parity check
                    return null
                }
            }'''
        try {
            compile(broken, 'SeqLockBadReader.groovy')
            fail('expected the parity-skipping reader to refute, but it compiled cleanly')
        } catch (MultipleCompilationErrorsException e) {
            assertTrue(e.message.contains('Cannot prove') || e.message.contains('postcondition'),
                "expected a postcondition refutation, got:\n" + e.message)
        }
    }
}
