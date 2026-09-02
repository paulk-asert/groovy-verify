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

/**
 * 'P282 CREW' — Kerridge c13's concurrent-read / exclusive-write discipline, made checkable. c13 hands one
 * shared map to N readers and M writers under a PAR: correct not by separation (which Phase 240 enforces
 * everywhere else) but by a lock discipline. Groovy spells that discipline DECLARATIVELY, with
 * `@WithReadLock` / `@WithWriteLock` around a `ReentrantReadWriteLock` — and being declarative is what makes
 * it checkable, because the annotation says which half a method takes.
 *
 * <p>The lock transforms stay TRANSPARENT to the prover (Phase 115): nothing here claims a lock makes
 * anything thread-safe, and the check-then-act case still proves the same invariant with and without one.
 * What this group adds are the two ways of making the discipline a fiction — a write taken under the READ
 * lock, and the two halves taken on DIFFERENT locks — both syntactic, both refused.
 */
class G337_p282_crew {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 282 CREW (Kerridge c13): the concurrent-read / exclusive-write lock discipline, checked where Groovy states it declaratively. `@WithReadLock` / `@WithWriteLock` remain TRANSPARENT to the prover (Phase 115 — the class @Invariant is the monitor invariant, and the same invariant proves with or without the lock), so nothing here claims thread-safety the verifier cannot see; what is refused are the two syntactic ways the discipline becomes a fiction. A WRITE under the read lock races every concurrent reader — the one mistake CREW exists to prevent — and is refused naming the field. Read and write halves naming DIFFERENT lock fields exclude nothing, and are refused naming both. A write-locked writer beside read-locked readers is the correct shape and stays clean, as does a read-locked method writing only its own locals.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    /** The two lock transforms, imported for this group only — adding them to the shared HDR would shift
     *  every case's source line numbers, and the doc pins diagnostics that quote them (Phase 277's lesson). */
    static final String LOCKS = 'import groovy.transform.WithReadLock\nimport groovy.transform.WithWriteLock\n'

    private static String tcLocks(String classText) {
        HDR + LOCKS + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" + classText.stripIndent()
    }

    static final List<Map> CASES = [
        // c13's shape: one shared object, concurrent readers, an exclusive writer. The discipline holds,
        // and `refute:` pins that the checker does not cry wolf over the correct arrangement.
        [group: 'P282 CREW', name: 'concurrent readers and an exclusive writer: the discipline holds', ok: true,
         refute: ['Write under a read lock', 'Read and write locks differ'],
         src: tcLocks("""class Db {
                        private int value = 0
                        @WithWriteLock
                        void put(int v) { value = v }
                        @WithReadLock
                        int get() { return value }
                    }
                    class C {
                        static int crew() {
                            Db db = new Db()
                            def t1 = async { db.put(5) }
                            def t2 = async { db.get() }
                            def r = await(t1, t2)
                            return 0
                        }
                    }""")],
        // The mistake CREW exists to prevent: a write taken under the read lock, which by design admits
        // concurrent readers — so the write races every one of them.
        [group: 'P282 CREW', name: 'a write under the read lock is refused', expect: 'Write under a read lock',
         src: tcLocks("""class Db2 {
                        private int value = 0
                        @WithReadLock
                        void bump() { value = value + 1 }
                        @WithReadLock
                        int get() { return value }
                    }
                    class C {
                        static int crewBug() {
                            Db2 db = new Db2()
                            def t1 = async { db.bump() }
                            def t2 = async { db.get() }
                            def r = await(t1, t2)
                            return 0
                        }
                    }""")],
        // …including the increment forms, which are writes however they are spelled.
        [group: 'P282 CREW', name: 'an increment under the read lock is a write too', expect: 'Write under a read lock',
         src: tcLocks("""class Db3 {
                        private int value = 0
                        @WithReadLock
                        void bump() { value++ }
                    }
                    class C {
                        static int c3() { Db3 d = new Db3(); d.bump(); return 0 }
                    }""")],
        // The halves on different locks: a reader and a writer then hold unrelated locks and exclude nothing.
        [group: 'P282 CREW', name: 'read and write halves on different locks are refused', expect: 'Read and write locks differ',
         src: tcLocks("""class Db4 {
                        private final java.util.concurrent.locks.ReentrantReadWriteLock lockA = new java.util.concurrent.locks.ReentrantReadWriteLock()
                        private final java.util.concurrent.locks.ReentrantReadWriteLock lockB = new java.util.concurrent.locks.ReentrantReadWriteLock()
                        private int value = 0
                        @WithWriteLock('lockA')
                        void put(int v) { value = v }
                        @WithReadLock('lockB')
                        int get() { return value }
                    }
                    class C {
                        static int c4() { Db4 d = new Db4(); d.put(1); return d.get() }
                    }""")],
        // Not over-eager: a read-locked method may write its OWN locals all it likes.
        [group: 'P282 CREW', name: 'a read-locked method writing only locals is fine', ok: true,
         refute: 'Write under a read lock',
         src: tcLocks("""class Db5 {
                        private int value = 7
                        @WithReadLock
                        int scaled(int k) {
                            int acc = 0
                            acc = acc + value * k
                            return acc
                        }
                    }
                    class C {
                        static int c5() { Db5 d = new Db5(); return d.scaled(2) }
                    }""")],
    ]
}
