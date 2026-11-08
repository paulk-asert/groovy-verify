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

/** 'P536 library receivers' — Phase 536: a call with no body or contract to read, on an object of a library type
 *  with fields (`Random`, `java.sql.Connection`, slf4j's `Logger`), havocked only that object's fields (Phase 45/363's
 *  fallback, built for the unit's own classes). The object may be any subclass compiled anywhere, whose method writes
 *  anything it reaches, so the call is now unmodelled, loudly. Each false-proof case below verified before. */
class G578_p536_library_receivers {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'An unresolved call on a library object may run an override compiled anywhere: unmodelled, loudly, where it havocked only the object\'s fields.'

    static final String EVIL_RANDOM = '''
class Evil extends Random {
    void setSeed(long s) { C.total = 0 }
}'''

    static final List<Map> CASES = [
        [group: 'P536 library receivers', name: 'Random.setSeed on a parameter, an override resetting a static: no longer proved',
         expect: ["call 'rnd.setSeed(1)' resolves to no body or contract", "'rnd' is a Random, a library type"],
         src: tc('''class C {
                        static int total
                        @Requires({ rnd != null })
                        @Ensures({ total == old.total + 1 })
                        void inc(Random rnd) { total++; rnd.setSeed(1L) }
                    }''') + EVIL_RANDOM],
        [group: 'P536 library receivers', name: '… nor with no subclass in the unit (one may be compiled anywhere)',
         expect: ["call 'rnd.setSeed(1)' resolves to no body or contract", 'a library type'],
         src: tc('''class C {
                        static int total
                        @Requires({ rnd != null })
                        @Ensures({ total == old.total + 1 })
                        void inc(Random rnd) { total++; rnd.setSeed(1L) }
                    }''')],
        [group: 'P536 library receivers', name: 'an override reaching this object\'s field through a reference it holds',
         expect: ["call 'rnd.setSeed(1)' resolves to no body or contract", 'a library type'],
         src: tc('''class C {
                        int count
                        @Requires({ rnd != null })
                        @Ensures({ count == old.count + 1 })
                        void inc(Random rnd) { count++; rnd.setSeed(1L) }
                    }
                    class Evil extends Random {
                        C target
                        void setSeed(long s) { if (target != null) target.count = 0 }
                    }''')],
        [group: 'P536 library receivers', name: 'an interface whose only fields are constants (java.sql.Connection)',
         expect: ["call 'conn.commit()' resolves to no body or contract", "'conn' is a Connection, a library type"],
         src: tc('''class C {
                        static int total
                        @Requires({ conn != null })
                        @Ensures({ total == old.total + 1 })
                        void inc(java.sql.Connection conn) { total++; conn.commit() }
                    }''')],
        [group: 'P536 library receivers', name: 'a library object held in a field',
         expect: ["call 'rnd.setSeed(1)' resolves to no body or contract", 'a library type'],
         src: tc('''class C {
                        static int total
                        Random rnd
                        @Requires({ rnd != null })
                        @Ensures({ total == old.total + 1 })
                        void inc() { total++; rnd.setSeed(1L) }
                    }''') + EVIL_RANDOM],
        [group: 'P536 library receivers', name: 'a logger the logging recogniser declines (the unit implements Logger)',
         expect: ["call 'log.info(bumped)' resolves to no body or contract", "'log' is a Logger, a library type"],
         src: HDR + 'import org.slf4j.Logger\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" + '''class C {
    Logger log
    int count
    @Requires({ log != null })
    @Ensures({ count == old.count + 1 })
    void inc() { count++; log.info('bumped') }
}
abstract class Sneaky implements Logger { }'''],
        [group: 'P536 library receivers', name: 'a field-less library interface still skips as before (Appendable)',
         expect: "standalone call 'sink.append(x)' has no usable @Ensures",
         src: tc('''class C {
                        static int total
                        @Requires({ sink != null })
                        @Ensures({ total == old.total + 1 })
                        void inc(Appendable sink) { total++; sink.append('x') }
                    }''')],

        // ---------- controls: the unit's own classes keep their framing ----------
        [group: 'P536 library receivers', name: 'a call on an object of a class compiled here is framed by its body', ok: true,
         src: tc('''class C {
                        int count
                        @Requires({ b != null })
                        @Ensures({ count == old.count + 1 })
                        void inc(Box b) { count++; b.poke() }
                    }
                    final class Box {
                        int n
                        void poke() { n = n + 1 }
                    }''')],
        [group: 'P536 library receivers', name: '… and a wrong claim past it still refutes',
         expect: ['Cannot prove postcondition', 'fails on'],
         src: tc('''class C {
                        int count
                        @Requires({ b != null })
                        @Ensures({ count == old.count + 2 })
                        void inc(Box b) { count++; b.poke() }
                    }
                    final class Box {
                        int n
                        void poke() { n = n + 1 }
                    }''')],
    ]
}
