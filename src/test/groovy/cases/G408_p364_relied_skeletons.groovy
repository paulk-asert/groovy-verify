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
 * 'P364 a library writes what its proofs relied on' — slice 3b of the open-world plan. Under `closedWorld: true`
 * (Phase 362) each reliance on a member of a class compiled in the same unit is now kept as a contract, and written
 * with the classes to `META-INF/groovy-verify/relied/<fqn>.groovy` — a frame as `@Modifies`, a value as
 * `@Ensures({ result == … })` (or `@NoOverride` when no single expression states it), a field read as its getter's
 * `@Ensures` — the skeletons a later unit's checked overrides are held to (Phase 363). The two-unit flow is
 * ReliedSkeletonTest's; these cases pin the in-memory side: with no output directory nothing can be written, so each
 * class's reliances are ledgered as unwritten; and a relied `@NoOverride` holds an override unless it delegates.
 */
class G408_p364_relied_skeletons {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 364 a library writes what its proofs relied on: under closedWorld: true the reliances on a class compiled in the same unit are written to META-INF/groovy-verify/relied/<fqn>.groovy with the classes — a frame as @Modifies, a value as @Ensures (or @NoOverride), a field read as its getter\'s contract — for a later unit\'s checked overrides; an in-memory compile, with nowhere to write, ledgers them as unwritten, and a relied @NoOverride holds an override unless it delegates.'

    static final String NO_OVERRIDE = '''package fixture
                    class LibCounter { @NoOverride @Modifies({ [] }) int get() {} }'''

    static final List<Map> CASES = [

        [group: "P364 a library writes what its proofs relied on", name: "an in-memory compile ledgers its reliances as unwritten", ok: true,
         trusted: "[closed world] Counter — relied skeleton not written: the compilation has no output directory",
         src: tcw('''class A {
                        @Requires({ c != null && c.count == 0 && c.total == 7 })
                        @Ensures({ c.total == 7 })
                        static void g(Counter c) { c.incr() }
                    }
                    class Counter { int count; int total; void incr() { count = count + 1 } }''')],
        [group: "P364 a library writes what its proofs relied on", name: "… and one relying on nothing ledgers nothing", ok: true,
         untrusted: "relied skeleton not written",
         src: tcw('''final class A {
                        @Requires({ c != null && c.count == 0 && c.total == 7 })
                        @Ensures({ c.total == 7 })
                        static void g(Counter c) { c.incr() }
                    }
                    final class Counter { int count; int total; void incr() { count = count + 1 } }''')],
        [group: "P364 a library writes what its proofs relied on", name: "a relied @NoOverride holds an override",
         expect: "Method 'get' overrides fixture.LibCounter#get, whose body verified code compiled with closedWorld: true used as its value",
         relied: ['fixture.LibCounter': NO_OVERRIDE],
         src: tc('''class Changed extends fixture.LibCounter {
                        int get() { count + 1 }
                    }''')],
        [group: "P364 a library writes what its proofs relied on", name: "… unless it delegates", ok: true,
         relied: ['fixture.LibCounter': NO_OVERRIDE],
         src: tc('''class Proxy extends fixture.LibCounter {
                        int get() { super.get() }
                    }''')],
    ]
}
