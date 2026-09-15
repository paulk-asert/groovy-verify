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
 * 'P301 actor build sites' — WHERE the actor is built. Phase 299 read one constructor, which turned out to be a
 * blunt stand-in for the real question: how many places give the field a value. Counting answers it for every
 * shape at once — secondary constructors that CHAIN to the one that builds, a lifecycle {@code init()}, two
 * constructors of which only one ever runs, and a method that REPLACES the actor later. The last of those was a
 * soundness hole, not a reach gap: the initialiser's handler was being reported for an actor the class swaps out.
 */
class G351_p301_actor_build_sites {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 301 where the actor is built: every constructor and every method of the class is read for field assignments, not just a single constructor, and COUNTING decides which is the definition. One place — a secondary constructor chaining to the one that builds it, or a lifecycle init() — is a definition and is read. Two places are a disjunction (only one constructor runs per instance) or a replacement (a method swapping the actor out), and since no analysis of one of them alone would be sound, the field is not found at all. The replacement case was a soundness HOLE rather than a reach gap: before this, a class whose initialiser built a stashing actor and whose method replaced it with another had the initialiser\'s handler reported anyway.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final String STASHING = "Actor.reactor({ ActorContext<String> ctx, String m -> ctx.stash(); m } as ReactorHandler<String, String>)"
    static final String CLEAN = "Actor.reactor({ ActorContext<String> ctx, String m -> m } as ReactorHandler<String, String>)"

    static final List<Map> CASES = [
        // ── secondary constructors that CHAIN: one place builds the actor, so there is one definition.
        [group: 'P301 actor build sites', name: 'a secondary constructor chaining to the one that builds is read',
         expect: "Stashed messages are never replayed: actor 'gate' in the class C",
         src: tc("""class C {
                        Actor<String> gate
                        C() { this(5) }
                        C(int n) { gate = ${STASHING} }
                        void run() { gate.send('a') }
                    }""")],

        // ── a lifecycle method builds it: still one place, so still one definition.
        [group: 'P301 actor build sites', name: 'an actor built in a lifecycle init method is read',
         expect: "Stashed messages are never replayed: actor 'gate' in the class C",
         src: tc("""class C {
                        Actor<String> gate
                        void init() { gate = ${STASHING} }
                        void run() { gate.send('a') }
                    }""")],

        // ── two constructors that each build it: only one runs per instance, so neither can be analysed alone.
        [group: 'P301 actor build sites', name: 'two constructors that each build the actor are a disjunction, withheld', ok: true,
         refute: ['Stashed messages', 'Scheduled message', 'Unbounded stash'],
         src: tc("""class C {
                        Actor<String> gate
                        C() { gate = ${STASHING} }
                        C(int n) { gate = ${CLEAN} }
                        void run() { gate.send('a') }
                    }""")],

        // ── the SOUNDNESS half: a method that replaces the actor. Before Phase 301 the initialiser's handler
        //    was reported regardless, for an actor the class swaps out.
        [group: 'P301 actor build sites', name: 'an actor a method replaces later is withheld, not reported from its initialiser', ok: true,
         refute: ['Stashed messages', 'Scheduled message', 'Unbounded stash'],
         src: tc("""class C {
                        static Actor<String> gate = ${STASHING}
                        static void replace() { gate = ${CLEAN} }
                        static void run() { gate.send('a') }
                    }""")],

        // ── a method that only SENDS is not a build site: one definition remains.
        [group: 'P301 actor build sites', name: 'a method that only sends is not a build site',
         expect: "Stashed messages are never replayed: actor 'gate' in the class C",
         src: tc("""class C {
                        static Actor<String> gate = ${STASHING}
                        static void run() { gate.send('a') }
                        static void more() { gate.send('b'); gate.stop() }
                    }""")],

        // ── the whole stack still reaches it: a chained-constructor actor plays its @Protocol role.
        [group: 'P301 actor build sites', name: 'an actor built through a chained constructor plays its protocol role',
         expect: "actor 'gate' replies 'nak' to 'req' in phase 'the handler' after it receives 'req' where the protocol's reply is 'ack'",
         src: tc('''class C {
                        Actor<String> gate
                        C() { this(5) }
                        C(int n) {
                            gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                                if (m == 'req') { return 'nak' }
                                'done'
                            } as ReactorHandler<String, String>)
                        }
                        @Protocol({
                            req: client >> gate
                            ack: gate >> client
                            loop { cmd: client >> gate }
                        })
                        void run() {
                            gate.sendAndGet('req').get()
                            gate.send('cmd')
                        }
                    }''')],
    ]
}
