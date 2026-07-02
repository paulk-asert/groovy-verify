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

/** 'P29 enum-sets' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G067_p29_enum_sets {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A finite-state-machine\'s reachable states as an enum/ordinal set: full coverage entails every state, partial coverage cannot.'

    static final List<Map> CASES = [

        // ---------- Phase 29: Sets.boundedBy / Sets.boundedCount generalised to enum-element sets ----------
        // FSM via ordinals — the workaround pattern still works.
        [group: 'P29 enum-sets', name: 'FSM via Set<Integer> ordinals: full coverage verifies', ok: true,
         src: tc('''class FSM {
                        enum State { IDLE, RUNNING, DONE }
                        Set<Integer> handled
                        @Requires({ Sets.boundedCount(handled, State.values().length) == State.values().length })
                        @Ensures({ (0..<State.values().length).every { it in handled } })
                        boolean allHandled() { true }
                    }''')],
        // Direct Set<State> spelling — the headline Phase 29 capability. Sets.boundedCount(s, N) where
        // N is the enum's domain size proves every state is handled, via the iff axiom asserted
        // at setFor time.
        [group: 'P29 enum-sets', name: 'FSM via Set<State>: full coverage entails every state', ok: true,
         src: tc('''class FSM {
                        enum State { IDLE, RUNNING, DONE }
                        Set<State> handled
                        @Requires({ Sets.boundedCount(handled, State.values().length) == State.values().length })
                        @Ensures({ State.IDLE in handled && State.RUNNING in handled && State.DONE in handled })
                        boolean allHandled() { true }
                    }''')],
        // Soundness: without the full-coverage @Requires, the full-state @Ensures must refute.
        [group: 'P29 enum-sets', name: 'partial coverage cannot prove every state',
         expect: 'Cannot prove postcondition',
         src: tc('''class FSM {
                        enum State { IDLE, RUNNING, DONE }
                        Set<State> handled
                        @Ensures({ State.IDLE in handled && State.RUNNING in handled && State.DONE in handled })
                        boolean allHandled() { true }
                    }''')],
        // Pigeonhole: card(Set<Enum>) <= enum.values().length asserted at setFor time, so a
        // postcondition relying on it (s.size() <= 3 for a 3-state enum) verifies without an
        // explicit Sets.boundedBy clause.
        [group: 'P29 enum-sets', name: 'pigeonhole bound is automatic for enum sets', ok: true,
         src: tc('''class FSM {
                        enum State { IDLE, RUNNING, DONE }
                        @Ensures({ s.size() <= 3 })
                        static int f(Set<State> s) { 0 }
                    }''')],
        // Sets.boundedBy over Set<Enum> with matching n verifies (pigeonhole + iff already asserted).
        [group: 'P29 enum-sets', name: 'Sets.boundedBy matching enum size verifies', ok: true,
         src: tc('''class FSM {
                        enum State { IDLE, RUNNING, DONE }
                        @Requires({ Sets.boundedBy(s, State.values().length) })
                        @Ensures({ s.size() <= State.values().length })
                        static int f(Set<State> s) { 0 }
                    }''')],
        // Sets.boundedBy with NON-matching n on enum set: still skips (no partial-ordering meaning).
        [group: 'P29 enum-sets', name: 'Sets.boundedBy non-matching n on enum set skipped',
         expect: 'outside fragment',
         src: tc('''class FSM {
                        enum State { IDLE, RUNNING, DONE }
                        @Requires({ Sets.boundedBy(s, 2) })
                        @Ensures({ s.size() <= 2 })
                        static int f(Set<State> s) { 0 }
                    }''')],
    ]
}
