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

/** 'P117 agent-invariant' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G228_p117_agent_invariant {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'An Agent/actor\'s class @Invariant is the serialized monitor invariant each handler preserves (bounded-buffer occupancy); an unguarded add refutes.'

    static final List<Map> CASES = [
        // ---------- P117 agents/actors: the monitor invariant via serialization ----------
        // The lock trick spans paradigms. An Agent/Actor is a monitor whose mutual exclusion comes from
        // processing one message at a time, not from a lock — so the class @Invariant is again the monitor
        // invariant, and each handler is verified to preserve it, with NO lock annotation. The structural
        // half we assume is the runtime's serialization (not mutual exclusion). A bounded buffer whose
        // occupancy invariant an Agent maintains under concurrent producers/consumers:
        [group: 'P117 agent-invariant', name: 'bounded buffer occupancy invariant (no lock)', ok: true,
         src: tc('''@Invariant({ 0 <= count && count <= capacity })
                    class Buffer {
                        int count
                        int capacity
                        @Requires({ count < capacity })
                        @Ensures({ count == old.count + 1 })
                        void add() { count = count + 1 }
                        @Requires({ count > 0 })
                        @Ensures({ count == old.count - 1 })
                        void remove() { count = count - 1 }
                    }''')],
        // Refute: an unguarded add lets a handler break the occupancy invariant — caught.
        [group: 'P117 agent-invariant', name: 'unguarded add breaks occupancy invariant', expect: 'Cannot prove class invariant',
         src: tc('''@Invariant({ 0 <= count && count <= capacity })
                    class Buffer {
                        int count
                        int capacity
                        @groovy.transform.Synchronized
                        void add() { count = count + 1 }
                    }''')],
        // The Agent update-function model: `agent.send { inc(it) }` applies a pure update atomically; the
        // update is proven to preserve the agent's invariant (here, non-negativity).
        [group: 'P117 agent-invariant', name: 'agent update function preserves the invariant', ok: true,
         src: tc('''class Counter {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n + 1 && result >= 0 })
                        static int inc(int n) { n + 1 }
                        @Requires({ n > 0 })
                        @Ensures({ result == n - 1 && result >= 0 })
                        static int dec(int n) { n - 1 }
                    }''')],
    ]
}
