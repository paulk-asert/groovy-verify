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

/** 'P186 map-mutation' — map puts across every position (straight-line, loops, class invariants), pinned;
 *  the shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G267_p186_map_mutation {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Map mutation (m[k] = v and m.put(k, v)) modelled as value-array store + key-set add + cardinality law, now pinned across every position: straight-line bodies (read-back, sound key-set/size effects — a stale !containsKey or size claim refutes, containsKey after a put verifies), class @Invariant preservation over map FIELDS (a guarded mutator preserves, a clobber refutes, old.m[k] relates pre/post), and — new in Phase 186 — LOOP bodies (the store previously fell into the Int-indexed array path and sort-crashed to a loud skip on non-Int keys; now routed through the map key/value sorts with cross-key framing). The crown: Leino\'s ticket lock in his imperative MODEL-1 form — mutating request/enter/leave methods over map fields, the strengthened valid as the class @Invariant — verifies, and a dispenser that fails to advance refutes (the compile-time twin of the TLC TicketBad trace). Corrects the Phase-170 assumption that mutable-map-field framing was out of fragment.'

    static final List<Map> CASES = [

        // ---------- Phase 186: map mutation, pinned across every position ----------
        // Most of this surface already worked (value store + key-set add + cardinality law, shared by the
        // m[k] = v and m.put spellings) but was UNPINNED — which is why the Phase-170 ticket lock assumed
        // mutable-map-field framing was out of fragment and used Model-2. These pin it; the loop-body cases
        // pin the one genuine gap Phase 186 closed (the store sort-crashed on non-Int-keyed maps in loops).

        // Straight-line: store then read back.
        [group: 'P186 map-mutation', name: 'store read-back verifies', ok: true,
         src: tc('''class M {
                        enum State { IDLE, RUNNING, DONE }
                        @Requires({ m != null })
                        @Ensures({ result == 5 })
                        static int g(Map<State,Integer> m) { m[State.IDLE] = 5; return m[State.IDLE] }
                    }''')],
        [group: 'P186 map-mutation', name: 'wrong read-back refutes', expect: 'Cannot prove postcondition',
         src: tc('''class M {
                        enum State { IDLE, RUNNING, DONE }
                        @Requires({ m != null })
                        @Ensures({ result == 6 })
                        static int g(Map<State,Integer> m) { m[State.IDLE] = 5; return m[State.IDLE] }
                    }''')],
        // Key-set soundness: a put may ADD the key, so a stale !containsKey claim must refute…
        [group: 'P186 map-mutation', name: 'stale !containsKey after a put refutes (key-set is updated)', expect: 'Cannot prove postcondition',
         src: tc('''class M {
                        enum State { IDLE, RUNNING, DONE }
                        @Requires({ m != null && !m.containsKey(State.IDLE) })
                        @Ensures({ !m.containsKey(State.IDLE) })
                        static void g(Map<State,Integer> m) { m[State.IDLE] = 5 }
                    }''')],
        // …and the positive direction is complete, not just sound: containsKey after the put verifies.
        [group: 'P186 map-mutation', name: 'containsKey after a put verifies', ok: true,
         src: tc('''class M {
                        enum State { IDLE, RUNNING, DONE }
                        @Requires({ m != null })
                        @Ensures({ m.containsKey(State.IDLE) })
                        static void g(Map<State,Integer> m) { m[State.IDLE] = 5 }
                    }''')],
        // The size effect rides the cardinality law: a fresh-key put grows size, so a stale claim refutes.
        [group: 'P186 map-mutation', name: 'stale size after a fresh-key put refutes (cardinality law)', expect: 'Cannot prove postcondition',
         src: tc('''class M {
                        enum State { IDLE, RUNNING, DONE }
                        @Requires({ m != null && !m.containsKey(State.IDLE) && m.size() == 1 })
                        @Ensures({ m.size() == 1 })
                        static void g(Map<State,Integer> m) { m[State.IDLE] = 5 }
                    }''')],
        // The m.put(k, v) method spelling is the same mutation (the receiver dereference carries the usual
        // implicit nullity obligation, discharged by the guard).
        [group: 'P186 map-mutation', name: 'put() method form verifies', ok: true,
         src: tc('''class M {
                        enum State { IDLE, RUNNING, DONE }
                        @Requires({ m != null })
                        @Ensures({ result == 5 })
                        static int g(Map<State,Integer> m) { m.put(State.IDLE, 5); return m[State.IDLE] }
                    }''')],
        // Class @Invariant over a map FIELD: a guarded mutator preserves it (symbolic enum key — the store
        // at k must keep BOTH literal-key clauses, via the enum domain closure)…
        [group: 'P186 map-mutation', name: 'class @Invariant over a map field preserved by a mutator', ok: true,
         src: tc('''@Invariant({ m[State.IDLE] >= 0 && m[State.RUNNING] >= 0 })
                    class Counters {
                        enum State { IDLE, RUNNING, DONE }
                        Map<State,Integer> m
                        @Requires({ m[k] < 1000 })
                        void bump(State k) { m[k] = m[k] + 1 }
                    }''')],
        // …and a clobber refutes.
        [group: 'P186 map-mutation', name: 'map-field clobber refutes the class invariant', expect: 'Cannot prove class invariant',
         src: tc('''@Invariant({ m[State.IDLE] >= 0 && m[State.RUNNING] >= 0 })
                    class Counters {
                        enum State { IDLE, RUNNING, DONE }
                        Map<State,Integer> m
                        void clobber(State k) { m[k] = -1 }
                    }''')],
        // old.m[k] relates the pre- and post-state of a map-field mutator.
        [group: 'P186 map-mutation', name: 'old.m[k] across a map-field mutator', ok: true,
         src: tc('''@Invariant({ m[State.IDLE] >= 0 })
                    class Bumper {
                        enum State { IDLE, RUNNING, DONE }
                        Map<State,Integer> m
                        @Requires({ m[State.IDLE] < 1000 })
                        @Ensures({ m[State.IDLE] == old.m[State.IDLE] + 1 })
                        void bump() { m[State.IDLE] = m[State.IDLE] + 1 }
                    }''')],
        // LOOP bodies (the Phase-186 fix): a map put inside a @Invariant-carrying loop threads through the
        // loop — value store + key-set add in the map's own sorts, not the Int-indexed array path.
        [group: 'P186 map-mutation', name: 'map put inside a loop threads the invariant', ok: true,
         src: tc('''class L {
                        enum State { IDLE, RUNNING, DONE }
                        @Requires({ n >= 0 && m[State.IDLE] == 0 })
                        @Ensures({ result == n })
                        static int g(Map<State,Integer> m, int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && m[State.IDLE] == i })
                            @Decreases({ n - i })
                            while (i < n) { m[State.IDLE] = m[State.IDLE] + 1; i = i + 1 }
                            return m[State.IDLE]
                        }
                    }''')],
        [group: 'P186 map-mutation', name: 'loop map put with a wrong exit claim refutes', expect: 'Cannot prove postcondition',
         src: tc('''class L {
                        enum State { IDLE, RUNNING, DONE }
                        @Requires({ n >= 0 && m[State.IDLE] == 0 })
                        @Ensures({ result == n + 1 })
                        static int g(Map<State,Integer> m, int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && m[State.IDLE] == i })
                            @Decreases({ n - i })
                            while (i < n) { m[State.IDLE] = m[State.IDLE] + 1; i = i + 1 }
                            return m[State.IDLE]
                        }
                    }''')],
        // Cross-key framing inside the loop: storing at IDLE must not disturb DONE's invariant clause.
        [group: 'P186 map-mutation', name: 'loop map put frames the other keys', ok: true,
         src: tc('''class L {
                        enum State { IDLE, RUNNING, DONE }
                        @Requires({ n >= 0 && m[State.IDLE] == 0 && m[State.DONE] == 7 })
                        @Ensures({ result == 7 })
                        static int g(Map<State,Integer> m, int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && m[State.DONE] == 7 })
                            @Decreases({ n - i })
                            while (i < n) { m[State.IDLE] = m[State.IDLE] + 1; i = i + 1 }
                            return m[State.DONE]
                        }
                    }''')],
        // ---------- The crown: Leino's ticket lock, MODEL-1 (the imperative form) ----------
        // KRML260's first formalisation — mutating atomic-event METHODS over map fields, the strengthened
        // `valid` as the class @Invariant — verifies as written. Completes the Phase-170 arc with the model
        // it originally set aside: Model-2 (two-state predicates) was chosen on the assumption that mutable-
        // map-field framing was out of fragment; it wasn't (only unpinned). request = map put + dispenser
        // increment + state put; enter = guarded put; leave = display increment + put.
        [group: 'P186 map-mutation', name: 'Leino ticket lock, Model-1: all three events preserve valid', ok: true,
         src: tc('''@Invariant({ serving <= ticket &&
                        (cs[Phil.A] != CS.Thinking ==> (serving <= t[Phil.A] && t[Phil.A] < ticket)) &&
                        (cs[Phil.B] != CS.Thinking ==> (serving <= t[Phil.B] && t[Phil.B] < ticket)) &&
                        ((cs[Phil.A] != CS.Thinking && cs[Phil.B] != CS.Thinking) ==> t[Phil.A] != t[Phil.B]) &&
                        (cs[Phil.A] == CS.Eating ==> t[Phil.A] == serving) &&
                        (cs[Phil.B] == CS.Eating ==> t[Phil.B] == serving) })
                    class Ticket {
                        enum Phil { A, B }
                        enum CS { Thinking, Hungry, Eating }
                        int ticket
                        int serving
                        Map<Phil,CS> cs
                        Map<Phil,Integer> t
                        @Requires({ cs[p] == CS.Thinking })
                        void request(Phil p) { t[p] = ticket; ticket = ticket + 1; cs[p] = CS.Hungry }
                        @Requires({ cs[p] == CS.Hungry })
                        void enter(Phil p) { if (t[p] == serving) cs[p] = CS.Eating }
                        @Requires({ cs[p] == CS.Eating })
                        void leave(Phil p) { serving = serving + 1; cs[p] = CS.Thinking }
                    }''')],
        // Teeth — the compile-time twin of the TLC TicketBad trace: a dispenser that fails to advance hands
        // out duplicate tickets, and the invariant (its uniqueness/strict-bound conjuncts) refutes.
        [group: 'P186 map-mutation', name: 'Model-1 broken dispenser refutes the invariant', expect: 'Cannot prove class invariant',
         src: tc('''@Invariant({ serving <= ticket &&
                        (cs[Phil.A] != CS.Thinking ==> (serving <= t[Phil.A] && t[Phil.A] < ticket)) &&
                        (cs[Phil.B] != CS.Thinking ==> (serving <= t[Phil.B] && t[Phil.B] < ticket)) &&
                        ((cs[Phil.A] != CS.Thinking && cs[Phil.B] != CS.Thinking) ==> t[Phil.A] != t[Phil.B]) &&
                        (cs[Phil.A] == CS.Eating ==> t[Phil.A] == serving) &&
                        (cs[Phil.B] == CS.Eating ==> t[Phil.B] == serving) })
                    class TicketBad {
                        enum Phil { A, B }
                        enum CS { Thinking, Hungry, Eating }
                        int ticket
                        int serving
                        Map<Phil,CS> cs
                        Map<Phil,Integer> t
                        @Requires({ cs[p] == CS.Thinking })
                        void request(Phil p) { t[p] = ticket; cs[p] = CS.Hungry }
                    }''')],
    ]
}
