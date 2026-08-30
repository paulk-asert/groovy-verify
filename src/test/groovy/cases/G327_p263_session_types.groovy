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
 * 'P263 session types' — a @Protocol is the GLOBAL type of a method's channel network (Scribble-style:
 * `label: from -> to`, `loop { … }`, `choice at role { … } or { … }`), projected onto each role and checked
 * against every process's control flow: a process never performs an op its role's local type does not allow
 * next, and never ends where the protocol continues. Structural, with a counter-trace; the other rungs'
 * certificates stand on their own.
 */
class G327_p263_session_types {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 263 session types (slice 23 of the SEQ/PAR ladder): a @Protocol on the method is the GLOBAL type of its channel network in the multiparty-session-type sense — `label: from -> to` messages (the label is the channel), `loop { … }`, `choice at role { … } or { … }` — PROJECTED onto each role (a message is `!c` to its sender, `?c` to its receiver; a choice at S is S\'s selection and, for another role, an external choice its branches must let it tell apart by their first message to it, or be identical for it) and checked by CONFORMANCE: each process (the main body, each async arm) is bound to a role by the channel ends it uses, its control flow read as an automaton over channel ops (sends, receives, drains, ALTs as choices, loops as stars, ifs as unions), and language inclusion decides — a violation is named with the trace that reaches it ("receives from reply after it sends on request … where the protocol expects it to …"). What it adds is ORDER across the whole conversation, structurally (no solver). Loud boundaries: a choice whose branches are opened by different roles (the fair server — beyond classic projection), a role nobody plays, a process that plays no role.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final String REQ_REPLY = """@Protocol({
                            loop {
                                request: client >> server
                                reply:   server >> client
                            }
                        })"""

    static String clientServer(String proto, String client, String server = """int j = 0
                                @Invariant({ j >= 0 })
                                while (true) {
                                    int q = request.first()
                                    reply.send(q + 1)
                                    j = j + 1
                                }""") { """class C {
                        ${proto}
                        static void clientServer() {
                            AsyncChannel<Integer> request = AsyncChannel.create(4)
                            AsyncChannel<Integer> reply = AsyncChannel.create(4)
                            async {                                              // the server
                                ${server}
                            }
                            ${client}
                        }
                    }""" }

    static final String CLIENT = """int i = 0
                            @Invariant({ i >= 0 })
                            while (true) {                                       // the client
                                request.send(i)
                                int r = reply.first()
                                i = i + 1
                            }"""

    static final List<Map> CASES = [
        // ---------- the request–reply session ----------
        [group: 'P263 session types', name: 'the forever client–server follows its request–reply protocol', ok: true,
         src: tc(clientServer(REQ_REPLY, CLIENT))],
        [group: 'P263 session types', name: 'a client that waits before asking violates it — named with the trace', expect: "receives from 'reply' (line",
         src: tc(clientServer(REQ_REPLY, """int i = 0
                            @Invariant({ i >= 0 })
                            while (true) {
                                int r = reply.first()
                                request.send(i)
                                i = i + 1
                            }"""))],
        [group: 'P263 session types', name: 'a server that answers twice violates it', expect: "sends on 'reply' (line",
         src: tc(clientServer(REQ_REPLY, CLIENT, """int j = 0
                                @Invariant({ j >= 0 })
                                while (true) {
                                    int q = request.first()
                                    reply.send(q + 1)
                                    reply.send(q + 2)
                                    j = j + 1
                                }"""))],
        [group: 'P263 session types', name: 'a bounded client and a draining server follow the same protocol (loops are stars)', ok: true,
         src: tc("""class C {
                        ${REQ_REPLY}
                        @Requires({ n >= 0 })
                        static void clientServer(int n) {
                            AsyncChannel<Integer> request = AsyncChannel.create(4)
                            AsyncChannel<Integer> reply = AsyncChannel.create(4)
                            async {
                                for (int q in request) {
                                    reply.send(q + 1)
                                }
                            }
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) {
                                request.send(i)
                                int r = reply.first()
                                i = i + 1
                            }
                            request.close()
                        }
                    }""")],
        // ---------- three roles: the primed token ring — the protocol must say the priming ----------
        [group: 'P263 session types', name: 'the primed token ring follows a three-role protocol that says the priming', ok: true,
         src: tc("""class C {
                        @Protocol({
                            ab: a >> b                       // the priming token
                            loop {
                                bc: b >> c
                                ca: c >> a
                                ab: a >> b
                            }
                        })
                        static void ring() {
                            AsyncChannel<Integer> ab = AsyncChannel.create(4)
                            AsyncChannel<Integer> bc = AsyncChannel.create(4)
                            AsyncChannel<Integer> ca = AsyncChannel.create(4)
                            async {                                              // b
                                int j = 0
                                @Invariant({ j >= 0 })
                                while (true) {
                                    int y = ab.first()
                                    bc.send(y + 1)
                                    j = j + 1
                                }
                            }
                            async {                                              // c
                                int m = 0
                                @Invariant({ m >= 0 })
                                while (true) {
                                    int z = bc.first()
                                    ca.send(z + 1)
                                    m = m + 1
                                }
                            }
                            ab.send(0)                                           // a
                            int i = 0
                            @Invariant({ i >= 0 })
                            while (true) {
                                int x = ca.first()
                                ab.send(x + 1)
                                i = i + 1
                            }
                        }
                    }""")],
        [group: 'P263 session types', name: 'the same ring against a protocol without the priming: the first send is the violation', expect: "sends on 'ab' (line",
         src: tc("""class C {
                        @Protocol({
                            loop {
                                bc: b >> c
                                ca: c >> a
                                ab: a >> b
                            }
                        })
                        static void ring() {
                            AsyncChannel<Integer> ab = AsyncChannel.create(4)
                            AsyncChannel<Integer> bc = AsyncChannel.create(4)
                            AsyncChannel<Integer> ca = AsyncChannel.create(4)
                            async {
                                int j = 0
                                @Invariant({ j >= 0 })
                                while (true) {
                                    int y = ab.first()
                                    bc.send(y + 1)
                                    j = j + 1
                                }
                            }
                            async {
                                int m = 0
                                @Invariant({ m >= 0 })
                                while (true) {
                                    int z = bc.first()
                                    ca.send(z + 1)
                                    m = m + 1
                                }
                            }
                            ab.send(0)
                            int i = 0
                            @Invariant({ i >= 0 })
                            while (true) {
                                int x = ca.first()
                                ab.send(x + 1)
                                i = i + 1
                            }
                        }
                    }""")],
        // ---------- a choice at the client: two request kinds, each answered ----------
        [group: 'P263 session types', name: 'a choice at the client (two request kinds) — the client\'s if/else and the server\'s ALT both conform', expect: 'Skipped channel verification', refute: 'Protocol violation',
         src: tc("""class C {
                        @Protocol({
                            loop {
                                choice(at: client) {
                                    add: client >> server
                                    sum: server >> client
                                } or {
                                    neg: client >> server
                                    res: server >> client
                                }
                            }
                        })
                        static void calc() {
                            AsyncChannel<Integer> add = AsyncChannel.create(4)
                            AsyncChannel<Integer> neg = AsyncChannel.create(4)
                            AsyncChannel<Integer> sum = AsyncChannel.create(4)
                            AsyncChannel<Integer> res = AsyncChannel.create(4)
                            async {                                              // the server
                                int j = 0
                                @Invariant({ j >= 0 })
                                while (true) {
                                    ChannelSelect.Result r = await ChannelSelect.from(add, neg).select()
                                    int q = (int) r.value
                                    if (r.index == 0) {
                                        sum.send(q + 1)
                                    }
                                    if (r.index == 1) {
                                        res.send(0 - q)
                                    }
                                    j = j + 1
                                }
                            }
                            int i = 0
                            @Invariant({ i >= 0 })
                            while (true) {                                       // the client chooses
                                if (i % 2 == 0) {
                                    add.send(i)
                                    int s = sum.first()
                                } else {
                                    neg.send(i)
                                    int r = res.first()
                                }
                                i = i + 1
                            }
                        }
                    }""")],
        // ---------- the loud boundaries ----------
        [group: 'P263 session types', name: 'the fair server: a choice opened by different roles is beyond this projection', expect: 'every branch must begin with a message from',
         src: tc("""class C {
                        @Protocol({
                            loop {
                                choice(at: server) {
                                    reqA:   clientA >> server
                                    replyA: server >> clientA
                                } or {
                                    reqB:   clientB >> server
                                    replyB: server >> clientB
                                }
                            }
                        })
                        static void fairServer() {
                            AsyncChannel<Integer> reqA = AsyncChannel.create(4)
                            AsyncChannel<Integer> reqB = AsyncChannel.create(4)
                            AsyncChannel<Integer> replyA = AsyncChannel.create(4)
                            AsyncChannel<Integer> replyB = AsyncChannel.create(4)
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    reqA.send(i)
                                    int r = replyA.first()
                                    i = i + 1
                                }
                            }
                            async {
                                int i = 0
                                @Invariant({ i >= 0 })
                                while (true) {
                                    reqB.send(i)
                                    int r = replyB.first()
                                    i = i + 1
                                }
                            }
                            int j = 0
                            @Invariant({ j >= 0 })
                            while (true) {
                                ChannelSelect.Result r = await ChannelSelect.from(reqA, reqB).select()
                                int q = (int) r.value
                                if (r.index == 0) {
                                    replyA.send(q + 1)
                                }
                                if (r.index == 1) {
                                    replyB.send(q + 1)
                                }
                                j = j + 1
                            }
                        }
                    }""")],
        [group: 'P263 session types', name: 'a role nobody plays is named', expect: 'no process plays it',
         src: tc(clientServer("""@Protocol({
                            loop {
                                request: client >> server
                                reply:   server >> client
                                log:     server >> logger
                            }
                        })""", CLIENT).replace('AsyncChannel<Integer> reply = AsyncChannel.create(4)', 'AsyncChannel<Integer> reply = AsyncChannel.create(4)\n                            AsyncChannel<Integer> log = AsyncChannel.create(4)'))],
        // Phase 267's subset binding improved this verdict: a send-only client FITS the client role (a
        // conformant process may use a subset of its alphabet), and conformance then names the real miss.
        [group: 'P263 session types', name: 'a client that never listens is refuted in its role, the miss named', expect: 'the protocol expects it to receives from',
         src: tc(clientServer(REQ_REPLY, """int i = 0
                            @Invariant({ i >= 0 })
                            while (true) {                                       // only asks, never listens
                                request.send(i)
                                i = i + 1
                            }"""))],
    ]
}
