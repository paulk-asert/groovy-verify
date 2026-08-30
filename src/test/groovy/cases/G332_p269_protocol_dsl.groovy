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
 * 'P269 protocol closure DSL' — the @Protocol closure: plain Groovy carried by Groovy's own parser
 * (labels are message names, >> points from sender to receiver, command chains are the combinators),
 * harvested and rendered to protocol text before STC (its names are vocabulary, not variables). Errors
 * come from the compiler with real positions; the Phase 263 string survives as `text = '''…'''`.
 */
class G332_p269_protocol_dsl {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 269 the @Protocol closure DSL (slice 30 of the SEQ/PAR ladder): the protocol is written as a Groovy CLOSURE — `@Protocol({ loop { request: client >> server; reply: server >> client } })` — and parsed by Groovy itself: a statement LABEL is the message name, `>>` points from sender to receiver, and `loop { }` / `choice(at: role) { } or { }` / `choice { } or { }` / `par { } and { }` are command chains. ContractExpansionTransform harvests the closure at CONVERSION (before STC would see undeclared names — the names are protocol vocabulary, not variables), renders it to the canonical protocol text, and clears the closure member; SessionChecker is unchanged downstream. Ill-formed DSL is a COMPILE error with the statement\'s own line and column (a wrong combinator, a wrong joiner — `choice … and`, a stray named argument, a message without its label). The Phase 263 string form survives as `text = \\\'\\\'\\\'…\\\'\\\'\\\'` for tools that carry protocols as strings. Every session-type capability (263-267) now reads the closure surface; the whole corpus is migrated.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static String clientServer(String proto) { """class C {
                        ${proto}
                        static void clientServer() {
                            AsyncChannel<Integer> request = AsyncChannel.create(4)
                            AsyncChannel<Integer> reply = AsyncChannel.create(4)
                            async {                                              // the server
                                int j = 0
                                @Invariant({ j >= 0 })
                                while (true) {
                                    int q = request.first()
                                    reply.send(q + 1)
                                    j = j + 1
                                }
                            }
                            int i = 0
                            @Invariant({ i >= 0 })
                            while (true) {                                       // the client
                                request.send(i)
                                int r = reply.first()
                                i = i + 1
                            }
                        }
                    }""" }

    static final List<Map> CASES = [
        [group: 'P269 protocol closure DSL', name: 'the closure DSL end to end: the request–reply loop conforms', ok: true,
         src: tc(clientServer("""@Protocol({
                            loop {
                                request: client >> server
                                reply:   server >> client
                            }
                        })"""))],
        [group: 'P269 protocol closure DSL', name: 'the string form survives as text = (the Phase 263 surface)', ok: true,
         src: tc(clientServer("""@Protocol(text = '''
                            loop {
                                request: client -> server
                                reply:   server -> client
                            }
                        ''')"""))],
        [group: 'P269 protocol closure DSL', name: 'a violation through the closure surface carries its trace', expect: "receives from 'reply' (line",
         src: tc(clientServer("""@Protocol({
                            loop {
                                request: client >> server
                                reply:   server >> client
                            }
                        })""").replace('request.send(i)\n                                int r = reply.first()', 'int r = reply.first()\n                                request.send(i)'))],
        [group: 'P269 protocol closure DSL', name: 'a wrong combinator is a compile error at its own line', expect: 'the @Protocol closure holds something the protocol DSL does not',
         src: tc(clientServer("""@Protocol({
                            forever {
                                request: client >> server
                            }
                        })"""))],
        [group: 'P269 protocol closure DSL', name: 'a choice joined with and is a compile error naming the joiner', expect: "cannot continue a 'choice'",
         src: tc(clientServer("""@Protocol({
                            choice(at: client) {
                                request: client >> server
                            } and {
                                reply: server >> client
                            }
                        })"""))],
        [group: 'P269 protocol closure DSL', name: 'a message without its label is a compile error', expect: 'the @Protocol closure holds something',
         src: tc(clientServer("""@Protocol({
                            loop {
                                client >> server
                            }
                        })"""))],
    ]
}
