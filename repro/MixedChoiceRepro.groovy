/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */

/*
 * The MIXED CHOICE over groovy.concurrent channels — the reproduction behind groovy-verify's Phase 267
 * (examples/kerridge.md, "the race") and the upstream proposal repro/GROOVY-MixedChoice-jira-draft.md.
 * A mixed choice is a session where either peer may open: left may send `ping` OR receive `pong`; right,
 * dually. occam banned output guards because arbitrating this needs a commit protocol
 * (Buckley–Silberschatz); ChannelSelect (GROOVY-12320) offers input guards only. Four experiments:
 *
 *   1. The COLLISION: both peers open (buffered sends both succeed) — each reads the other's opener
 *      as "your choice" and the two proceed down DIFFERENT branches of the same session.
 *   2. The DEGENERATE case: one initiator — the mixed choice quietly becomes that role's choice.
 *   3. POLITENESS: both peers only offer to receive — nobody opens, the session never starts.
 *   4. What ARBITRATION must give: a hand-rolled claim (one CAS standing in for the commit protocol —
 *      the SPEC, exactly-one-commit; the real protocol needs a revertible two-phase claim, see the
 *      draft) — N racing trials, exactly one branch committed in every one.
 *   5. The COHERENCE caveat's ground: a capacity-0 (rendezvous) send pends until a receiver takes it —
 *      the handshake an arbitrated select can hook into — while a buffered send completes alone, which
 *      is why session coherence between two selects needs capacity-0 openers.
 *
 * Run:  GROOVY_HOME=~/Developer/groovy-6.0.0-beta-3 ~/Developer/groovy-6.0.0-beta-3/bin/groovy repro/MixedChoiceRepro.groovy
 */
import groovy.concurrent.AsyncChannel
import java.util.concurrent.CountDownLatch
import java.util.concurrent.atomic.AtomicInteger
import static org.apache.groovy.runtime.async.AsyncSupport.*

println "Groovy ${GroovySystem.version}, ${System.getProperty('java.version')}"
println()

// ---------- 1. the collision: both peers open ----------
def ping = AsyncChannel.<Integer>create(4)                 // left -> right
def pong = AsyncChannel.<Integer>create(4)                 // right -> left
ping.send(1)                                               // left opens its branch...
pong.send(2)                                               // ...and right opens its own: both succeed (buffered)
int leftSees = await pong.receive()                        // left: "an opener from right — so right chose pong"
int rightSees = await ping.receive()                       // right: "an opener from left — so left chose ping"
println "1. both peers open a mixed choice (ping: left -> right | pong: right -> left):"
println "   left sent ping AND read the pong opener (${leftSees}) — it continues down the PONG branch"
println "   right sent pong AND read the ping opener (${rightSees}) — it continues down the PING branch"
println "   => COLLISION: one session, two peers on DIFFERENT branches, each sure of its own choice"
println "      (each peer CONFORMS to the mixed local type alone; coherence is what broke)"
println()

// ---------- 2. one initiator: the degenerate mixed choice ----------
def ping2 = AsyncChannel.<Integer>create(4)
def pong2 = AsyncChannel.<Integer>create(4)
ping2.send(10)                                             // only left opens
int got2 = await ping2.receive()                           // right just offers to receive: takes left's opener
println "2. one initiator: left opens (${got2}), right only offers to receive"
println "   => the mixed choice DEGENERATES to a choice at left — the shape the checker certifies"
println()

// ---------- 3. politeness: nobody opens ----------
def ping3 = AsyncChannel.<Integer>create(4)
def pong3 = AsyncChannel.<Integer>create(4)
String outcome
try {
    def r = await groovy.concurrent.ChannelSelect.from(ping3, pong3).select().orTimeoutMillis(500)
    outcome = "completed with ${r}"
} catch (Throwable t) {
    outcome = "${t.class.simpleName} after 500 ms"
}
println "3. both peers only offer to receive (each ALTs on the other's opener): ${outcome}"
println "   => ${outcome.contains('Timeout') ? 'NOBODY OPENS — the session never starts (input guards cannot say \"or I will send\")' : outcome}"
println()

// ---------- 4. what arbitration must give: a two-phase claim ----------
int n = 1000
int both = 0, neither = 0
AtomicInteger leftWins = new AtomicInteger(), rightWins = new AtomicInteger()
for (int i = 0; i < n; i++) {
    AtomicInteger claim = new AtomicInteger(0)             // 0 = open; 1 = left committed; 2 = right committed
    CountDownLatch go = new CountDownLatch(1)
    Thread l = Thread.start { go.await(); if (claim.compareAndSet(0, 1)) leftWins.incrementAndGet() }
    Thread r = Thread.start { go.await(); if (claim.compareAndSet(0, 2)) rightWins.incrementAndGet() }
    go.countDown(); l.join(); r.join()
    if (claim.get() == 0) neither++
}
println "4. the same race through a CLAIM (one CAS standing in for the two-phase commit an arbitrated"
println "   select would run): ${n} trials — left committed ${leftWins.get()}, right committed ${rightWins.get()}, both 0, neither ${neither}"
println "   => EXACTLY ONE branch commits in every trial: the semantics claimable SEND offers would give"
println "      (GROOVY-12320 made receives claimable; a send offer that can be claimed or retired is the"
println "       missing half — ChannelSelect.offers(send(ping, v), receive(pong)).select())"
println()

// ---------- 5. rendezvous vs buffered: where cross-select coherence can come from ----------
def rz = AsyncChannel.<Integer>create(0)
def sendF = rz.send(42)
Thread.sleep(100)
boolean pendsAlone = !sendF.done
int taken = await rz.receive()
Thread.sleep(100)
boolean completesOnTake = sendF.done
def buf = AsyncChannel.<Integer>create(4)
def bufF = buf.send(7)
Thread.sleep(100)
println "5. capacity-0 send with no receiver: ${pendsAlone ? 'PENDS' : 'completed alone'}; after a receiver takes (${taken}): ${completesOnTake ? 'COMPLETES' : 'still pending'}"
println "   capacity-4 send with no receiver: ${bufF.done ? 'COMPLETES ALONE' : 'pends'}"
println "   => session coherence between two selects can only come from the rendezvous: a buffered send"
println "      offer commits unilaterally, and the experiment-1 collision would reproduce through the"
println "      proposed API — the racing mixed choice needs capacity-0 opener channels"
println()
println "Done."
System.exit(0)
