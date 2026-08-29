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

/*
 * Observed behaviour of groovy.concurrent.ChannelSelect (Groovy 6.0.0-beta-3) — the reproduction behind
 * groovy-verify's Phase 256 (examples/kerridge.md, "the fair server"). Four experiments, each printing
 * what it observed next to what a JCSP-style Alternative would do:
 *
 *   1. When several branches are ready, which wins?           (priority by list order)
 *   2. Does a losing branch keep its element order?           (the loser's element is re-sent to the BACK)
 *   3. Do losing branches accumulate pending receivers?       (one per select per losing branch)
 *   4. What happens when every branch is closed and drained?  (the select never completes)
 *
 * Run:  GROOVY_HOME=~/Developer/groovy-6.0.0-beta-3 ~/Developer/groovy-6.0.0-beta-3/bin/groovy repro/ChannelSelectRepro.groovy
 */
import groovy.concurrent.AsyncChannel
import groovy.concurrent.ChannelSelect
import static org.apache.groovy.runtime.async.AsyncSupport.*

/** Pending receivers registered on a channel (DefaultAsyncChannel.waitingReceivers), via reflection. */
static int waitingReceivers(AsyncChannel ch) {
    def f = ch.class.getDeclaredField('waitingReceivers')
    f.accessible = true
    ((Collection) f.get(ch)).size()
}

println "Groovy ${GroovySystem.version}, ${System.getProperty('java.version')}"
println()

// ---------- 1. priority by list order ----------
int[] wins = new int[2]
100.times {
    def a = AsyncChannel.<String>create(4)
    def b = AsyncChannel.<String>create(4)
    a.send('a'); b.send('b')                               // both ready before the select
    def r = await ChannelSelect.from(a, b).select()
    wins[r.index]++
}
int[] winsRev = new int[2]
100.times {
    def a = AsyncChannel.<String>create(4)
    def b = AsyncChannel.<String>create(4)
    a.send('a'); b.send('b')
    def r = await ChannelSelect.from(b, a).select()       // same channels, listed the other way round
    winsRev[r.index]++
}
println "1. both branches ready, 100 selects over [a, b]: index 0 won ${wins[0]}, index 1 won ${wins[1]}"
println "   the same over [b, a]:                         index 0 won ${winsRev[0]}, index 1 won ${winsRev[1]}"
println "   => ${wins[1] == 0 && winsRev[1] == 0 ? 'PRIORITY BY LIST ORDER (the first ready branch always wins)' : 'not strictly by list order'}"
println "   (JCSP: select() arbitrary, priSelect() by order, fairSelect() rotating — no fair choice is available here)"
println()

// ---------- 2. the losing branch's order ----------
def a2 = AsyncChannel.<String>create(4)
def b2 = AsyncChannel.<String>create(4)
a2.send('a1')
b2.send('b1'); b2.send('b2')                              // b holds [b1, b2], a holds [a1]
def r2 = await ChannelSelect.from(a2, b2).select()      // a wins (index 0); b's receive loses
def got = [await(b2.receive()), await(b2.receive())]
println "2. b held [b1, b2]; a select that '${r2.value}' won; b then delivers ${got}"
println "   => ${got == ['b1', 'b2'] ? 'FIFO kept' : 'REORDERED — the losing branch’s consumed element was re-sent to the BACK of its queue'}"
println()

// ---------- 3. stale receivers on a losing branch ----------
def busy = AsyncChannel.<Integer>create(4)
def quiet = AsyncChannel.<Integer>create(4)               // never has an element during the loop
int n = 1000
for (int i = 0; i < n; i++) {
    busy.send(i)
    def r = await ChannelSelect.from(busy, quiet).select()
    assert r.index == 0
}
int pending = waitingReceivers(quiet)
println "3. ${n} selects over [busy, quiet] with 'quiet' always empty: pending receivers registered on 'quiet' = ${pending}"
quiet.send(42)
Thread.sleep(300)                                          // let the stale receivers take and re-send it
int pendingAfter = waitingReceivers(quiet)
int buffered = quiet.bufferedSize
println "   then one send on 'quiet' + 300 ms: buffered = ${buffered}, pending receivers now = ${pendingAfter}"
println "   => ${pending >= n ? 'EVERY select left a pending receiver on the losing branch (unbounded growth in a long-lived multiplexer)' : 'pending receivers are bounded'}" +
        "${pending - pendingAfter > 1 ? '; the one element was taken and re-sent ' + (pending - pendingAfter) + ' times before settling' : ''}"
println()

// ---------- 4. every branch closed and drained ----------
def c1 = AsyncChannel.<Integer>create(1)
def c2 = AsyncChannel.<Integer>create(1)
c1.close(); c2.close()                                     // closed, nothing buffered
def sel = ChannelSelect.from(c1, c2).select()
String outcome
try {
    def r = await sel.orTimeoutMillis(500)
    outcome = "completed with ${r}"
} catch (Throwable t) {
    outcome = "${t.class.simpleName}: ${t.message}"
}
println "4. select over two closed, empty channels: ${outcome}"
println "   => ${outcome.contains('Timeout') ? 'NEVER COMPLETES (a ChannelClosedException would be the honest outcome)' : outcome.contains('ChannelClosed') ? 'fails fast with ChannelClosedException' : 'see above'}"
println()
println "Done."
System.exit(0)
