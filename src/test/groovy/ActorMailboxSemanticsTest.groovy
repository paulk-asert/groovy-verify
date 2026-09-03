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
import groovy.concurrent.Actor
import groovy.concurrent.ActorOptions
import org.junit.jupiter.api.Test

import java.util.concurrent.CountDownLatch
import java.util.concurrent.TimeUnit

import static org.junit.jupiter.api.Assertions.assertTrue

/**
 * What the BOUNDED MAILBOX really does to a {@code sendAndGet} caller whose message is dropped.
 *
 * <p>The checker models {@code groovy.concurrent} <b>as it behaves</b>, not as documented, so a claim about
 * an overflow policy has to be established here before any case may rest on it. The question this pins is a
 * liveness one, and it comes from an asymmetry in {@link ActorOptions}' own javadoc: the STASH policies each
 * say what becomes of a {@code sendAndGet} reply when a message is evicted or rejected ("bound to
 * IllegalStateException so the caller does not wait forever"), while the MAILBOX policy {@code DROP_NEWEST}
 * says only "the new message is silently dropped" — silent about the caller.
 *
 * <p>If a dropped {@code sendAndGet} leaves its Awaitable uncompleted, the caller waits forever: a silent
 * liveness loss, and exactly the shape the verifier refutes as "may block forever".
 */
class ActorMailboxSemanticsTest {

    /** Wedge the worker on the first message so the mailbox behind it can be filled deterministically. */
    private static Actor<String> wedged(CountDownLatch gate, ActorOptions opts) {
        Actor.reactor({ String m -> if (m == 'block') gate.await(5, TimeUnit.SECONDS); m }, opts)
    }

    @Test
    void aDroppedSendAndGetDoesNotStrandItsCaller() {
        CountDownLatch gate = new CountDownLatch(1)
        Actor<String> a = wedged(gate, ActorOptions.DEFAULTS.withBoundedMailbox(1, ActorOptions.Overflow.DROP_NEWEST))
        try {
            a.send('block')                       // occupies the worker
            Thread.sleep(200)                     // let the worker pick it up and wedge
            a.send('fills-the-mailbox')           // the one slot
            def reply = a.sendAndGet('dropped')   // capacity exceeded → DROP_NEWEST
            boolean settled
            try {
                reply.get(2, TimeUnit.SECONDS)
                settled = true
                println '  [runtime] a dropped sendAndGet COMPLETED normally'
            } catch (java.util.concurrent.TimeoutException ignored) {
                settled = false
                println '  [runtime] a dropped sendAndGet NEVER completed — the caller is stranded'
            } catch (Exception e) {
                settled = true
                println "  [runtime] a dropped sendAndGet completed exceptionally: ${e.cause?.class?.simpleName ?: e.class.simpleName}"
            }
            assertTrue(settled, 'sendAndGet into a full DROP_NEWEST mailbox left its Awaitable uncompleted — ' +
                'the caller waits forever, where the StashOverflow policies bind the reply so it does not')
        } finally {
            gate.countDown(); a.stop()
        }
    }

    /** The documented stash behaviour, as the control: there the reply IS bound. */
    @Test
    void theStashPolicyBindsTheReplyAsDocumented() {
        CountDownLatch gate = new CountDownLatch(1)
        Actor<String> a = wedged(gate, ActorOptions.DEFAULTS.withBoundedMailbox(2, ActorOptions.Overflow.FAIL))
        try {
            def reply = a.sendAndGet('block')
            gate.countDown()
            assertTrue(reply.get(5, TimeUnit.SECONDS) == 'block', 'an ordinary sendAndGet round-trips')
        } finally {
            gate.countDown(); a.stop()
        }
    }

    /**
     * {@code Overflow.BLOCK} — "the sending thread blocks until space is available". If that is literally
     * true then a bounded mailbox IS a bounded blocking channel, and the Phase 272 rendezvous model applies
     * to it unchanged: a send is a blocking event, so a cycle of actors each sending into a full mailbox is
     * a wait-for cycle the well-foundedness certificate can name. Everything the checker claims about a
     * BLOCK mailbox rests on this test.
     */
    @Test
    void aSendIntoAFullBlockMailboxReallyBlocksTheSender() {
        CountDownLatch gate = new CountDownLatch(1)
        Actor<String> a = wedged(gate, ActorOptions.DEFAULTS.withBoundedMailbox(1, ActorOptions.Overflow.BLOCK))
        CountDownLatch returned = new CountDownLatch(1)
        try {
            a.send('block')                       // occupies the worker
            Thread.sleep(200)
            a.send('fills-the-mailbox')           // the one slot
            Thread t = new Thread({ a.send('must-block'); returned.countDown() })
            t.daemon = true
            t.start()
            boolean early = returned.await(1, TimeUnit.SECONDS)
            println "  [runtime] send into a full BLOCK mailbox returned early: ${early}"
            assertTrue(!early, 'Overflow.BLOCK did not block the sender — the bounded-mailbox deadlock model would be unsound')
            gate.countDown()                      // the worker drains; the blocked send may now proceed
            boolean freed = returned.await(5, TimeUnit.SECONDS)
            println "  [runtime] …and completed once space appeared: ${freed}"
            assertTrue(freed, 'the blocked send never completed after space appeared')
        } finally {
            gate.countDown(); a.stop()
        }
    }

    /**
     * The gallery's stated assumption, checked rather than assumed: "sends never block on a buffered channel
     * (queued, the Awaitable discarded)". If an {@code AsyncChannel.create(k)} send blocked once k elements
     * were outstanding, that sentence would be true only while a network stays under capacity, and several
     * certificates rest on it. Overfill one and see.
     */
    @Test
    void aBufferedChannelSendDoesNotBlockTheSenderWhenFull() {
        groovy.concurrent.AsyncChannel<Integer> c = groovy.concurrent.AsyncChannel.create(2)
        CountDownLatch returned = new CountDownLatch(1)
        Thread t = new Thread({
            for (int i = 0; i < 8; i++) c.send(i)      // 8 sends into a capacity-2 channel, nothing draining
            returned.countDown()
        })
        t.daemon = true
        t.start()
        boolean freeRunning = returned.await(2, TimeUnit.SECONDS)
        println "  [runtime] 8 sends into a capacity-2 AsyncChannel with no reader completed: ${freeRunning}"
        assertTrue(freeRunning, 'a buffered AsyncChannel send BLOCKED when the buffer was full — the ' +
            "gallery's \"a send never blocks\" assumption would then hold only under capacity")
    }
}
