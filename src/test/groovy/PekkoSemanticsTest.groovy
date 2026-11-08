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
import org.apache.pekko.actor.typed.ActorRef
import org.apache.pekko.actor.typed.ActorSystem
import org.apache.pekko.actor.typed.Behavior
import org.apache.pekko.actor.typed.MailboxSelector
import org.apache.pekko.actor.typed.PostStop
import org.apache.pekko.actor.typed.javadsl.AbstractBehavior
import org.apache.pekko.actor.typed.javadsl.ActorContext
import org.apache.pekko.actor.typed.javadsl.AskPattern
import org.apache.pekko.actor.typed.javadsl.Behaviors
import org.apache.pekko.actor.typed.javadsl.Receive
import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.Test

import java.time.Duration
import java.util.concurrent.CompletableFuture
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.CountDownLatch
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicInteger

import static org.junit.jupiter.api.Assertions.assertEquals
import static org.junit.jupiter.api.Assertions.assertTrue

/**
 * What Apache Pekko typed actors (2.0.0) really do, measured before a Pekko encoding pack may rest on any of it —
 * the {@code groovy.concurrent} discipline of {@code ActorMailboxSemanticsTest}, applied to Pekko.
 *
 * <p>Each test drives the real runtime, prints what it saw as a {@code [runtime]} line, and asserts it, so a Pekko
 * upgrade that changes a fact fails here before a proof is built on the old one. The facts a pack would use:
 * <ul>
 *   <li>a handler is never handed {@code null} ({@code tell(null)} throws at the sender, and an {@code ask} whose
 *       message is null fails without delivering it);</li>
 *   <li>nothing is delivered after a handler returns {@code Behaviors.stopped()} — but an {@code AbstractBehavior}'s
 *       {@code onSignal(PostStop)} handler still runs once, after, on the state the stopping handler left;</li>
 *   <li>a tell to self is queued, never run inside the handler that sent it;</li>
 *   <li>{@code AbstractBehavior}'s constructor runs no subclass code ({@code createReceive} is called later);</li>
 *   <li>a full bounded mailbox drops, without blocking the sender;</li>
 *   <li>a stash past its capacity throws at the {@code stash} call;</li>
 *   <li>an {@code ask} nobody answers completes exceptionally at its timeout — but one answered by whichever actor
 *       its {@code replyTo} was handed on to completes, and a second reply is dropped without failing the replier;</li>
 *   <li>an exception in a handler stops the actor (no restart, unless supervised).</li>
 * </ul>
 */
class PekkoSemanticsTest {

    private final List<ActorSystem<?>> systems = []

    private <T> ActorSystem<T> system(Behavior<T> guardian) {
        ActorSystem<T> s = ActorSystem.create(guardian, 'measure' + systems.size())
        systems << s
        s
    }

    @AfterEach
    void terminate() {
        for (ActorSystem<?> s : systems) {
            s.terminate()
            s.getWhenTerminated().toCompletableFuture().get(10, TimeUnit.SECONDS)
        }
    }

    @Test
    void aNullMessageIsRefusedAtTheSender() {
        AtomicInteger handled = new AtomicInteger()
        ActorSystem<Object> s = system(Behaviors.receiveMessage { Object m -> handled.incrementAndGet(); Behaviors.same() })
        Throwable thrown = null
        try {
            s.tell(null)
        } catch (Throwable t) {
            thrown = t
        }
        Thread.sleep(300)
        println "  [runtime] tell(null) threw ${thrown?.class?.name}; the handler ran ${handled.get()} time(s)"
        assertTrue(thrown != null, 'tell(null) returned normally: a handler could be handed null')
        assertEquals(0, handled.get(), 'a null message reached the handler')
    }

    @Test
    void anAskWithANullMessageNeverReachesTheHandler() {
        AtomicInteger handled = new AtomicInteger()
        ActorSystem<Object> s = system(Behaviors.receiveMessage { Object m -> handled.incrementAndGet(); Behaviors.same() })
        Throwable failure = null
        try {
            AskPattern.ask(s, { ActorRef<String> replyTo -> null }, Duration.ofMillis(300), s.scheduler())
                .toCompletableFuture().get(5, TimeUnit.SECONDS)
        } catch (Throwable t) {
            failure = t
        }
        Thread.sleep(300)
        println "  [runtime] an ask whose message is null failed with ${failure?.class?.name}; the handler ran ${handled.get()} time(s)"
        assertTrue(failure != null, 'an ask with a null message completed normally')
        assertEquals(0, handled.get(), 'a null message reached the handler through ask')
    }

    @Test
    void nothingIsDeliveredAfterStopped() {
        AtomicInteger handled = new AtomicInteger()
        CountDownLatch first = new CountDownLatch(1)
        ActorSystem<String> s = system(Behaviors.setup { ctx ->
            Behaviors.receiveMessage { String m ->
                handled.incrementAndGet()
                first.countDown()
                Behaviors.stopped()
            }
        })
        s.tell('one'); s.tell('two'); s.tell('three')
        assertTrue(first.await(5, TimeUnit.SECONDS))
        Thread.sleep(500)
        println "  [runtime] three tells to an actor that stops on its first message: handled ${handled.get()}"
        assertEquals(1, handled.get(), 'a message was delivered after the handler returned Behaviors.stopped()')
    }

    static final ConcurrentLinkedQueue<String> STOPPER = new ConcurrentLinkedQueue<String>()

    static class Stopper extends AbstractBehavior<String> {
        private int count
        Stopper(ActorContext<String> context) { super(context) }
        @Override
        Receive<String> createReceive() {
            newReceiveBuilder().onMessage(String, this::onMsg).onSignal(PostStop, this::onPostStop).build()
        }
        private Behavior<String> onMsg(String m) {
            count++
            STOPPER << ('message ' + m + ', count ' + count)
            Behaviors.stopped()
        }
        private Behavior<String> onPostStop(PostStop s) {
            STOPPER << ('PostStop, count ' + count)
            this
        }
    }

    @Test
    void anAbstractBehaviorThatStopsGetsNoMoreMessagesButPostStopAfter() {
        STOPPER.clear()
        CompletableFuture<ActorRef<String>> child = new CompletableFuture<ActorRef<String>>()
        system(Behaviors.setup { ctx ->
            child.complete(ctx.spawn(Behaviors.setup { c -> new Stopper(c) }, 'stopper'))
            Behaviors.empty()
        })
        ActorRef<String> ref = child.get(5, TimeUnit.SECONDS)
        ref.tell('one'); ref.tell('two'); ref.tell('three')
        Thread.sleep(500)
        println "  [runtime] an AbstractBehavior stopping on its first message, with an onSignal(PostStop): ${STOPPER.toList()}"
        assertEquals(['message one, count 1', 'PostStop, count 1'], STOPPER.toList(),
            'after Behaviors.stopped(): expected no further message, then PostStop once on the stopped state')
    }

    @Test
    void aTellToSelfIsQueuedNotReentered() {
        ConcurrentLinkedQueue<String> trace = new ConcurrentLinkedQueue<String>()
        CountDownLatch done = new CountDownLatch(1)
        ActorSystem<String> s = system(Behaviors.setup { ctx ->
            Behaviors.receiveMessage { String m ->
                trace << ('enter ' + m)
                if (m == 'a') ctx.self.tell('b')
                trace << ('exit ' + m)
                if (m == 'b') done.countDown()
                Behaviors.same()
            }
        })
        s.tell('a')
        assertTrue(done.await(5, TimeUnit.SECONDS))
        println "  [runtime] a handler telling itself: ${trace.toList()}"
        assertEquals(['enter a', 'exit a', 'enter b', 'exit b'], trace.toList(),
            'a tell to self ran inside the handler that sent it')
    }

    static final AtomicInteger RECEIVE_BUILDS = new AtomicInteger()
    static final ConcurrentLinkedQueue<String> CONSTRUCTION = new ConcurrentLinkedQueue<String>()

    static class Probe extends AbstractBehavior<String> {
        int count
        Probe(ActorContext<String> context) {
            super(context)
            CONSTRUCTION << 'after super(context): createReceive called ' + RECEIVE_BUILDS.get() + ' time(s)'
        }
        @Override
        Receive<String> createReceive() {
            RECEIVE_BUILDS.incrementAndGet()
            newReceiveBuilder().onMessage(String, { String m -> count++; this }).build()
        }
    }

    @Test
    void theAbstractBehaviorConstructorRunsNoSubclassCode() {
        RECEIVE_BUILDS.set(0); CONSTRUCTION.clear()
        CountDownLatch built = new CountDownLatch(1)
        ActorSystem<String> s = system(Behaviors.setup { ctx ->
            Probe p = new Probe(ctx)
            built.countDown()
            p
        })
        assertTrue(built.await(5, TimeUnit.SECONDS))
        Thread.sleep(200)
        int beforeMessages = RECEIVE_BUILDS.get()
        s.tell('x'); s.tell('y'); s.tell('z')
        Thread.sleep(500)
        println "  [runtime] ${CONSTRUCTION.toList()}; createReceive calls before any message ${beforeMessages}, " +
            "after three messages ${RECEIVE_BUILDS.get()}"
        assertEquals(['after super(context): createReceive called 0 time(s)'], CONSTRUCTION.toList(),
            "AbstractBehavior's constructor called createReceive (subclass code) before the subclass constructor finished")
        assertEquals(1, RECEIVE_BUILDS.get(), 'createReceive is not built once per actor')
    }

    @Test
    void aFullBoundedMailboxDropsWithoutBlockingTheSender() {
        CountDownLatch gate = new CountDownLatch(1)
        AtomicInteger handled = new AtomicInteger()
        CompletableFuture<ActorRef<String>> child = new CompletableFuture<ActorRef<String>>()
        system(Behaviors.setup { ctx ->
            child.complete(ctx.spawn(Behaviors.receiveMessage { String m ->
                if (m == 'block') gate.await(5, TimeUnit.SECONDS)
                handled.incrementAndGet()
                Behaviors.same()
            }, 'bounded', MailboxSelector.bounded(2)))
            Behaviors.empty()
        })
        ActorRef<String> ref = child.get(5, TimeUnit.SECONDS)
        ref.tell('block')
        Thread.sleep(300)
        long t0 = System.nanoTime()
        (1..6).each { ref.tell('m' + it) }
        long ms = (System.nanoTime() - t0).intdiv(1_000_000L)
        gate.countDown()
        Thread.sleep(800)
        println "  [runtime] 6 tells into a bounded(2) mailbox behind a wedged handler returned in ${ms} ms; handled ${handled.get()} in all"
        assertTrue(ms < 1000, 'a tell into a full bounded mailbox blocked the sender')
        assertEquals(3, handled.get(), 'a full bounded mailbox did not drop the overflow (1 wedged + 2 queued expected)')
    }

    @Test
    void aStashPastItsCapacityThrowsAtTheStashCall() {
        ConcurrentLinkedQueue<String> seen = new ConcurrentLinkedQueue<String>()
        CountDownLatch third = new CountDownLatch(1)
        ActorSystem<String> s = system(Behaviors.withStash(2, { stash ->
            Behaviors.receiveMessage { String m ->
                try {
                    stash.stash(m)
                    seen << ('stashed ' + m)
                } catch (Throwable t) {
                    seen << ('threw ' + t.class.name)
                    third.countDown()
                }
                Behaviors.same()
            }
        }))
        s.tell('a'); s.tell('b'); s.tell('c')
        assertTrue(third.await(5, TimeUnit.SECONDS), 'a third stash into a capacity-2 buffer did not throw')
        println "  [runtime] stash(2) given three: ${seen.toList()}"
        assertTrue(seen.toList().last().startsWith('threw ') && seen.toList().last().contains('StashOverflowException'))
    }

    @Test
    void anUnansweredAskCompletesExceptionallyAtItsTimeout() {
        ActorSystem<Object> s = system(Behaviors.receiveMessage { Object m -> Behaviors.same() })   // never replies
        long t0 = System.nanoTime()
        Throwable failure = null
        try {
            AskPattern.ask(s, { ActorRef<String> replyTo -> 'question' }, Duration.ofMillis(300), s.scheduler())
                .toCompletableFuture().get(5, TimeUnit.SECONDS)
        } catch (java.util.concurrent.ExecutionException e) {
            failure = e.cause
        }
        long ms = (System.nanoTime() - t0).intdiv(1_000_000L)
        println "  [runtime] an ask nobody answers failed after ${ms} ms with ${failure?.class?.name}"
        assertTrue(failure != null, 'an unanswered ask completed normally')
        assertTrue(failure instanceof java.util.concurrent.TimeoutException,
            "an unanswered ask failed with ${failure?.class?.name}, not a TimeoutException")
    }

    @Test
    void anAskIsAnsweredByWhoeverItsReplyToIsHandedTo() {
        CompletableFuture<ActorRef<ActorRef<String>>> helper = new CompletableFuture<ActorRef<ActorRef<String>>>()
        ActorSystem<ActorRef<String>> s = system(Behaviors.setup { ctx ->
            helper.complete(ctx.spawn(Behaviors.receiveMessage { ActorRef<String> r -> r.tell('from the helper'); Behaviors.same() },
                'helper'))
            Behaviors.receiveMessage { ActorRef<String> r -> helper.getNow(null).tell(r); Behaviors.same() }   // hands it on
        })
        helper.get(5, TimeUnit.SECONDS)
        String answer = AskPattern.ask(s, { ActorRef<String> replyTo -> replyTo }, Duration.ofSeconds(3), s.scheduler())
            .toCompletableFuture().get(5, TimeUnit.SECONDS)
        println "  [runtime] an ask whose replyTo the handler hands to another actor completed with '${answer}'"
        assertEquals('from the helper', answer, 'an ask answered by the actor its replyTo was handed to did not complete')
    }

    @Test
    void aSecondReplyIsDroppedWithoutFailingTheReplier() {
        ConcurrentLinkedQueue<String> trace = new ConcurrentLinkedQueue<String>()
        CountDownLatch done = new CountDownLatch(2)
        ActorSystem<Object> s = system(Behaviors.receiveMessage { Object m ->
            if (m instanceof ActorRef) {
                ActorRef<String> r = (ActorRef<String>) m
                r.tell('first'); r.tell('second')
                trace << 'replied twice'
            } else {
                trace << ('then ' + m)
            }
            done.countDown()
            Behaviors.same()
        })
        String answer = AskPattern.ask(s, { ActorRef<String> replyTo -> replyTo }, Duration.ofSeconds(3), s.scheduler())
            .toCompletableFuture().get(5, TimeUnit.SECONDS)
        s.tell('next')
        assertTrue(done.await(5, TimeUnit.SECONDS))
        println "  [runtime] a handler that replies twice: the ask completed with '${answer}'; the handler went on: ${trace.toList()}"
        assertEquals('first', answer)
        assertEquals(['replied twice', 'then next'], trace.toList(), 'a second reply failed or stopped the replier')
    }

    @Test
    void anExceptionInAHandlerStopsTheActor() {
        AtomicInteger handled = new AtomicInteger()
        CountDownLatch first = new CountDownLatch(1)
        CompletableFuture<ActorRef<String>> child = new CompletableFuture<ActorRef<String>>()
        system(Behaviors.setup { ctx ->       // the throwing actor is a child: a guardian's failure would end the system
            child.complete(ctx.spawn(Behaviors.receiveMessage { String m ->
                handled.incrementAndGet()
                first.countDown()
                if (m == 'boom') throw new IllegalStateException('boom')
                Behaviors.same()
            }, 'thrower'))
            Behaviors.empty()
        })
        ActorRef<String> ref = child.get(5, TimeUnit.SECONDS)
        ref.tell('boom'); ref.tell('after')
        assertTrue(first.await(5, TimeUnit.SECONDS))
        Thread.sleep(500)
        println "  [runtime] a child whose handler throws on its first message: handled ${handled.get()} message(s) in all"
        assertEquals(1, handled.get(), 'an actor kept handling messages after its handler threw (restarted or resumed)')
    }

    @Test
    void sameAndThisAreTheSameBehaviour() {
        ConcurrentLinkedQueue<String> trace = new ConcurrentLinkedQueue<String>()
        CountDownLatch done = new CountDownLatch(2)
        ActorSystem<String> s = system(Behaviors.setup { ctx ->
            new AbstractBehavior<String>(ctx) {
                int n
                @Override
                Receive<String> createReceive() {
                    newReceiveBuilder().onMessage(String, { String m ->
                        n++; trace << (m + ':' + n); done.countDown()
                        m == 'same' ? Behaviors.same() : this
                    }).build()
                }
            }
        })
        s.tell('same'); s.tell('this')
        assertTrue(done.await(5, TimeUnit.SECONDS))
        println "  [runtime] Behaviors.same() then this: ${trace.toList()}"
        assertEquals(['same:1', 'this:2'], trace.toList(), 'Behaviors.same() did not keep the actor and its state')
    }
}
