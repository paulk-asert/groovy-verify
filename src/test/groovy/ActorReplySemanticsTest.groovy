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
import groovy.concurrent.ActorContext
import groovy.concurrent.ReactorHandler
import groovy.concurrent.StatefulHandler
import org.junit.jupiter.api.Test

import java.util.concurrent.TimeUnit
import java.util.concurrent.TimeoutException

import static org.junit.jupiter.api.Assertions.assertEquals
import static org.junit.jupiter.api.Assertions.assertFalse
import static org.junit.jupiter.api.Assertions.assertTrue

/**
 * What a {@code sendAndGet} REPLY really is, measured before Phase 294 models it (the Phase 289 rule: the
 * checker models {@code groovy.concurrent} as it BEHAVES).
 *
 * <p>Four facts the reply check rests on. A reply is the value the DISPATCH returns, so for a
 * {@code reactor} it is the handler's own return — the label a {@code @Protocol} reply names — while for a
 * {@code stateful} actor the return is the new STATE, which is why the checker withholds the label there.
 * A reply is produced exactly when the message is HANDLED: a message the phase merely ignores still replies,
 * a deferred one replies only once a replay finally handles it, a throwing arm completes it exceptionally,
 * and one still stashed at {@code stop()} fails. That is what makes a deferred-but-answered message a
 * deadlock: the peer blocks on a reply that the protocol's own next message would have to unblock.
 */
class ActorReplySemanticsTest {

    // not `await` — in Groovy 6 `await { … }` is the async await, which would try to await the closure itself
    private static void waitUntil(Closure<Boolean> cond) {
        long end = System.currentTimeMillis() + 5000
        while (!cond() && System.currentTimeMillis() < end) Thread.sleep(20)
    }

    @Test
    void aReactorRepliesWithItsHandlersReturnAndAStatefulActorWithItsNewState() {
        Actor<String> r = Actor.reactor({ ActorContext<String> ctx, String m -> 'ack:' + m } as ReactorHandler<String, String>)
        Object reactorReply = r.sendAndGet('req').get(5, TimeUnit.SECONDS)
        r.stop()
        Actor<String> s = Actor.stateful(0, { ActorContext<String> ctx, Integer st, String m -> st + 1 } as StatefulHandler<Integer, String>)
        Object first = s.sendAndGet('a').get(5, TimeUnit.SECONDS)
        Object second = s.sendAndGet('b').get(5, TimeUnit.SECONDS)
        s.stop()
        println "  [runtime] reactor sendAndGet -> ${reactorReply}; stateful sendAndGet -> ${first}, then ${second}"
        assertEquals('ack:req', reactorReply, "a reactor's reply is its handler's return")
        assertEquals([1, 2], [first, second], "a stateful actor's reply is its NEW STATE, not a chosen value")
    }

    @Test
    void aMessageThePhaseMerelyIgnoresStillReplies() {
        Actor<String> a = Actor.reactor({ ActorContext<String> ctx, String m -> m == 'req' ? 'ack' : 'other' } as ReactorHandler<String, String>)
        Object reply = a.sendAndGet('zzz').get(5, TimeUnit.SECONDS)
        a.stop()
        println "  [runtime] the default branch's reply: ${reply}"
        assertEquals('other', reply, 'every HANDLED message replies — being ignored by the default is still handled')
    }

    @Test
    void aDeferredMessageRepliesOnlyOnceAReplayHandlesIt() {
        StatefulHandler<Integer, String> waiting, open
        open = { ActorContext<String> ctx, Integer s, String m -> 'answer:' + m } as StatefulHandler<Integer, String>
        waiting = { ActorContext<String> ctx, Integer s, String m ->
            if (m == 'go') { ctx.become(open); ctx.unstashAll(); return s }
            ctx.stash()
            s
        } as StatefulHandler<Integer, String>
        Actor<String> a = Actor.stateful(0, waiting)
        def reply = a.sendAndGet('req')
        Thread.sleep(200)
        boolean pendingWhileStashed = !reply.isDone()
        a.send('go')
        waitUntil { reply.isDone() }
        Object value = reply.isDone() ? reply.get(5, TimeUnit.SECONDS) : null
        a.stop()
        println "  [runtime] while stashed the reply was pending=${pendingWhileStashed}; after the replay: ${value}"
        assertTrue(pendingWhileStashed, 'a deferred message has not been answered — the peer is still blocked')
        assertEquals('answer:req', value, 'the reply follows the message through the stash, into the phase that handles it')
    }

    @Test
    void aThrowingArmCompletesTheReplyExceptionallyAndStopFailsAStillStashedOne() {
        Actor<String> t = Actor.reactor({ ActorContext<String> ctx, String m -> throw new IllegalStateException('nope') } as ReactorHandler<String, String>)
        def thrown = t.sendAndGet('req')
        waitUntil { thrown.isDone() }
        boolean exceptionally = thrown.isCompletedExceptionally()
        t.stop()
        Actor<String> s = Actor.stateful(0, { ActorContext<String> ctx, Integer st, String m -> ctx.stash(); st } as StatefulHandler<Integer, String>)
        def stashed = s.sendAndGet('req')
        Thread.sleep(200)
        boolean pendingBeforeStop = !stashed.isDone()
        s.stop()
        waitUntil { stashed.isDone() }
        String outcome
        try {
            stashed.get(5, TimeUnit.SECONDS)
            outcome = 'completed normally'
        } catch (TimeoutException ignored) {
            outcome = 'never completed'
        } catch (Exception e) {
            Throwable c = e.cause ?: e
            outcome = "failed: ${c.class.simpleName}"
        }
        println "  [runtime] a throwing arm: exceptionally=${exceptionally}; a still-stashed reply at stop(): ${outcome}"
        assertTrue(exceptionally, 'a throwing arm completes the reply exceptionally — that is not the protocol\'s ack')
        assertFalse(!pendingBeforeStop, 'a stashed message is unanswered until it is handled')
        assertTrue(outcome.startsWith('failed:'), 'a reply still owed at stop() fails rather than hanging for ever')
    }
}
