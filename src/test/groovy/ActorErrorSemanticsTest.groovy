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
import groovy.util.function.TriConsumer
import org.junit.jupiter.api.Test

import java.util.concurrent.TimeUnit
import java.util.function.BiConsumer

import static org.junit.jupiter.api.Assertions.assertEquals
import static org.junit.jupiter.api.Assertions.assertTrue

/**
 * What {@code Actor.onError} really does, measured before Phase 296 models it (the Phase 289 rule: the checker
 * models {@code groovy.concurrent} as it BEHAVES).
 *
 * <p>The callback is widely read as supervision — install one and the failure is handled. It is not that. The
 * actor survives a throwing dispatch <em>with or without</em> a callback, so what the callback adds is an
 * observation point and, for the three-parameter form, a {@code become}: a RECOVERY EDGE that is the actor's
 * rather than a phase's, since it fires for a throw inside a {@code become} target too. What it cannot do is
 * rescue the caller: a {@code sendAndGet} on the failed message completes exceptionally either way. The message
 * is gone in every case, which is why Phase 296 keeps a throw on a protocol message a violation and uses the
 * callback only to say where the actor carried on.
 */
class ActorErrorSemanticsTest {

    // not `await` — in Groovy 6 `await { … }` is the async await, which would try to await the closure itself
    private static void waitUntil(Closure<Boolean> cond) {
        long end = System.currentTimeMillis() + 5000
        while (!cond() && System.currentTimeMillis() < end) Thread.sleep(20)
    }

    private static ReactorHandler<String, String> boomOn(String trigger, List<String> log, String tag) {
        { ActorContext<String> ctx, String m ->
            if (m == trigger) throw new IllegalStateException('boom')
            log << "${tag}:${m}".toString()
            m
        } as ReactorHandler<String, String>
    }

    @Test
    void theActorSurvivesAThrowWithOrWithoutACallback() {
        List<String> bare = Collections.synchronizedList(new ArrayList<String>())
        Actor<String> a = Actor.reactor(boomOn('boom', bare, 'bare'))
        a.send('boom'); a.send('after')
        waitUntil { bare.contains('bare:after') }
        a.stop()

        List<String> errs = Collections.synchronizedList(new ArrayList<String>())
        List<String> watched = Collections.synchronizedList(new ArrayList<String>())
        Actor<String> b = Actor.reactor(boomOn('boom', watched, 'watched'))
        b.onError({ Throwable t, String msg -> errs << "${t.class.simpleName}/${msg}".toString() } as BiConsumer<Throwable, String>)
        b.send('boom'); b.send('after')
        waitUntil { watched.contains('watched:after') }
        b.stop()

        println "  [runtime] without a callback the actor still handled ${bare}; with one it reported ${errs} and handled ${watched}"
        assertEquals(['bare:after'], bare, 'a throwing dispatch does not kill the actor, and its message is not retried')
        assertEquals(['IllegalStateException/boom'], errs, 'the callback is given the throwable AND the offending message')
        assertEquals(['watched:after'], watched, 'the callback changes nothing about what is handled')
    }

    @Test
    void theRecoveryEdgeIsTheActorsAndFiresInsideBecomeTargets() {
        List<String> log = Collections.synchronizedList(new ArrayList<String>())
        ReactorHandler<String, String> second, safe
        safe = { ActorContext<String> ctx, String m -> log << "safe:${m}".toString(); m } as ReactorHandler<String, String>
        second = boomOn('boom', log, 'second')
        Actor<String> a = Actor.reactor({ ActorContext<String> ctx, String m ->
            if (m == 'go') { ctx.become(second); return m }
            log << "first:${m}".toString()
            m
        } as ReactorHandler<String, String>)
        a.onError({ ActorContext<String> ctx, Throwable t, String msg -> log << "onError:${msg}".toString(); ctx.become(safe) } as TriConsumer<ActorContext<String>, Throwable, String>)
        a.send('go'); a.send('boom'); a.send('next')
        waitUntil { log.any { it.startsWith('safe:') } }
        a.stop()
        println "  [runtime] a throw inside a become target: ${log}"
        assertEquals(['onError:boom', 'safe:next'], log,
            'the callback fires for a throw in ANY phase, and its become decides where the next message lands')
    }

    @Test
    void aCallbackCannotRescueTheSendAndGetReply() {
        Actor<String> a = Actor.reactor(boomOn('boom', Collections.synchronizedList(new ArrayList<String>()), 'x'))
        a.onError({ Throwable t, String msg -> } as BiConsumer<Throwable, String>)
        def reply = a.sendAndGet('boom')
        waitUntil { reply.isDone() }
        boolean exceptionally = reply.isCompletedExceptionally()
        a.stop()
        println "  [runtime] with a callback installed, the sendAndGet reply is exceptional: ${exceptionally}"
        assertTrue(exceptionally, 'an onError observes the error; it does not complete the caller\'s reply normally')
    }

    @Test
    void aFailedDispatchSimplyDoesNotAdvanceTheState() {
        Actor<String> a = Actor.stateful(0, { ActorContext<String> ctx, Integer s, String m ->
            if (m == 'boom') throw new IllegalStateException('boom')
            s + 1
        } as StatefulHandler<Integer, String>)
        Object first = a.sendAndGet('a').get(5, TimeUnit.SECONDS)
        def boom = a.sendAndGet('boom')
        waitUntil { boom.isDone() }
        Object after = a.sendAndGet('b').get(5, TimeUnit.SECONDS)
        a.stop()
        println "  [runtime] state ${first} → (throw) → ${after}"
        assertEquals([1, 2], [first, after],
            'the failed dispatch neither advances nor rolls back the state — it simply does not happen')
    }
}
