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
import groovy.concurrent.ActorOptions
import groovy.concurrent.ReactorHandler
import org.junit.jupiter.api.Test

import java.util.concurrent.TimeUnit

import static org.junit.jupiter.api.Assertions.assertEquals
import static org.junit.jupiter.api.Assertions.assertTrue

/**
 * What {@code ActorContext.stash()} / {@code unstashAll()} really do, measured before anything is modelled
 * (the Phase 289 rule: the checker models {@code groovy.concurrent} as it BEHAVES).
 *
 * <p>The property the stash check rests on is conservation: a stashed message comes back ONLY through
 * {@code unstashAll()}. If no behaviour ever calls it, the message never reaches a handler again, and at
 * {@code stop()} it is rejected — a {@code sendAndGet} caller's reply fails, a plain send is discarded. The
 * control pins the healthy shape: {@code become} a new behaviour, {@code unstashAll()}, and the deferred
 * messages are replayed, oldest first, ahead of anything sent since.
 */
class ActorStashSemanticsTest {

    // not `await` — in Groovy 6 `await { … }` is the async await, which would try to await the closure itself
    private static void waitUntil(Closure<Boolean> cond) {
        long end = System.currentTimeMillis() + 5000
        while (!cond() && System.currentTimeMillis() < end) Thread.sleep(20)
    }

    @Test
    void aStashedMessageThatIsNeverUnstashedIsLost() {
        List<String> seen = Collections.synchronizedList(new ArrayList<String>())
        Actor<String> a = Actor.reactor({ ActorContext<String> ctx, String m ->
            if (m.startsWith('defer')) { ctx.stash(); return null }
            seen << m
            m
        } as ReactorHandler<String, String>)
        def reply = a.sendAndGet('defer-asked')
        a.send('defer-told')
        a.send('ordinary')
        waitUntil {seen.contains('ordinary') }
        a.stop()
        String outcome
        try {
            reply.get(5, TimeUnit.SECONDS)
            outcome = 'completed normally'
        } catch (java.util.concurrent.TimeoutException ignored) {
            outcome = 'never completed'
        } catch (Exception e) {
            Throwable c = e.cause ?: e
            outcome = "failed: ${c.class.simpleName}: ${c.message}"
        }
        println "  [runtime] handler saw ${seen}; the stashed sendAndGet at stop(): ${outcome}"
        assertEquals(['ordinary'], seen, 'a stashed message must never reach a handler without unstashAll()')
        assertTrue(outcome.startsWith('failed: IllegalStateException'),
            "the stashed sendAndGet must be rejected at stop(), got: ${outcome}")
    }

    /**
     * Phase 292 slice 2 — a BOUNDED stash overrun by one: bound 2, three messages stashed, then the trigger that
     * replays. Records, per policy, which sendAndGet replies failed and what the replay delivered. The stash-bound
     * check models exactly these outcomes.
     */
    private static Map overrun(ActorOptions.StashOverflow policy) {
        List<String> seen = Collections.synchronizedList(new ArrayList<String>())
        Actor<String> a = Actor.reactor({ ActorContext<String> ctx, String m ->
            if (m == 'open') {
                ctx.become({ ActorContext<String> c, String n -> seen << n; n } as ReactorHandler<String, String>)
                ctx.unstashAll()
                return m
            }
            ctx.stash()
            null
        } as ReactorHandler<String, String>, ActorOptions.DEFAULTS.withStashBound(2, policy))
        Map<String, String> replies = new LinkedHashMap<String, String>()
        try {
            def r1 = a.sendAndGet('m1'), r2 = a.sendAndGet('m2'), r3 = a.sendAndGet('m3')
            a.send('open')
            [m1: r1, m2: r2, m3: r3].each { String k, def r ->
                try { replies[k] = "ok(${r.get(5, TimeUnit.SECONDS)})" }
                catch (Exception e) { Throwable c = e.cause ?: e; replies[k] = "failed(${c.class.simpleName}: ${c.message})" }
            }
            waitUntil { seen.size() >= 2 }
        } finally {
            a.stop()
        }
        println "  [runtime] stash bound 2, ${policy}: replies ${replies}; replayed ${seen}"
        [replies: replies, seen: new ArrayList<String>(seen)]
    }

    @Test
    void failThrowsFromStashSoTheOverflowingMessageFails() {
        Map r = overrun(ActorOptions.StashOverflow.FAIL)
        assertTrue(((Map) r.replies).m3.toString().startsWith('failed(IllegalStateException'), "FAIL: the 3rd reply must fail, got ${r.replies}")
        assertEquals(['m1', 'm2'], r.seen, 'FAIL: the two stashed messages are replayed')
    }

    @Test
    void dropOldestEvictsTheFirstStashedMessage() {
        Map r = overrun(ActorOptions.StashOverflow.DROP_OLDEST)
        assertTrue(((Map) r.replies).m1.toString().startsWith('failed(IllegalStateException'), "DROP_OLDEST: the 1st reply must fail, got ${r.replies}")
        assertEquals(['m2', 'm3'], r.seen, 'DROP_OLDEST: the two newest are replayed')
    }

    @Test
    void rejectRefusesTheOverflowingMessage() {
        Map r = overrun(ActorOptions.StashOverflow.REJECT)
        assertTrue(((Map) r.replies).m3.toString().startsWith('failed(IllegalStateException'), "REJECT: the 3rd reply must fail, got ${r.replies}")
        assertEquals(['m1', 'm2'], r.seen, 'REJECT: the two stashed messages are replayed')
    }

    @Test
    void unstashAllAfterBecomeReplaysTheStashOldestFirst() {
        List<String> seen = Collections.synchronizedList(new ArrayList<String>())
        Actor<String> a = Actor.reactor({ ActorContext<String> ctx, String m ->
            if (m == 'open') {
                ctx.become({ ActorContext<String> c, String n -> seen << n; n } as ReactorHandler<String, String>)
                ctx.unstashAll()
                return m
            }
            ctx.stash()
            null
        } as ReactorHandler<String, String>)
        try {
            a.send('first')
            a.send('second')
            a.send('open')
            a.send('third')
            waitUntil {seen.size() >= 3 }
            println "  [runtime] after become + unstashAll the new behaviour saw ${seen}"
            assertEquals(['first', 'second', 'third'], seen,
                'unstashAll must replay the stash FIFO, ahead of messages sent since')
        } finally {
            a.stop()
        }
    }
}
