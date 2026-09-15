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
import groovy.concurrent.Cancellable
import groovy.concurrent.ReactorHandler
import org.junit.jupiter.api.Test

import java.time.Duration

import static org.junit.jupiter.api.Assertions.assertEquals
import static org.junit.jupiter.api.Assertions.assertTrue

/**
 * What {@code ActorContext.scheduleOnce} / {@code scheduleAtFixedRate} really do, measured before Phase 297
 * models them (the Phase 289 rule: the checker models {@code groovy.concurrent} as it BEHAVES).
 *
 * <p>A timer is a message source the protocol knows nothing about: the actor sends it to itself. Two facts
 * decide the whole model. It lands in whichever behaviour is current WHEN IT FIRES, not the one that armed it
 * — so a timeout armed just before a {@code become} arrives in the phase moved to. And a repeat goes on firing
 * across every {@code become} — so a repeat whose message a phase stashes grows that stash with the CLOCK
 * rather than with anything a peer does. A scheduled message is otherwise an ordinary one: dispatched, stashed
 * and replayed like any other.
 */
class ActorTimerSemanticsTest {

    // not `await` — in Groovy 6 `await { … }` is the async await, which would try to await the closure itself
    private static void waitUntil(Closure<Boolean> cond) {
        long end = System.currentTimeMillis() + 5000
        while (!cond() && System.currentTimeMillis() < end) Thread.sleep(20)
    }

    @Test
    void aTimerLandsInThePhaseCurrentWhenItFiresNotTheOneThatArmedIt() {
        List<String> log = Collections.synchronizedList(new ArrayList<String>())
        ReactorHandler<String, String> later
        later = { ActorContext<String> ctx, String m -> log << "later:${m}".toString(); m } as ReactorHandler<String, String>
        Actor<String> a = Actor.reactor({ ActorContext<String> ctx, String m ->
            if (m == 'arm') { ctx.scheduleOnce('tick', Duration.ofMillis(150)); ctx.become(later); return m }
            log << "armer:${m}".toString()
            m
        } as ReactorHandler<String, String>)
        a.send('arm')
        waitUntil { log.any { it.endsWith(':tick') } }
        a.stop()
        println "  [runtime] a timeout armed then become()d away from: ${log}"
        assertEquals(['later:tick'], log, 'the timer fires into the CURRENT behaviour, not the one that armed it')
    }

    @Test
    void aRepeatKeepsFiringAcrossABecomeAndStopsAtStop() {
        List<String> ticks = Collections.synchronizedList(new ArrayList<String>())
        ReactorHandler<String, String> other
        other = { ActorContext<String> ctx, String m -> ticks << "other:${m}".toString(); m } as ReactorHandler<String, String>
        Actor<String> a = Actor.reactor({ ActorContext<String> ctx, String m ->
            if (m == 'go') { ctx.scheduleAtFixedRate('tick', Duration.ofMillis(30), Duration.ofMillis(30)); ctx.become(other); return m }
            m
        } as ReactorHandler<String, String>)
        a.send('go')
        waitUntil { ticks.size() >= 3 }
        List<String> seen = new ArrayList<String>(ticks)
        a.stop()
        int atStop = ticks.size()
        Thread.sleep(300)
        int grew = ticks.size() - atStop
        println "  [runtime] repeats after the become: ${seen.take(3)}; after stop() it grew by ${grew}"
        assertTrue(seen.every { it == 'other:tick' } && seen.size() >= 3, 'the repeat belongs to the ACTOR, and fires on across a become')
        assertEquals(0, grew, 'stop() does cancel the repeat')
    }

    @Test
    void aScheduledMessageIsStashedAndReplayedLikeAnyOther() {
        List<String> log = Collections.synchronizedList(new ArrayList<String>())
        ReactorHandler<String, String> open
        open = { ActorContext<String> ctx, String m -> log << "open:${m}".toString(); m } as ReactorHandler<String, String>
        Actor<String> a = Actor.reactor({ ActorContext<String> ctx, String m ->
            if (m == 'arm') { ctx.scheduleOnce('tick', Duration.ofMillis(100)); return m }
            if (m == 'release') { ctx.become(open); ctx.unstashAll(); return m }
            ctx.stash()
            m
        } as ReactorHandler<String, String>)
        a.send('arm')
        Thread.sleep(300)
        List<String> whileStashing = new ArrayList<String>(log)
        a.send('release')
        waitUntil { log.any { it.endsWith(':tick') } }
        a.stop()
        println "  [runtime] while the phase stashed: ${whileStashing}; after the replay: ${log}"
        assertEquals([], whileStashing, 'a scheduled message is stashable like any other — it did not reach a handler')
        assertEquals(['open:tick'], log, 'and it is replayed into the phase that handles it')
    }

    @Test
    void aRepeatIntoAStashingPhaseGrowsTheStashWithTheClock() {
        List<String> drained = Collections.synchronizedList(new ArrayList<String>())
        ReactorHandler<String, String> drain
        drain = { ActorContext<String> ctx, String m -> drained << m; m } as ReactorHandler<String, String>
        Actor<String> a = Actor.reactor({ ActorContext<String> ctx, String m ->
            if (m == 'go') { ctx.scheduleAtFixedRate('tick', Duration.ofMillis(20), Duration.ofMillis(20)); return m }
            if (m == 'drain') { ctx.become(drain); ctx.unstashAll(); return m }
            ctx.stash()
            m
        } as ReactorHandler<String, String>)
        a.send('go')
        Thread.sleep(600)                       // nothing at all happens here: no peer, no send
        a.send('drain')
        waitUntil { drained.size() > 0 }
        Thread.sleep(200)
        int ticks = drained.count { it == 'tick' }
        a.stop()
        println "  [runtime] ticks stashed by 600ms of idling at a 20ms period: ${ticks}"
        assertTrue(ticks > 15, "the stash grows with ELAPSED TIME, not with what a peer does (got ${ticks})")
    }

    @Test
    void aKeptCancellableStopsTheRepeat() {
        List<String> log = Collections.synchronizedList(new ArrayList<String>())
        Cancellable[] held = new Cancellable[1]
        Actor<String> a = Actor.reactor({ ActorContext<String> ctx, String m ->
            if (m == 'go') { held[0] = ctx.scheduleAtFixedRate('tick', Duration.ofMillis(30), Duration.ofMillis(30)); return m }
            if (m == 'off') { log << "cancel=${held[0].cancel()}".toString(); return m }
            log << m
            m
        } as ReactorHandler<String, String>)
        a.send('go')
        waitUntil { log.count { it == 'tick' } >= 2 }
        a.send('off')
        Thread.sleep(200)
        int atCancel = log.size()
        Thread.sleep(300)
        int grew = log.size() - atCancel
        a.stop()
        println "  [runtime] ${log.take(4)}; after cancel() it grew by ${grew}"
        assertTrue(log.contains('cancel=true'), 'cancel() reports that it stopped a live repeat')
        assertEquals(0, grew, 'and the repeat really stops — which is why a KEPT Cancellable withholds the claim')
    }
}
