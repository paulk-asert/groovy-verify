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
 * 'P297 actor timers' — {@code ActorContext.scheduleOnce} / {@code scheduleAtFixedRate}: the last corner of the
 * Actor API, and a message source the protocol knows nothing about. Measured: a timer fires into whichever
 * behaviour is current AT THAT MOMENT (not the one that armed it), a repeat goes on firing across every
 * {@code become}, and a scheduled message is dispatched, stashed and replayed like any other.
 */
class G347_p297_actor_timers {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 297 actor timers: `ctx.scheduleOnce` / `ctx.scheduleAtFixedRate` schedule a message the actor sends to ITSELF, and measurement decides where it lands — in whichever behaviour is current when the timer fires, not the one that armed it, with a repeat firing on across every become. So the checker asks what each phase REACHABLE from the arming point does with that message: one that throws kills the actor\'s own message (the armed-a-timeout-then-moved-on bug), and one that stashes a REPEAT is an unbounded stash with certainty rather than possibility — the actor feeds it from the clock, so nothing a peer does is needed to exhaust the heap (measured at 40 messages in 600ms for a 20ms period). A phase that merely IGNORES the message is deliberately not reported: dropping a timeout that no longer applies is the idiom. Nothing is claimed when the become-graph is unreadable, the message is not a literal, an onError arms a timer, or the method cancels anything.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    /** An actor that arms a timer in its first phase, then becomes `later`. */
    static String timed(String schedule, String laterBody, String tail = '') { """class C {
                        static void run() {
                            ReactorHandler<String, String> later
                            later = { ActorContext<String> ctx, String m -> ${laterBody} } as ReactorHandler<String, String>
                            Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                                if (m == 'go') { ${schedule}; ctx.become(later); return m }
                                m
                            } as ReactorHandler<String, String>)
                            gate.send('go')${tail}
                        }
                    }""" }

    static final String ONCE = "ctx.scheduleOnce('timeout', Duration.ofMillis(500))"
    static final String REPEAT = "ctx.scheduleAtFixedRate('tick', Duration.ofMillis(50), Duration.ofMillis(50))"

    static final List<Map> CASES = [
        // ── the classic bug: arm a timeout, move on, and the phase you moved to blows up on it.
        [group: 'P297 actor timers', name: 'a timeout armed before a become lands in a phase that throws on it',
         expect: "Scheduled message rejected by its own actor: 'gate' in run() schedules 'timeout' for itself (line 8), but a timer fires into whichever behaviour is current AT THAT MOMENT, not the one that armed it — and phase 'later', reachable from there, throws on 'timeout'",
         src: tc(timed(ONCE, "throw new IllegalStateException('unexpected ' + m)"))],

        // ── the phase that moved on handles it: the ordinary shape, nothing claimed.
        [group: 'P297 actor timers', name: 'a phase that handles the scheduled message is left alone', ok: true,
         refute: ['Scheduled message', 'Unbounded stash'],
         src: tc(timed(ONCE, "if (m == 'timeout') { return 'expired' }\n                                m"))],

        // ── a phase that merely IGNORES it is the idiom for a timeout that no longer applies: NOT a finding.
        [group: 'P297 actor timers', name: 'a phase that ignores a stale timeout is the idiom, not a finding', ok: true,
         refute: ['Scheduled message', 'Unbounded stash'],
         src: tc(timed(ONCE, "m"))],

        // ── the repeat into a stashing phase: the actor feeds its own stash from the clock.
        [group: 'P297 actor timers', name: 'a repeating timer into a stashing phase grows the stash from the clock',
         expect: "Unbounded stash from the actor's own timer: 'gate' in run() repeats 'tick' (scheduleAtFixedRate, line 9) and phase 'later', reachable from there, stashes it",
         src: tc(timed(REPEAT, "ctx.stash()\n                                m"))],

        // ── a scheduleOnce into the same stashing phase is Phase 292's business, not this check's.
        [group: 'P297 actor timers', name: 'a one-shot timer into a stashing phase is not an unbounded stash',
         expect: 'Stashed messages are never replayed',
         refute: 'Unbounded stash',
         src: tc(timed(ONCE, "ctx.stash()\n                                m"))],

        // ── withheld: the Cancellable is KEPT, so the repeat may yet be stopped and nothing is claimed.
        //    (Phase 292 still says the stash is never replayed — a different, true finding.)
        [group: 'P297 actor timers', name: 'a kept Cancellable withholds the unbounded claim',
         expect: 'Stashed messages are never replayed',
         refute: ['Unbounded stash', 'Scheduled message'],
         src: tc('''class C {
                        static void run() {
                            ReactorHandler<String, String> later
                            later = { ActorContext<String> ctx, String m -> ctx.stash(); m } as ReactorHandler<String, String>
                            Actor<String> gate = Actor.reactor({ ActorContext<String> ctx, String m ->
                                if (m == 'go') {
                                    Cancellable beat = ctx.scheduleAtFixedRate('tick', Duration.ofMillis(50), Duration.ofMillis(50))
                                    ctx.become(later)
                                    return m
                                }
                                m
                            } as ReactorHandler<String, String>)
                            gate.send('go')
                        }
                    }''')],

        // ── withheld: a non-literal scheduled message says nothing about where it lands.
        [group: 'P297 actor timers', name: 'a non-literal scheduled message withholds the claim', ok: true,
         refute: ['Scheduled message', 'Unbounded stash'],
         src: tc(timed("ctx.scheduleOnce(m, Duration.ofMillis(500))", "throw new IllegalStateException('unexpected ' + m)"))],
    ]
}
