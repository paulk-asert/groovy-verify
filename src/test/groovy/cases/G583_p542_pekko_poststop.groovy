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

import static cases.G581_p540_pekko_stopped.*

/** 'P542 Pekko PostStop' — Phase 542, the Pekko pack's slice 5: a registered PostStop handler runs once after a handler
 *  returned Behaviors.stopped(), on the state it left (measured in PekkoSemanticsTest), and nothing observes the actor
 *  after it. So it neither assumes nor owes the class invariant, and an onSignal(PostStop, this::h) step no longer
 *  withdraws Phase 540's release. Any other signal step still does. */
class G583_p542_pekko_poststop {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A Pekko PostStop handler runs on the stopped state, outside the class invariant: neither assumed nor owed, so the stopped() release stands beside it.'

    static final String WITH_POSTSTOP = 'newReceiveBuilder().onMessage(Greeted, this::onGreeted).onSignal(PostStop, this::onPostStop).build()'

    /** The blog's bot as written, plus a PostStop handler whose body is {@code body}. */
    static String withPostStop(String body, Map opts = [:]) {
        helloBot(LIVE, AS_WRITTEN, [receive: opts.receive ?: WITH_POSTSTOP,
            extra: "    private Behavior<Greeted> onPostStop(${opts.param ?: 'PostStop'} signal) {\n${body}\n    }\n" + (opts.extra ?: '')])
    }

    static final String LOGS = '''        getContext().getLog().info("stopped after $greetingCounter greetings")
        this'''

    static final String OUTSIDE = '[pack fact] HelloWorldBot#onPostStop — the class invariant is neither assumed nor owed in onPostStop: it runs after the actor stops (pekko pack)'

    static final List<Map> CASES = [
        [group: 'P542 Pekko PostStop', name: 'the blog\'s bot with a PostStop handler: the release stands, the handler runs outside the invariant', ok: true,
         trusted: OUTSIDE,
         src: withPostStop(LOGS)],
        [group: 'P542 Pekko PostStop', name: 'the handler may not assume the invariant: the stopped state breaks it',
         expect: ['Assertion may not hold: (greetingCounter < max)', 'counterexample: greetingCounter = 0, max = 0'],
         src: withPostStop('''        assert greetingCounter < max
        this''')],
        [group: 'P542 Pekko PostStop', name: 'nor does it owe it: nothing sees the state after', ok: true,
         src: withPostStop('''        greetingCounter = -1
        this''')],
        [group: 'P542 Pekko PostStop', name: 'a handler typed Signal sees other signals too: no release', expect: BROKEN_AT_STOP,
         src: withPostStop(LOGS, [param: 'Signal', receive: 'newReceiveBuilder().onMessage(Greeted, this::onGreeted).onSignal(Signal, this::onPostStop).build()'])],
        [group: 'P542 Pekko PostStop', name: 'onSignal(PostStop, …) to a handler taking any Signal: no release', expect: BROKEN_AT_STOP,
         src: withPostStop(LOGS, [param: 'Signal'])],
        [group: 'P542 Pekko PostStop', name: 'the step\'s class decides what is delivered: onSignal(Terminated, …) to a PostStop handler, no release',
         expect: BROKEN_AT_STOP,   // @TypeChecked accepts it
         src: withPostStop(LOGS, [receive: 'newReceiveBuilder().onMessage(Greeted, this::onGreeted).onSignal(Terminated, this::onPostStop).build()'])],
        [group: 'P542 Pekko PostStop', name: 'any other signal step still withdraws the release', expect: BROKEN_AT_STOP,
         src: withPostStop(LOGS, [param: 'Terminated', receive: 'newReceiveBuilder().onMessage(Greeted, this::onGreeted).onSignal(Terminated, this::onPostStop).build()'])],
        [group: 'P542 Pekko PostStop', name: 'a PostStop handler also called directly is no handler: no release',
         expect: BROKEN_AT_STOP,
         src: withPostStop(LOGS, [extra: '    private Behavior<Greeted> halt() {\n        onPostStop(PostStop.instance())\n    }\n'])],
        [group: 'P542 Pekko PostStop', name: 'where a public method could read the state, the handler is an ordinary one: assumes and owes it', ok: true,
         src: helloBot(LIVE, '''        if (greetingCounter + 1 < max) greetingCounter++
        return this''', [receive: WITH_POSTSTOP,
             extra: '    private Behavior<Greeted> onPostStop(PostStop signal) {\n        assert greetingCounter < max\n        this\n    }\n    int greetings() { greetingCounter }\n'])],
        [group: 'P542 Pekko PostStop', name: 'VERIFY_TRUST=deny: the release fails the compile, at the handler\'s parameter', trustMode: 'deny',
         expect: ['Trusted without proof (VERIFY_TRUST=deny): ' + OUTSIDE, '@ line 32, column 42.'],   // onPostStop's parameter
         src: withPostStop(LOGS)],
    ]
}
