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

/** 'P540 Pekko stopped' — Phase 540, the Pekko pack's slice 3: after a handler returns Behaviors.stopped() no message is
 *  delivered again (measured in PekkoSemanticsTest), so the class invariant — the property of the actor's live states —
 *  is not owed on that exit. The blog's HelloWorldBot, exactly as written, proves its live-state invariant
 *  greetingCounter < max. Measured too: an onSignal(PostStop) handler runs once after, on that state, so a class with
 *  any onSignal step gets no release; nor does one whose state anything else could observe. */
class G581_p540_pekko_stopped {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A Pekko handler returning Behaviors.stopped() owes no class invariant on that exit (nothing is delivered after); the blog\'s bot proves its live-state invariant as written.'

    static final String PK = 'import org.apache.pekko.actor.typed.*\nimport org.apache.pekko.actor.typed.javadsl.*\n' +
        'import org.apache.pekko.actor.typed.javadsl.ActorContext\n'
    static final String MSGS = '''
record Greet(String whom, ActorRef<Greeted> replyTo) {}
record Greeted(String whom, ActorRef<Greet> from) {}
'''
    static String pk(String t) { HDR + PK + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" + t.stripIndent() + MSGS }

    static final String LIVE = 'max >= 1 && 0 <= greetingCounter && greetingCounter < max'

    /** The blog's onGreeted, as written. */
    static final String AS_WRITTEN = '''        greetingCounter++
        getContext().getLog().info("Greeting $greetingCounter for ${message.whom}")
        if (greetingCounter == max) {
            return Behaviors.stopped()
        } else {
            message.from.tell(new Greet(message.whom, getContext().getSelf()))
            return this
        }'''

    static final String RECEIVE = 'newReceiveBuilder().onMessage(Greeted, this::onGreeted).build()'
    static final String HANDLER = 'private Behavior<Greeted> onGreeted(Greeted message)'

    /** The blog's HelloWorldBot (before its {@code extra} members), under the class invariant {@code inv}. */
    static String helloBot(String inv, String body, Map opts = [:]) {
        String fields = opts.fields ?: '    private final int max\n    private int greetingCounter\n'
        pk("""@Invariant({ ${inv} })
class HelloWorldBot extends AbstractBehavior<Greeted> {
${fields}
    @Requires({ max >= 1 })
    HelloWorldBot(ActorContext<Greeted> context, int max) {
        super(context)
        this.max = max
    }

    @Override
    Receive<Greeted> createReceive() {
        ${opts.receive ?: RECEIVE}
    }
${opts.ensures ?: ''}
    ${opts.handler ?: HANDLER} {
${body}
    }
${opts.extra ?: ''}}
${opts.after ?: ''}""")
    }

    static final String BROKEN = 'Cannot prove class invariant of onGreeted holds at method exit'
    /** Owed at the stopped() exit: the counter has just reached max there. */
    static final List<String> BROKEN_AT_STOP = [BROKEN, 'counterexample: greetingCounter = 0, max = 1']

    static final List<Map> CASES = [
        // ---------- the blog's bot, as written ----------
        [group: 'P540 Pekko stopped', name: 'the blog\'s bot as written proves its live-state invariant', ok: true,
         trusted: '[pack fact] HelloWorldBot#onGreeted — the class invariant is not owed where it returns Behaviors.stopped() (pekko pack)',
         src: helloBot(LIVE, AS_WRITTEN)],
        [group: 'P540 Pekko stopped', name: '… whose weaker invariant greetingCounter <= max is still not inductive: refuted at an unreachable state',
         expect: [BROKEN, 'counterexample: greetingCounter = 1, max = 1'],
         src: helloBot('max >= 1 && 0 <= greetingCounter && greetingCounter <= max', AS_WRITTEN)],
        [group: 'P540 Pekko stopped', name: 'returning this where the blog stops: the live-state invariant is owed, and broken', expect: BROKEN_AT_STOP,
         src: helloBot(LIVE, AS_WRITTEN.replace('return Behaviors.stopped()', 'return this'))],
        [group: 'P540 Pekko stopped', name: 'returning Behaviors.same() where the blog stops: still owed', expect: BROKEN_AT_STOP,
         src: helloBot(LIVE, AS_WRITTEN.replace('return Behaviors.stopped()', 'return Behaviors.same()'))],

        // ---------- a postcondition is still owed on the stopped exit ----------
        [group: 'P540 Pekko stopped', name: 'a true postcondition on the stopped exit proves', ok: true,
         src: helloBot(LIVE, AS_WRITTEN, [ensures: '    @Ensures({ greetingCounter == old.greetingCounter + 1 })'])],
        [group: 'P540 Pekko stopped', name: 'a false postcondition on the stopped exit refutes',
         expect: ['Cannot prove postcondition of onGreeted', 'counterexample: greetingCounter = 0, max = 1'],
         src: helloBot(LIVE, AS_WRITTEN, [ensures: '    @Ensures({ greetingCounter < max })'])],

        // ---------- anything that could see the stopped state withdraws the release ----------
        [group: 'P540 Pekko stopped', name: 'an onSignal(PostStop) closure runs after stopped(), unverified: no release (a PostStop method is Phase 542\'s)', expect: BROKEN_AT_STOP,
         src: helloBot(LIVE, AS_WRITTEN, [receive: 'newReceiveBuilder().onMessage(Greeted, this::onGreeted).onSignal(PostStop, { PostStop s -> this }).build()'])],
        [group: 'P540 Pekko stopped', name: 'a public method could read the stopped state: no release', expect: BROKEN_AT_STOP,
         src: helloBot(LIVE, AS_WRITTEN, [extra: '    int greetings() { greetingCounter }\n'])],
        [group: 'P540 Pekko stopped', name: 'a Groovy property is a public getter: no release', expect: BROKEN_AT_STOP,
         src: helloBot(LIVE, AS_WRITTEN, [fields: '    private final int max\n    private int greetingCounter\n    String label\n'])],
        [group: 'P540 Pekko stopped', name: 'a parameter of the actor\'s type elsewhere assumes its invariant: no release', expect: BROKEN_AT_STOP,
         src: helloBot(LIVE, AS_WRITTEN, [after: 'class Watcher {\n    static boolean seen(HelloWorldBot b) { b != null }\n}\n'])],
        [group: 'P540 Pekko stopped', name: 'a field of the actor\'s type elsewhere: no release', expect: BROKEN_AT_STOP,
         src: helloBot(LIVE, AS_WRITTEN, [after: 'class Holder {\n    private HelloWorldBot bot\n}\n'])],
        [group: 'P540 Pekko stopped', name: 'a static method reaches no instance\'s state: the release stands', ok: true,
         src: helloBot(LIVE, AS_WRITTEN, [extra: '    static String kind() { \'greeter\' }\n'])],
        [group: 'P540 Pekko stopped', name: 'a public handler is not only the runtime\'s to call: no release', expect: BROKEN_AT_STOP,
         src: helloBot(LIVE, AS_WRITTEN, [handler: 'Behavior<Greeted> onGreeted(Greeted message)', ensures: '    @Requires({ message != null })'])],
        [group: 'P540 Pekko stopped', name: 'a private helper returning stopped() is no handler: its result decides nothing, so no release',
         expect: ['Cannot prove class invariant of halt holds at method exit', 'counterexample: greetingCounter = 0, max = 1', 'fails on: halt()'],
         src: helloBot(LIVE, AS_WRITTEN, [extra: '    private Behavior<Greeted> halt() {\n        greetingCounter = max\n        Behaviors.stopped()\n    }\n'])],
        [group: 'P540 Pekko stopped', name: 'Behaviors.stopped(postStop) runs a callback after: not a claimed value, so no release (a loud skip)',
         expect: 'Skipped verification of postcondition for onGreeted (return expression',
         src: helloBot(LIVE, AS_WRITTEN.replace('return Behaviors.stopped()',
                       'return Behaviors.stopped({ -> } as org.apache.pekko.japi.function.Effect)'))],

        // ---------- the trust is visible ----------
        [group: 'P540 Pekko stopped', name: 'VERIFY_TRUST=deny: the release fails the compile, at the stopped() return', trustMode: 'deny',
         expect: ['Trusted without proof (VERIFY_TRUST=deny): [pack fact] HelloWorldBot#onGreeted — the class invariant is not owed where it returns Behaviors.stopped() (pekko pack)',
                  '@ line 26, column 20.'],   // the `Behaviors.stopped()` return
         src: helloBot(LIVE, AS_WRITTEN)],
    ]
}
