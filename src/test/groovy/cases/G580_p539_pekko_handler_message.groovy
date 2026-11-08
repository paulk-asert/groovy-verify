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

/** 'P539 Pekko handler message' — Phase 539, the Pekko pack's slice 2: a registered handler's message is non-null on
 *  entry with no @Requires. Pekko never delivers null (tell(null) throws at the sender; an ask whose message is null
 *  fails before delivery — both measured in PekkoSemanticsTest), so a private handler referenced only as this::name in
 *  an onMessage / onAnyMessage / onSignal step gets the fact, ledgered as a 'pack fact'. Any other way to reach the
 *  method — a direct call, a stored reference, a non-private method, an overload — and the message is possibly null. */
class G580_p539_pekko_handler_message {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A Pekko handler registered on a receive builder gets a non-null message on entry, a ledgered pack fact; any other caller withdraws it.'

    static final String PK = 'import org.apache.pekko.actor.typed.*\nimport org.apache.pekko.actor.typed.javadsl.*\n' +
        'import org.apache.pekko.actor.typed.javadsl.ActorContext\n'
    static final String MSGS = '''
record Greet(String whom, ActorRef<Greeted> replyTo) {}
record Greeted(String whom, ActorRef<Greet> from) {}
'''
    static String pk(String t) { HDR + PK + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" + t.stripIndent() + MSGS }

    static final String TELL = 'message.from.tell(new Greet(message.whom, getContext().getSelf()))'

    /** A Bot whose handler declaration and receive are given; the handler bumps count and replies through the message. */
    static String bot(String receive, String handlerDecl, String extra = '') {
        pk("""class Bot extends AbstractBehavior<Greeted> {
    int count
    Bot(ActorContext<Greeted> context) { super(context) }
    @Override
    Receive<Greeted> createReceive() { ${receive} }
    @Ensures({ count == old.count + 1 })
    ${handlerDecl} {
        count++
        ${TELL}
        this
    }
${extra}}""")
    }

    static final String RECEIVE = 'newReceiveBuilder().onMessage(Greeted, this::onGreeted).build()'
    static final String HANDLER = 'private Behavior<Greeted> onGreeted(Greeted message)'
    static final String NPE = 'Possible NullPointerException'

    static final List<Map> CASES = [
        // ---------- the blog's bot, as the blog declares its handler ----------
        [group: 'P539 Pekko handler message', name: 'the blog\'s guarded bot with no @Requires on its handler: its invariant proved', ok: true,
         trusted: '[pack fact] HelloWorldBot#onGreeted — message is never null on entry (pekko pack)',
         src: pk('''@Invariant({ max >= 1 && 0 <= greetingCounter && greetingCounter <= max })
                    class HelloWorldBot extends AbstractBehavior<Greeted> {
                        private final int max
                        private int greetingCounter

                        @Requires({ max >= 1 })
                        HelloWorldBot(ActorContext<Greeted> context, int max) {
                            super(context)
                            this.max = max
                        }

                        @Override
                        Receive<Greeted> createReceive() {
                            newReceiveBuilder().onMessage(Greeted, this::onGreeted).build()
                        }

                        private Behavior<Greeted> onGreeted(Greeted message) {
                            if (greetingCounter == max) return Behaviors.stopped()
                            greetingCounter++
                            getContext().getLog().info("Greeting $greetingCounter for ${message.whom}")
                            if (greetingCounter == max) return Behaviors.stopped()
                            message.from.tell(new Greet(message.whom, getContext().getSelf()))
                            return this
                        }
                    }''')],

        // ---------- the registrations that deliver ----------
        [group: 'P539 Pekko handler message', name: 'onMessage(Class, this::h)', ok: true, src: bot(RECEIVE, HANDLER)],
        [group: 'P539 Pekko handler message', name: 'onAnyMessage(this::h)', ok: true,
         src: bot('newReceiveBuilder().onAnyMessage(this::onGreeted).build()', HANDLER)],
        [group: 'P539 Pekko handler message', name: 'a predicate and a handler, both registered: both get the fact', ok: true,
         src: bot('newReceiveBuilder().onMessage(Greeted, this::wanted, this::onGreeted).build()', HANDLER,
                  '    @Ensures({ result == (m.whom != null) })\n    private boolean wanted(Greeted m) { m.whom != null }\n')],
        [group: 'P539 Pekko handler message', name: 'the Groovy method-pointer spelling this.&h', ok: true,
         src: bot('newReceiveBuilder().onMessage(Greeted, this.&onGreeted).build()', HANDLER)],

        // ---------- every other way in withdraws the fact ----------
        [group: 'P539 Pekko handler message', name: 'a public handler: any caller could pass null', expect: NPE,
         src: bot(RECEIVE, 'Behavior<Greeted> onGreeted(Greeted message)')],
        [group: 'P539 Pekko handler message', name: 'a private handler also called directly', expect: NPE,
         src: bot(RECEIVE, HANDLER, '    void poke() { onGreeted(null) }\n')],
        [group: 'P539 Pekko handler message', name: 'a private handler also stored as a reference', expect: NPE,
         src: bot(RECEIVE, HANDLER, '    def stash() { this::onGreeted }\n')],
        [group: 'P539 Pekko handler message', name: 'an overloaded handler name', expect: NPE,
         src: bot(RECEIVE, HANDLER, '    private Behavior<Greeted> onGreeted(Greet g) { this }\n')],
        [group: 'P539 Pekko handler message', name: 'a private method never registered', expect: NPE,
         src: bot('newReceiveBuilder().onAnyMessage(this::other).build()', HANDLER,
                  '    private Behavior<Greeted> other(Greeted g) { this }\n')],
        [group: 'P539 Pekko handler message', name: 'a private method of a class that is not a behaviour', expect: NPE,
         src: pk('''class Plain {
                        int count
                        @Ensures({ count == old.count + 1 })
                        private int onGreeted(Greeted message) { count++; message.whom.size() }
                    }''')],
        [group: 'P539 Pekko handler message', name: 'a handler registered through a step that passes no message (onMessageEquals) is not claimed',
         expect: NPE,
         src: bot('newReceiveBuilder().onMessageEquals(null, this::onGreeted).build()', HANDLER)],
        [group: 'P539 Pekko handler message', name: 'another behaviour registering its own method of the same name does not count', expect: NPE,
         src: bot('newReceiveBuilder().onAnyMessage(this::other).build()', HANDLER,
                  '    private Behavior<Greeted> other(Greeted g) { this }\n') + '''
@TypeChecked(extensions = 'verification.VerifyChecker')
class Other extends AbstractBehavior<Greeted> {
    Other(ActorContext<Greeted> context) { super(context) }
    Receive<Greeted> createReceive() { newReceiveBuilder().onMessage(Greeted, this::onGreeted).build() }
    private Behavior<Greeted> onGreeted(Greeted message) { this }
}
'''],
        [group: 'P539 Pekko handler message', name: 'a registered pointer to the same name on another object does not count', expect: NPE,
         src: bot('newReceiveBuilder().onMessage(Greeted, helper::onGreeted).build()', HANDLER,
                  '    Helper helper = new Helper()\n') + '''
class Helper {
    Behavior<Greeted> onGreeted(Greeted message) { Behaviors.same() }
}
'''],

        // ---------- the trust is visible ----------
        [group: 'P539 Pekko handler message', name: 'VERIFY_TRUST=deny: the pack fact fails the compile, at the parameter', trustMode: 'deny',
         expect: ['Trusted without proof (VERIFY_TRUST=deny): [pack fact] Bot#onGreeted — message is never null on entry (pekko pack)',
                  '@ line 12, column 41.'],   // `Greeted message`, in the handler's signature
         src: bot(RECEIVE, HANDLER)],
    ]
}
