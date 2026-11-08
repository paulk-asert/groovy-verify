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

/** 'P538 Pekko pack' — Phase 538, the Pekko typed-actor pack's slice 1: a handler's own body stays in the fragment.
 *  A returned behaviour (Behaviors.same() / stopped() / empty(), a built receive) is an opaque non-null value,
 *  ActorRef.tell changes nothing the sender reads (a pack-shipped skeleton; a null message throws), and
 *  super(context) in an AbstractBehavior subclass runs no subclass code. Each fact measured in PekkoSemanticsTest.
 *  The handlers here carry @Requires({ message != null }); Phase 539 (G580) makes it unnecessary for a registered
 *  private handler. */
class G579_p538_pekko_pack {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Pekko typed handlers verify: returned behaviours as opaque values, tell framed as writing nothing of the sender\'s, super(context) as no effect.'

    static final String PK = 'import org.apache.pekko.actor.typed.*\nimport org.apache.pekko.actor.typed.javadsl.*\n' +
        'import org.apache.pekko.actor.typed.javadsl.ActorContext\n'
    static final String MSGS = '''
record Greet(String whom, ActorRef<Greeted> replyTo) {}
record Greeted(String whom, ActorRef<Greet> from) {}
'''
    static String pk(String t) { HDR + PK + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" + t.stripIndent() + MSGS }

    /** A handler class whose onGreeted claims the counter went up by one. */
    static String bot(String handlerBody) {
        pk("""class Bot extends AbstractBehavior<Greeted> {
    int count
    Bot(ActorContext<Greeted> context) { super(context) }
    @Override
    Receive<Greeted> createReceive() { newReceiveBuilder().onMessage(Greeted, this::onGreeted).build() }
    @Requires({ message != null })
    @Ensures({ count == old.count + 1 })
    Behavior<Greeted> onGreeted(Greeted message) {
${handlerBody}
    }
}""")
    }

    /** The blog's HelloWorldBot, with a class invariant; {@code guard} decides whether a late greeting is ignored. */
    static String helloBot(String handlerBody) {
        pk("""@Invariant({ max >= 1 && 0 <= greetingCounter && greetingCounter <= max })
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

    @Requires({ message != null })
    private Behavior<Greeted> onGreeted(Greeted message) {
${handlerBody}
    }
}""")
    }

    static final List<Map> CASES = [
        // ---------- the blog's bot ----------
        [group: 'P538 Pekko pack', name: 'the blog\'s bot, ignoring a late greeting: its invariant proved', ok: true,
         src: helloBot('''        if (greetingCounter == max) return Behaviors.stopped()   // a late greeting: ignore it
        greetingCounter++
        getContext().getLog().info("Greeting $greetingCounter for ${message.whom}")
        if (greetingCounter == max) return Behaviors.stopped()
        message.from.tell(new Greet(message.whom, getContext().getSelf()))
        return this''')],
        [group: 'P538 Pekko pack', name: '… and as the blog writes it, refuted: nothing yet says no message follows stopped()',
         expect: ['Cannot prove class invariant of onGreeted holds at method exit', 'counterexample: greetingCounter = 1, max = 1'],
         src: helloBot('''        greetingCounter++
        getContext().getLog().info("Greeting $greetingCounter for ${message.whom}")
        if (greetingCounter == max) {
            return Behaviors.stopped()
        } else {
            message.from.tell(new Greet(message.whom, getContext().getSelf()))
            return this
        }''')],

        // ---------- returned behaviours ----------
        [group: 'P538 Pekko pack', name: 'return this', ok: true, src: bot('        count++\n        return this')],
        [group: 'P538 Pekko pack', name: 'return Behaviors.same()', ok: true, src: bot('        count++\n        return Behaviors.same()')],
        [group: 'P538 Pekko pack', name: 'return Behaviors.stopped()', ok: true, src: bot('        count++\n        return Behaviors.stopped()')],
        [group: 'P538 Pekko pack', name: 'return Behaviors.empty()', ok: true, src: bot('        count++\n        return Behaviors.empty()')],
        [group: 'P538 Pekko pack', name: 'a returned behaviour is non-null', ok: true,
         src: pk('''class Bot extends AbstractBehavior<Greeted> {
                        Bot(ActorContext<Greeted> context) { super(context) }
                        @Override
                        Receive<Greeted> createReceive() { newReceiveBuilder().onMessage(Greeted, this::onGreeted).build() }
                        @Ensures({ result != null })
                        Behavior<Greeted> onGreeted(Greeted message) { Behaviors.stopped() }
                    }''')],
        [group: 'P538 Pekko pack', name: '… but nothing else about it is known',
         expect: 'Skipped verification of postcondition for onGreeted',
         src: pk('''class Bot extends AbstractBehavior<Greeted> {
                        Bot(ActorContext<Greeted> context) { super(context) }
                        @Override
                        Receive<Greeted> createReceive() { newReceiveBuilder().onMessage(Greeted, this::onGreeted).build() }
                        @Ensures({ result.is(this) })
                        Behavior<Greeted> onGreeted(Greeted message) { Behaviors.same() }
                    }''')],

        // ---------- tell ----------
        [group: 'P538 Pekko pack', name: 'a tell changes nothing the sender reads', ok: true,
         src: bot('        count++\n        message.from.tell(new Greet(message.whom, getContext().getSelf()))\n        return this')],
        [group: 'P538 Pekko pack', name: 'a tell through an ActorRef field', ok: true,
         src: pk('''class Bot extends AbstractBehavior<Greeted> {
                        int count
                        ActorRef<Greet> greeter
                        Bot(ActorContext<Greeted> context) { super(context) }
                        @Override
                        Receive<Greeted> createReceive() { newReceiveBuilder().onMessage(Greeted, this::onGreeted).build() }
                        @Requires({ message != null && greeter != null })
                        @Ensures({ count == old.count + 1 })
                        Behavior<Greeted> onGreeted(Greeted message) {
                            count++
                            greeter.tell(new Greet(message.whom, getContext().getSelf()))
                            this
                        }
                    }''')],
        [group: 'P538 Pekko pack', name: 'a wrong claim past a tell refutes',
         expect: ['Cannot prove postcondition of onGreeted', 'ensured: (count == (old.count + 1))'],
         src: bot('        count += 2\n        message.from.tell(new Greet(message.whom, getContext().getSelf()))\n        return this')],
        [group: 'P538 Pekko pack', name: 'a null message throws at the tell',
         expect: 'Possible RuntimeException: message.from.tell(null) throws',
         src: bot('        count++\n        message.from.tell(null)\n        return this')],

        // ---------- construction and the receive ----------
        [group: 'P538 Pekko pack', name: 'super(context) and the built receive keep a class invariant', ok: true,
         src: pk('''@Invariant({ count >= 0 })
                    class Bot extends AbstractBehavior<Greeted> {
                        int count
                        Bot(ActorContext<Greeted> context) { super(context) }
                        @Override
                        Receive<Greeted> createReceive() { newReceiveBuilder().onMessage(Greeted, this::onGreeted).build() }
                        Behavior<Greeted> onGreeted(Greeted message) { count++; this }
                    }''')],
        [group: 'P538 Pekko pack', name: 'a receive whose handler is built by a call of this class is not claimed',
         expect: 'Skipped verification of postcondition for createReceive',
         src: pk('''@Invariant({ count >= 0 })
                    class Bot extends AbstractBehavior<Greeted> {
                        int count
                        Bot(ActorContext<Greeted> context) { super(context) }
                        org.apache.pekko.japi.function.Function<Greeted, Behavior<Greeted>> handler() { null }
                        @Override
                        Receive<Greeted> createReceive() { newReceiveBuilder().onMessage(Greeted, handler()).build() }
                    }''')],
        [group: 'P538 Pekko pack', name: 'super(seed) to another library class is not taken as no effect (Random\'s calls setSeed)',
         expect: 'Skipped verification of postcondition for <init> (statement with no modelled effect',
         src: tc('''@Invariant({ n >= 0 })
                    class R extends Random {
                        int n
                        R(long seed) { super(seed) }
                    }''')],
    ]
}
