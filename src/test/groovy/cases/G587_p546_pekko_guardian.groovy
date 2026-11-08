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
 * 'P546 Pekko guardian' — Phase 546, the Pekko pack's slice 7: the code that starts the actors. Probed on the blog's
 * sample program (groovy-pekko-gpars), every class under the verifier, two false alarms. {@code context.spawn(…)} in
 * {@code HelloWorldMain}'s constructor was a possible NullPointerException, {@code fails on: <init>(null)}, though
 * that call fails in {@code super(context)}: {@code AbstractBehavior} throws IllegalArgumentException on a null
 * context (measured). And {@code system.tell(…)} in {@code Run}, since {@code ActorSystem.create} had no skeleton; with
 * one, its {@code result != null} was still dropped when the guardian argument is a call, a formal the ensures never
 * reads.
 */
class G587_p546_pekko_guardian {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A Pekko actor\'s constructor has a non-null context past super(context) (AbstractBehavior throws on null), and ActorSystem.create returns a system: the blog\'s whole sample program verifies.'

    static final String G = 'P546 Pekko guardian'

    static final String TC = "@TypeChecked(extensions = 'verification.VerifyChecker')\n"
    static final String IMPORTS = '''import groovy.transform.CompileStatic
import org.apache.pekko.actor.typed.ActorRef
import org.apache.pekko.actor.typed.ActorSystem
import org.apache.pekko.actor.typed.Behavior
import org.apache.pekko.actor.typed.javadsl.AbstractBehavior
import org.apache.pekko.actor.typed.javadsl.ActorContext
import org.apache.pekko.actor.typed.javadsl.Behaviors
import org.apache.pekko.actor.typed.javadsl.Receive
'''

    /** The blog's greeter, as written but for {@code Behaviors.<Greet>setup}, which @TypeChecked needs. */
    static final String GREETER = TC + '''class HelloWorld extends AbstractBehavior<Greet> {

    static record Greet(String whom, ActorRef<Greeted> replyTo) {}
    static record Greeted(String whom, ActorRef<Greet> from) {}

    static Behavior<Greet> create() {
        Behaviors.<Greet>setup(HelloWorld::new)
    }

    private HelloWorld(ActorContext<Greet> context) {
        super(context)
    }

    @Override
    Receive<Greet> createReceive() {
        newReceiveBuilder().onMessage(Greet.class, this::onGreet).build()
    }

    @CompileStatic
    private Behavior<Greet> onGreet(Greet command) {
        context.log.info "Hello $command.whom!"
        command.replyTo.tell(new Greeted(command.whom, context.self))
        this
    }
}
'''

    /** The blog's bot with its two contracts. */
    static final String BOT = '@Invariant({ max >= 1 && 0 <= greetingCounter && greetingCounter < max })\n' + TC +
        '''class HelloWorldBot extends AbstractBehavior<HelloWorld.Greeted> {

    @Requires({ max >= 1 })
    static Behavior<HelloWorld.Greeted> create(int max) {
        Behaviors.<HelloWorld.Greeted>setup(context -> new HelloWorldBot(context, max))
    }

    private final int max
    private int greetingCounter

    @Requires({ max >= 1 })
    private HelloWorldBot(ActorContext<HelloWorld.Greeted> context, int max) {
        super(context)
        this.max = max
    }

    @Override
    Receive<HelloWorld.Greeted> createReceive() {
        newReceiveBuilder().onMessage(HelloWorld.Greeted.class, this::onGreeted).build()
    }

    @CompileStatic
    private Behavior<HelloWorld.Greeted> onGreeted(HelloWorld.Greeted message) {
        greetingCounter++
        context.log.info "Greeting $greetingCounter for $message.whom"
        if (greetingCounter == max) {
            return Behaviors.stopped()
        } else {
            message.from.tell(new HelloWorld.Greet(message.whom, context.self))
            return this
        }
    }
}
'''

    /** The blog's main behaviour, its constructor's body after {@code super(context)} given. */
    static String main(String ctorRest = "        greeter = context.spawn(HelloWorld.create(), 'greeter')", String ctorStart = '        super(context)') {
        TC + """class HelloWorldMain extends AbstractBehavior<HelloWorldMain.SayHello> {

    static record SayHello(String name) { }

    static Behavior<SayHello> create() {
        Behaviors.<SayHello>setup(HelloWorldMain::new)
    }

    private final ActorRef<HelloWorld.Greet> greeter

    private HelloWorldMain(ActorContext<SayHello> context) {
${ctorStart}
${ctorRest}
    }

    @Override
    Receive<SayHello> createReceive() {
        newReceiveBuilder().onMessage(SayHello.class, this::onStart).build()
    }

    private Behavior<SayHello> onStart(SayHello command) {
        var replyTo = context.spawn(HelloWorldBot.create(3), command.name)
        greeter.tell(new HelloWorld.Greet(command.name, replyTo))
        this
    }
}
"""
    }

    /** The blog's Run script, as a class. */
    static String run(String create = "ActorSystem.create(HelloWorldMain.create(), 'hello')") {
        TC + """class Run {
    static void main(String[] args) {
        var system = ${create}

        system.tell(new HelloWorldMain.SayHello('World'))
        system.tell(new HelloWorldMain.SayHello('Pekko'))

        sleep 2000
        system.terminate()
    }
}
"""
    }

    static String program(String first, String... rest) { HDR + IMPORTS + ([first] + (rest as List)).join('\n') }

    static final String NPE = 'Possible NullPointerException'
    static final String PAST_SUPER = '[pack fact] HelloWorldMain#<init> — context is non-null past super(context): AbstractBehavior\'s constructor throws on null (pekko pack)'

    static final List<Map> CASES = [
        // Before: `context.spawn` a possible NullPointerException, `fails on: <init>(null)`; `system.tell` one too.
        [group: G, name: 'the blog\'s sample program verifies, guardian and all', ok: true, trusted: PAST_SUPER,
         src: program(run(), main(), GREETER, BOT)],
        [group: G, name: '… resting on the ActorSystem.create skeleton', ok: true,
         trusted: '[external spec] org.apache.pekko.actor.typed.ActorSystem#create/2 — registry skeleton (META-INF/groovy-verify/specs)',
         src: program(run(), main(), GREETER, BOT)],

        // ---------- the constructor's context ----------
        [group: G, name: 'a context reassigned after super(context) is the new value',
         expect: [NPE, 'obligation: context != null'],
         src: program(main('''        context = null
        greeter = context.spawn(HelloWorld.create(), 'greeter')'''), GREETER, BOT)],
        [group: G, name: 'a constructor delegating with this(…) gets no fact',
         expect: [NPE, 'obligation: context != null'],
         src: program(main('''        greeter = context.spawn(HelloWorld.create(), 'greeter')
    }

    private HelloWorldMain(ActorContext<SayHello> context, int n) {
        super(context)
        greeter = null''', '        this(context, 0)'), GREETER, BOT)],
        [group: G, name: 'a subclass of a subclass: its super isn\'t AbstractBehavior\'s',
         expect: [NPE, 'obligation: context != null'],
         src: program(TC + '''class Sub extends Base {
    final ActorRef<String> child
    Sub(ActorContext<String> context) {
        super(context)
        child = context.spawn(Behaviors.<String>empty(), 'child')
    }
}
''', TC + '''class Base extends AbstractBehavior<String> {
    Base(ActorContext<String> context) { super(context) }
    @Override
    Receive<String> createReceive() { newReceiveBuilder().build() }
}
''')],
        [group: G, name: 'VERIFY_TRUST=deny: the fact fails the compile, at the constructor\'s parameter', trustMode: 'deny',
         expect: ['Trusted without proof (VERIFY_TRUST=deny): ' + PAST_SUPER, '@ line 21, column 28.'],
         src: program(main(), GREETER, BOT)],

        // ---------- ActorSystem.create ----------
        [group: G, name: 'a guardian passed in', ok: true,
         src: program(TC + '''class Start {
    static void start(Behavior<HelloWorldMain.SayHello> guardian) {
        var system = ActorSystem.create(guardian, 'hello')
        system.tell(new HelloWorldMain.SayHello('World'))
        system.terminate()
    }
}
''', main(), GREETER, BOT)],
        // The guardian argument is a call bound to an opaque value: a model may rest on it unseen, so the method names no
        // failing call, even for a failure that doesn't (conservative: here main(new String[0]) would fail)
        [group: G, name: 'a method with an opaque argument names no failing call',
         expect: ['Assertion may not hold', 'no failing call: the failure may rest on an argument of a library call that the verifier doesn\'t model'],
         refute: 'fails on',
         src: program(run().replace("        system.terminate()", "        system.terminate()\n        assert args.length > 0"), main(), GREETER, BOT)],
        [group: G, name: 'an overload with no skeleton (a Config) is a value the verifier doesn\'t model',
         expect: [NPE, 'obligation: system != null', 'a value the verifier doesn\'t model'],
         src: program(run("ActorSystem.create(HelloWorldMain.create(), 'hello', com.typesafe.config.ConfigFactory.load())"), main(), GREETER, BOT)],
    ]
}
