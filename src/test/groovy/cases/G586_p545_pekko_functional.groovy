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
 * 'P545 Pekko functional' — Phase 545, the Pekko pack's slice 6: the functional style. A closure handed to
 * {@code Behaviors.setup}, {@code receiveMessage}, {@code receive}, {@code receiveSignal}, or to an {@code onMessage}
 * (its predicate too) / {@code onAnyMessage} / {@code onSignal} step of a behaviour or receive builder, is called only
 * by the runtime, and measured (PekkoSemanticsTest) never to be handed null. Its parameters are non-null where it
 * runs, a ledgered pack fact. Phase 544 made the closure's body a path of its own; this gives that path its entry.
 * Before: every {@code message.whom} and {@code ctx.getSelf()} in the blog's functional bot was a possible
 * NullPointerException.
 */
class G586_p545_pekko_functional {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A closure handed to a Pekko Behaviors factory or builder step gets non-null parameters where it runs (setup\'s context, a handler\'s message or signal), a ledgered pack fact; a closure it reassigns, or one handed elsewhere, does not.'

    static final String G = 'P545 Pekko functional'

    static final String PK = 'import org.apache.pekko.actor.typed.*\nimport org.apache.pekko.actor.typed.javadsl.*\n' +
        'import org.apache.pekko.actor.typed.javadsl.ActorContext\nimport org.apache.pekko.japi.function.Function2\n' +
        'import org.apache.pekko.japi.function.Predicate\n'
    static final String MSGS = '''
record Greet(String whom, ActorRef<Greeted> replyTo) {}
record Greeted(String whom, ActorRef<Greet> from) {}
'''
    static String pk(String t, String imports = '') { HDR + PK + imports + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" + t.stripIndent() + MSGS }

    /** The Groovy blog's bot in the functional style, its handler's tail given. */
    static String functionalBot(String tail) {
        pk("""class FunctionalBot {
    @Requires({ max >= 1 })
    static Behavior<Greeted> create(int max) { bot(0, max) }

    @Requires({ max >= 1 && 0 <= greetingCounter && greetingCounter < max })
    private static Behavior<Greeted> bot(int greetingCounter, int max) {
        Behaviors.receive { ActorContext<Greeted> context, Greeted message ->
            int n = greetingCounter + 1
            context.getLog().info("Greeting \$n for \${message.whom}")
${tail}
        }
    }
}""")
    }

    static final String AS_WRITTEN = '''            if (n == max) {
                return Behaviors.<Greeted> stopped()
            } else {
                message.from.tell(new Greet(message.whom, context.getSelf()))
                return bot(n, max)
            }'''

    static final String NPE = 'Possible NullPointerException'

    static final List<Map> CASES = [
        // Before: a possible NullPointerException at each use of message and context.
        [group: G, name: 'the blog\'s functional bot verifies as written', ok: true,
         trusted: '[pack fact] FunctionalBot#bot — closure parameter message is never null (pekko pack)',
         src: functionalBot(AS_WRITTEN)],
        [group: G, name: '… and its context is ledgered too', ok: true,
         trusted: '[pack fact] FunctionalBot#bot — closure parameter context is never null (pekko pack)',
         src: functionalBot(AS_WRITTEN)],
        [group: G, name: 'recursing past max breaks bot\'s precondition: refuted inside the handler',
         expect: ['Cannot prove precondition of bot at this call site', 'counterexample: greetingCounter = 0, max = 1',
                  'no failing call'], refute: 'fails on',
         src: functionalBot('''            message.from.tell(new Greet(message.whom, context.getSelf()))
            return bot(n, max)''')],
        [group: G, name: 'setup\'s context and receiveMessage\'s message', ok: true,
         trusted: '[pack fact] B#create — closure parameter ctx is never null (pekko pack)',
         src: pk('''class B {
    static Behavior<Greeted> create() {
        Behaviors.<Greeted> setup { ActorContext<Greeted> ctx ->
            ctx.getLog().info("started")
            Behaviors.<Greeted> receiveMessage { Greeted m ->
                m.from.tell(new Greet(m.whom, ctx.getSelf()))
                Behaviors.<Greeted> same()
            }
        }
    }
}''')],
        [group: G, name: 'the implicit it', ok: true,
         trusted: '[pack fact] B#create — closure parameter it is never null (pekko pack)',
         src: pk('''class B {
    static Behavior<Greeted> create() {
        Behaviors.<Greeted> receiveMessage { it.whom.length() > 0 ? Behaviors.<Greeted> same() : Behaviors.<Greeted> stopped() }
    }
}''')],
        [group: G, name: 'a behaviour builder\'s steps: onMessage, its predicate, onSignal', ok: true,
         src: pk('''class B {
    static Behavior<Greeted> create() {
        Behaviors.receive(Greeted)
            .onMessage(Greeted, { Greeted m -> m.whom.isEmpty() } as Predicate<Greeted>, { Greeted m -> Behaviors.<Greeted> stopped() })
            .onMessage(Greeted, { Greeted m -> m.from.tell(new Greet(m.whom, null)); Behaviors.<Greeted> same() })
            .onSignal(PostStop, { PostStop s -> s.hashCode(); Behaviors.<Greeted> same() })
            .build()
    }
}''')],
        [group: G, name: 'receive with a signal function: its context and signal', ok: true,
         src: pk('''class B {
    static Behavior<Greeted> create() {
        Behaviors.<Greeted> receive(
            { ActorContext<Greeted> c, Greeted m -> m.whom.length() > 0 ? Behaviors.<Greeted> same() : Behaviors.<Greeted> stopped() } as Function2<ActorContext<Greeted>, Greeted, Behavior<Greeted>>,
            { ActorContext<Greeted> c, Signal s -> c.getLog().info("signal ${s.hashCode()}"); Behaviors.<Greeted> same() } as Function2<ActorContext<Greeted>, Signal, Behavior<Greeted>>)
    }
}''')],
        [group: G, name: 'a static-imported receiveMessage', ok: true,
         src: pk('''class B {
    static Behavior<Greeted> create() {
        receiveMessage { Greeted m -> m.whom.length() > 0 ? Behaviors.<Greeted> same() : Behaviors.<Greeted> stopped() }
    }
}''', 'import static org.apache.pekko.actor.typed.javadsl.Behaviors.receiveMessage\n')],
        [group: G, name: 'a closure on an AbstractBehavior\'s receive builder', ok: true,
         src: pk('''class Bot extends AbstractBehavior<Greeted> {
    Bot(ActorContext<Greeted> context) { super(context) }
    @Override
    Receive<Greeted> createReceive() {
        newReceiveBuilder().onMessage(Greeted, { Greeted message ->
            message.from.tell(new Greet(message.whom, getContext().getSelf()))
            Behaviors.<Greeted> same()
        }).build()
    }
}''')],

        // ---------- where the fact isn't given ----------
        [group: G, name: 'a parameter the closure reassigns: the fact would outlive the value',
         expect: [NPE, 'obligation: m != null'],
         src: pk('''class B {
    static Greeted pick(Greeted g) { g.whom == 'x' ? null : g }
    static Behavior<Greeted> create() {
        Behaviors.<Greeted> receiveMessage { Greeted m ->
            m = pick(m)
            m.whom.length() > 0 ? Behaviors.<Greeted> same() : Behaviors.<Greeted> stopped()
        }
    }
}''')],
        // A handler nested in setup's closure keeps the old reading (Phase 544's boundary): only the fact's own guard
        // stands between it and a silent proof.
        [group: G, name: '… and in a handler nested in setup\'s closure', expect: [NPE, 'obligation: m != null'],
         src: pk('''class B {
    static Greeted pick(Greeted g) { g.whom == 'x' ? null : g }
    static Behavior<Greeted> create() {
        Behaviors.<Greeted> setup { ActorContext<Greeted> ctx ->
            Behaviors.<Greeted> receiveMessage { Greeted m ->
                m = pick(m)
                m.whom.length() > 0 ? Behaviors.<Greeted> same() : Behaviors.<Greeted> stopped()
            }
        }
    }
}''')],
        [group: G, name: 'a method of the same name that isn\'t Pekko\'s', expect: [NPE, 'obligation: m != null'],
         src: pk('''class B {
    static int run() {
        Helper.receiveMessage { Greeted m -> m.whom.length() }
    }
}
class Helper {
    static int receiveMessage(Closure<Integer> c) { c != null ? c.call(null) : 0 }
}''')],
        [group: G, name: '… nor one of the user\'s own, called bare', expect: [NPE, 'obligation: m != null'],
         src: pk('''class B {
    static int receiveMessage(Closure<Integer> c) { c != null ? c.call(null) : 0 }
    static int run() {
        receiveMessage { Greeted m -> m.whom.length() }
    }
}''')],
        [group: G, name: 'withTimers isn\'t measured: its scheduler is possibly null', expect: [NPE, 'obligation: t != null'],
         src: pk('''class B {
    static Behavior<Greeted> create() {
        Behaviors.<Greeted> withTimers { TimerScheduler<Greeted> t ->
            t.isTimerActive('k') ? Behaviors.<Greeted> same() : Behaviors.<Greeted> stopped()
        }
    }
}''')],
        [group: G, name: 'VERIFY_TRUST=deny: the fact fails the compile, at the closure\'s parameter', trustMode: 'deny',
         expect: ['Trusted without proof (VERIFY_TRUST=deny): [pack fact] B#create — closure parameter m is never null (pekko pack)',
                  '@ line 10, column 46.'],
         src: pk('''class B {
    static Behavior<Greeted> create() {
        Behaviors.<Greeted> receiveMessage { Greeted m -> m.whom.length() > 0 ? Behaviors.<Greeted> same() : Behaviors.<Greeted> stopped() }
    }
}''')],
    ]
}
