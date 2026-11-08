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

/** 'P541 Pekko reply' — Phase 541, the Pekko pack's slice 4: a registered handler whose message carries an
 *  {@code ActorRef replyTo} owes a reply on every normal exit — measured in PekkoSemanticsTest, an ask nobody answers
 *  fails at its timeout, one answered by whoever its replyTo was handed to completes, and a second reply is dropped
 *  harmlessly. Telling it, or handing it on (an argument, a stored value, a lambda given to Pekko), meets it; a feasible
 *  path that does neither is an error with its counterexample. */
class G582_p541_pekko_reply {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A Pekko handler given a replyTo replies, or hands it on, on every feasible path; one that may return without is an error with the counterexample.'

    static final String PK = 'import org.apache.pekko.actor.typed.*\nimport org.apache.pekko.actor.typed.javadsl.*\n' +
        'import org.apache.pekko.actor.typed.javadsl.ActorContext\n'
    static final String MSGS = '''
record Add(int n, ActorRef<Integer> replyTo) {}
record Forward(int n, ActorRef<Integer> replyTo) {}
'''
    static String pk(String t) { HDR + PK + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" + t.stripIndent() + MSGS }

    /** Answers each Add with the new total, or -1 for a negative one. */
    static final String REPLIES = '''        if (message.n < 0) {
            message.replyTo.tell(-1)
            return Behaviors.same()
        }
        total = total + message.n
        message.replyTo.tell(total)
        return this'''

    /** A tally actor under {@code @Invariant({ total >= 0 })} (none with {@code inv: null}) whose Add handler is {@code body}. */
    static String tally(String body, Map opts = [:]) {
        String inv = opts.containsKey('inv') ? opts.inv : '@Invariant({ total >= 0 })\n'
        pk("""${inv ?: ''}class Tally extends AbstractBehavior<Add> {
    private int total
${opts.fields ?: ''}
    Tally(ActorContext<Add> context) {
        super(context)
    }

    @Override
    Receive<Add> createReceive() {
        newReceiveBuilder().onMessage(Add, this::onAdd).build()
    }

    ${opts.handler ?: 'private Behavior<Add> onAdd(Add message)'} {
${body}
    }
${opts.extra ?: ''}}
${opts.after ?: ''}""")
    }

    /** The behaviour a handler becomes while another answers: it keeps the reply ref. */
    static final String AWAITING = '''class Awaiting extends AbstractBehavior<Add> {
    private final ActorRef<Integer> replyTo
    Awaiting(ActorContext<Add> context, ActorRef<Integer> replyTo) {
        super(context)
        this.replyTo = replyTo
    }

    @Override
    Receive<Add> createReceive() {
        newReceiveBuilder().build()
    }
}
'''

    static final String MISSED = 'onAdd may return without a reply on message.replyTo (pekko pack)'

    static final List<Map> CASES = [
        // ---------- replies on every path ----------
        [group: 'P541 Pekko reply', name: 'a reply on each of two exits: verified', ok: true, src: tally(REPLIES)],
        [group: 'P541 Pekko reply', name: 'the rejection path forgets to reply: refuted on it',
         expect: [MISSED, 'counterexample: message.n = -1, total = 0', '@ line 21, column 20.'],   // at its `return Behaviors.same()`
         src: tally(REPLIES.replace('            message.replyTo.tell(-1)\n', ''))],
        [group: 'P541 Pekko reply', name: 'the class has no invariant: the reply is owed all the same',
         expect: [MISSED],
         src: tally(REPLIES.replace('            message.replyTo.tell(-1)\n', ''), [inv: null])],
        [group: 'P541 Pekko reply', name: 'two guards that can\'t both fail: the path replying on neither is infeasible', ok: true,
         src: tally('''        if (message.n > 0) message.replyTo.tell(1)
        if (message.n <= 0) message.replyTo.tell(0)
        return this''')],
        [group: 'P541 Pekko reply', name: 'replying twice is no error (a second reply is dropped, measured)', ok: true,
         src: tally('''        message.replyTo.tell(total)
        message.replyTo.tell(total)
        return this''')],
        [group: 'P541 Pekko reply', name: 'returning stopped() still owes the reply (the asker would time out)',
         expect: [MISSED],
         src: tally('''        if (message.n == 0) return Behaviors.stopped()
        message.replyTo.tell(total)
        return this''')],
        [group: 'P541 Pekko reply', name: 'a throw is no normal exit: nothing owed on it', ok: true,
         src: tally('''        if (message.n < 0) throw new IllegalArgumentException('negative')
        message.replyTo.tell(total)
        return this''')],

        // ---------- the spellings of a reply ----------
        [group: 'P541 Pekko reply', name: 'the record accessor message.replyTo()', ok: true,
         src: tally('''        message.replyTo().tell(total)
        return this''')],
        [group: 'P541 Pekko reply', name: 'through a local holding it', ok: true,
         src: tally('''        ActorRef<Integer> r = message.replyTo
        r?.tell(total)
        return this''')],
        [group: 'P541 Pekko reply', name: 'a local holding it, never told: refuted',
         expect: [MISSED],
         src: tally('''        ActorRef<Integer> r = message.replyTo
        return this''')],

        // ---------- handing it on ----------
        [group: 'P541 Pekko reply', name: 'handed on inside a message to another actor', ok: true,
         src: tally('''        helper.tell(new Forward(message.n, message.replyTo))
        return this''', [fields: '    private final ActorRef<Forward> helper = null\n'])],
        [group: 'P541 Pekko reply', name: 'kept in a field, to answer later', ok: true,
         src: tally('''        pending = message.replyTo
        return this''', [fields: '    private ActorRef<Integer> pending\n'])],
        [group: 'P541 Pekko reply', name: '… or this.pending', ok: true,
         src: tally('''        this.pending = message.replyTo
        return this''', [fields: '    private ActorRef<Integer> pending\n'])],
        [group: 'P541 Pekko reply', name: 'handed to the behaviour it becomes', ok: true,
         src: tally('''        return new Awaiting(getContext(), message.replyTo)''', [after: AWAITING])],
        [group: 'P541 Pekko reply', name: 'a closure that would reply, never called: not a reply',
         expect: [MISSED],
         src: tally('''        Closure c = { message.replyTo.tell(total) }
        return this''')],
        [group: 'P541 Pekko reply', name: 'a closure handed to a collection: the call has no contract, so a loud skip, as for any',
         expect: 'Skipped verification of postcondition for onAdd (standalone call',
         src: tally('''        [1, 2].each { int k -> message.replyTo.tell(k) }
        return this''')],

        // ---------- no obligation ----------
        [group: 'P541 Pekko reply', name: 'an ActorRef not named replyTo (the blog\'s from) owes nothing', ok: true,
         src: pk('''class Echo extends AbstractBehavior<Ping> {
    Echo(ActorContext<Ping> context) {
        super(context)
    }

    @Override
    Receive<Ping> createReceive() {
        newReceiveBuilder().onMessage(Ping, this::onPing).build()
    }

    private Behavior<Ping> onPing(Ping message) {
        return this
    }
}
record Ping(ActorRef<String> from) {}
''')],
        [group: 'P541 Pekko reply', name: 'a replyTo that is no ActorRef owes nothing', ok: true,
         src: pk('''class Notes extends AbstractBehavior<Note> {
    Notes(ActorContext<Note> context) {
        super(context)
    }

    @Override
    Receive<Note> createReceive() {
        newReceiveBuilder().onMessage(Note, this::onNote).build()
    }

    private Behavior<Note> onNote(Note message) {
        return this
    }
}
record Note(int n, String replyTo) {}
''')],
        [group: 'P541 Pekko reply', name: 'a public handler isn\'t only the runtime\'s to call: no obligation', ok: true,
         src: tally('''        return this''', [handler: 'Behavior<Add> onAdd(Add message)'])],
    ]
}
