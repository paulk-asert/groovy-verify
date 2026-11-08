<!--
  SPDX-License-Identifier: Apache-2.0

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-->

# Apache Pekko typed actors

An actor's handler is ordinary sequential code: it reads a message, updates the actor's fields, tells other actors
things and returns the behaviour for the next message. What makes it hard to reason about is what happens *around*
it: who may call it, with what, what runs after it, and whether whoever asked a question ever gets an answer.
groovy-verify's `PekkoPack` answers those questions from what Pekko is **measured** to do, then checks the handler
itself with the usual machinery: `@Invariant`, `@Ensures`, `assert`, and counterexamples.

The pack is in tree and matched by name: Pekko is never compiled against, so a build without Pekko pays nothing.
It covers the Java DSL's `AbstractBehavior` style (Phases 538–542) and its functional style, `Behaviors.setup` /
`receive` (Phase 545).

## Measured first

Every fact the pack rests on is pinned by a test that drives the real runtime (Pekko 2.0.0), in
[`PekkoSemanticsTest`](../src/test/groovy/PekkoSemanticsTest.groovy). A Pekko upgrade that changes one fails there
before a proof is built on the old one.

| Fact | Measured as | Used for |
|---|---|---|
| a handler is never handed `null` | `tell(null)` throws `InvalidMessageException` at the sender; an `ask` with a null message fails before delivery | a registered handler's message is non-null |
| nothing is delivered after `Behaviors.stopped()` | three tells to an actor that stops on its first: handled once | the class invariant isn't owed on the stopped exit |
| …but a `PostStop` handler runs once after, on that state | `[message one, count 1, PostStop, count 1]` | the PostStop handler runs outside the invariant |
| a tell is queued, never run inside the sender's handler | a tell to self: `enter a, exit a, enter b, exit b` | `tell` writes nothing the sender reads |
| `super(context)` runs no subclass code | `createReceive` not called until the first message | the constructor's first statement is no effect |
| an `ask` nobody answers fails at its timeout | `TimeoutException` after ~320 ms (300 ms timeout) | a reply is owed on every path |
| …one answered by whoever its `replyTo` was handed to completes | the helper's answer arrives | handing the reply ref on meets the obligation |
| a second reply is dropped harmlessly | the ask completes with the first; the handler goes on | replying twice is no error |
| a functional handler closure is never handed `null` | `setup`, `receiveMessage`, `receive`, `receiveSignal`, and a builder's `onMessage` (with its predicate), `onAnyMessage` and `onSignal`, each sent a message, a refused `tell(null)` and a stop: every argument non-null | a handler closure's parameters are non-null |

## The blog's bot, as written

This is the `HelloWorldBot` from the Groovy blog's Pekko post, unchanged apart from the contracts. It greets back
until it has done so `max` times, then stops:

<!-- doclint:case p540-pekko-stopped/the-blog-s-bot-as-written-proves-its-live-state-invariant -->
```groovy
@Invariant({ max >= 1 && 0 <= greetingCounter && greetingCounter < max })
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
        greetingCounter++
        getContext().getLog().info("Greeting $greetingCounter for ${message.whom}")
        if (greetingCounter == max) {
            return Behaviors.stopped()
        } else {
            message.from.tell(new Greet(message.whom, getContext().getSelf()))
            return this
        }
    }
}
```

It verifies. Four of the pack's facts are at work:

- **`onGreeted`'s `message` is never null.** The handler is private, has one reference parameter, and is named in the
  source only as `this::onGreeted` inside an `onMessage` step, so only the runtime calls it, and the runtime never
  passes null. So `message.whom` needs no `@Requires`. A direct call or any other reference to `onGreeted`
  withdraws the fact.
- **`message.from.tell(…)` changes nothing the handler reads.** A shipped skeleton, held against the runtime by
  `SpecAuditTest`, says so.
- **`super(context)` is a statement with no effect**, so the constructor establishes the invariant.
- **The invariant isn't owed where the handler returns `Behaviors.stopped()`.** No message is delivered after it,
  and nothing else in the class could read the state: no property, no public method, no `onSignal` step (but see
  PostStop below), and no parameter or field of the actor's type anywhere in the source.

That last point decides which invariant is provable. The counter reaches `max` only on the stopped exit, so
`greetingCounter < max` is the property of the actor's **live** states. The weaker `greetingCounter <= max` is true
of every state the program reaches, but it isn't inductive: a step from a state where it holds can break it.

<!-- doclint:diagnostic p540-pekko-stopped/whose-weaker-invariant-greetingcounter-max-is-still-not-inductive-refuted-at-an-unreachable-state -->
```
[Static type checking] - Cannot prove class invariant of onGreeted holds at method exit … counterexample: greetingCounter = 1, max = 1
```

`greetingCounter = 1, max = 1` can't be reached: the bot would have stopped. The counterexample is the solver's
honest answer to the question asked, and the fix is the sharper invariant above.

## The functional style

The same bot without a class: its count is a parameter of a recursive `bot`, and the handler is a closure handed to
`Behaviors.receive`. What the class invariant says in the `AbstractBehavior` style, `bot`'s precondition says here:

<!-- doclint:case p545-pekko-functional/the-blog-s-functional-bot-verifies-as-written -->
```groovy
class FunctionalBot {
    @Requires({ max >= 1 })
    static Behavior<Greeted> create(int max) { bot(0, max) }

    @Requires({ max >= 1 && 0 <= greetingCounter && greetingCounter < max })
    private static Behavior<Greeted> bot(int greetingCounter, int max) {
        Behaviors.receive { ActorContext<Greeted> context, Greeted message ->
            int n = greetingCounter + 1
            context.getLog().info("Greeting $n for ${message.whom}")
            if (n == max) {
                return Behaviors.<Greeted> stopped()
            } else {
                message.from.tell(new Greet(message.whom, context.getSelf()))
                return bot(n, max)
            }
        }
    }
}
```

It verifies. Two things make that possible:

- **The closure's body is a path of its own** (Phase 544): it is checked from the state where the closure is written,
  so `n` is `greetingCounter + 1` at `bot(n, max)`, and `n == max` was ruled out on that branch. Drop the `if` and
  the recursive call refutes inside the handler, at `greetingCounter = 0, max = 1`.
- **The closure's parameters are never null.** The runtime is the only caller of a closure handed to `setup`,
  `receiveMessage`, `receive`, `receiveSignal`, or to an `onMessage` (its predicate too), `onAnyMessage` or `onSignal`
  step of a builder, and it never passes null (measured). A parameter the closure reassigns loses the fact.

Under `@TypeChecked`, give the closure's parameters their types: Groovy 6.0.0 doesn't infer them from the target.

## A reply on every path

Pekko's request–response is the `ask` pattern: the message carries an `ActorRef` named `replyTo`, and the asker
waits for an answer until its timeout. A handler that returns on some path without answering surfaces only as a
`TimeoutException`, at runtime, somewhere else. The pack makes it a compile error:

<!-- doclint:case p541-pekko-reply/a-reply-on-each-of-two-exits-verified -->
```groovy
@Invariant({ total >= 0 })
class Tally extends AbstractBehavior<Add> {
    private int total

    Tally(ActorContext<Add> context) {
        super(context)
    }

    @Override
    Receive<Add> createReceive() {
        newReceiveBuilder().onMessage(Add, this::onAdd).build()
    }

    private Behavior<Add> onAdd(Add message) {
        if (message.n < 0) {
            message.replyTo.tell(-1)
            return Behaviors.same()
        }
        total = total + message.n
        message.replyTo.tell(total)
        return this
    }
}

record Add(int n, ActorRef<Integer> replyTo) {}
```

Drop the `tell(-1)` on the rejection path and the compile fails at that path's `return`:

<!-- doclint:diagnostic p541-pekko-reply/the-rejection-path-forgets-to-reply-refuted-on-it -->
```
[Static type checking] - onAdd may return without a reply on message.replyTo (pekko pack)
    counterexample: message.n = -1, total = 0
 … @ line 21, column 20.
```

A path is reported only if the solver finds it **feasible**. `if (n > 0) reply(1); if (n <= 0) reply(0)` has a
path through neither branch syntactically, but no run takes it, so it verifies. These meet the obligation:
- a `tell` on `message.replyTo`, on the record accessor `message.replyTo()`, or on a local holding it;
- **handing it on**: as an argument of a call or constructor (a message to another actor, or the behaviour the
  handler becomes), or by keeping it in one of the actor's fields to answer later.

The reply is owed on a `stopped()` exit too, because the asker would time out all the same. A path that throws owes
nothing. A closure is never looked into, since `xs.each { r.tell(it) }` may run zero times.

The rule is by name. The blog's bot carries an `ActorRef` called `from`, which it tells on one path and not the
other; that is a conversation, not an `ask`, and nothing is owed.

## PostStop: the state after the stop

Measured: an actor that registers `onSignal(PostStop, …)` gets one more call after a handler returns `stopped()`,
on exactly the state that handler left. Since nothing observes the actor after that call, a registered PostStop
handler runs **outside** the class invariant: the invariant is neither assumed on entry nor owed on exit. With one,
the blog's bot still proves `greetingCounter < max`:

<!-- doclint:case p542-pekko-poststop/the-blog-s-bot-with-a-poststop-handler-the-release-stands-the-handler-runs-outside-the-invariant -->
```groovy
    Receive<Greeted> createReceive() {
        newReceiveBuilder().onMessage(Greeted, this::onGreeted).onSignal(PostStop, this::onPostStop).build()
    }
```

<!-- doclint:case p542-pekko-poststop/the-blog-s-bot-with-a-poststop-handler-the-release-stands-the-handler-runs-outside-the-invariant -->
```groovy
    private Behavior<Greeted> onPostStop(PostStop signal) {
        getContext().getLog().info("stopped after $greetingCounter greetings")
        this
    }
```

Not assuming it matters. An `assert greetingCounter < max` in that handler would fail at runtime, and it refutes,
at the stopped state:

<!-- doclint:diagnostic p542-pekko-poststop/the-handler-may-not-assume-the-invariant-the-stopped-state-breaks-it -->
```
[Static type checking] - Assertion may not hold: (greetingCounter < max) … counterexample: greetingCounter = 0, max = 0
```

Any other signal step still withdraws the stopped release: `Terminated`, a handler taking any `Signal`,
`onSignalEquals`, or a closure. Only PostStop has been measured.

## What is trusted

None of the facts above is proved from Pekko's source; each is measured and then assumed. The assumptions are
listed in the [trust ledger](../TOOLING.md), the same one that lists external specs. A compile prints them under
`VERIFY_TRUST=list`, and `VERIFY_TRUST=deny` fails on each one at its source position. For the bot with a PostStop
handler:

```
[external spec] org.apache.pekko.actor.typed.ActorRef#tell/1 — registry skeleton (META-INF/groovy-verify/specs)
[pack fact] HelloWorldBot#onGreeted — message is never null on entry (pekko pack)
[pack fact] HelloWorldBot#onGreeted — the class invariant is not owed where it returns Behaviors.stopped() (pekko pack)
[pack fact] HelloWorldBot#onPostStop — the class invariant is neither assumed nor owed in onPostStop: it runs after the actor stops (pekko pack)
```

For the functional bot, one line per closure parameter:

```
[pack fact] FunctionalBot#bot — closure parameter context is never null (pekko pack)
[pack fact] FunctionalBot#bot — closure parameter message is never null (pekko pack)
```

The reply obligation is a check, not an assumption, so it isn't listed.

## Not yet

- **The rest of the functional style.** `withTimers` and `withStash` closures aren't measured, so their scheduler or
  buffer is possibly null. A closure stored in a variable before it is passed gets nothing. The reply obligation and
  the stopped release are the `AbstractBehavior` style's only. Under `@TypeChecked` on Groovy 6.0.0, a handler
  closure's parameters need their types (`{ ActorContext<Greeted> context, Greeted message -> … }`), and
  `Behaviors.setup(ctx -> new Bot(ctx, max))` also needs `Behaviors.<T>setup(…)`: the lambda's parameter isn't
  inferred from the return-type target.
- **Closures as handlers.** `onMessage(T, { m -> … })` on an `AbstractBehavior`'s builder gets a non-null message and
  its body checked, but isn't a registered handler: the stopped release and the reply obligation don't apply to it,
  and a closure that replies isn't counted as a reply.
- **Calls without contracts.** `pipeToSelf`, `ask` from inside a handler, timers and stash have no skeletons yet, so
  a handler using one skips verification, loudly.
- **The guardian side, untried.** The cases cover the actors themselves. Code that starts them (`ActorSystem.create`,
  `ctx.spawn`, a main behaviour that spawns the bot and greets it) hasn't been run through the verifier, so whether
  it verifies, skips loudly, or needs contracts is not yet known.

The phase-by-phase account, with each slice's mutation testing, is in [ROADMAP.md](../ROADMAP.md) (Phases 537–545),
and the capability rows in [CAPABILITIES.md](../CAPABILITIES.md).
