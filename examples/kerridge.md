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

# The Kerridge gallery — CSP teaching shapes, certified

Jon Kerridge's ["Using Concurrency and Parallelism Effectively" i & ii](https://github.com/JonKerridge/UCaPE)
(free from bookboon.com, sources on GitHub) taught a generation of students process-oriented programming in
Groovy over [JCSP](https://github.com/CSPforJAVA/jcsp) — the occam inheritance: processes, one2one channels,
`PAR`, `ALT`, and the *plugAndPlay* process vocabulary (`GNumbers`, `GSquares`, `GPlus`, `GDelta`,
`GPrint`, …). His [Groovy Parallel Patterns library](https://github.com/JonKerridge/GPP_Library)
([arXiv 2103.12031](https://arxiv.org/abs/2103.12031)) carries the same tradition further: networks
"guaranteed deadlock and livelock free … through the use of formal methods" — proofs made *offline*, in the
Welch/Martin design-rule school.

This gallery ports his teaching shapes onto Groovy 6's `groovy.concurrent` (channels as `AsyncChannel`,
`PAR` arms as `async {}` tasks, the delta as `BroadcastChannel`) and runs them under the
[SEQ/PAR ladder](concurrency.md) (Phases 240–246) — where the corresponding certificates are issued **in the
compiler**: values proved end-to-end, deadlock-freedom as well-foundedness of the wait-for order, and the
classic student mistakes surfacing as *named compile errors* rather than runtime hangs. The shapes are
**inspired by UCaPE, written ourselves** — his repository carries no licence and JCSP is LGPL, so ideas are
ported, never sources (the same rule as the jcstress-inspired examples).

## The vocabulary, mapped

| Kerridge / JCSP | groovy.concurrent | What the checker does with it |
| --- | --- | --- |
| `Channel.one2one()` | `AsyncChannel.create(n)` | one live process per end, checked (Phase 241); a bounded FIFO — the *k*-th write is the *k*-th read (Phase 247) |
| a `CSProcess` under `PAR` | an `async { }` task | fork-window disjointness, checked (Phase 240) |
| typed channel discipline | Bean Validation bounds on the element type | checked at sends, assumed at opaque receives (Phase 242) |
| the client-server design rule | the wait-for order | deadlock-freedom proved as well-foundedness; a cycle is a spelled-out error (Phase 243) |
| poison pill / formal termination | `close()` | a drain provably finishes; a missing close is a named error (Phase 245) |
| `GDelta` (copy to every branch) | `BroadcastChannel.subscribe()` | every subscriber sees the element — fan-out *proves* |
| `GNumbers` with a literal count | a `for (n in 1..N)` producer loop | unrolled: the stream is bounded traffic, the pipeline proves (Phase 248) |
| `ALT` | `ChannelSelect` | future work (locally a nondeterministic branch, like `Awaitable.any`) |

## The one-shot shapes verify end to end

The book's first network — c02's `RunHelloWorld`, a producer and consumer under `PAR` over a one2one
channel — with the exchanged value *proved*:

<!-- doclint:case p246-kerridge-gallery/c02-hello-world-the-one-message-exchange-proves -->
```groovy
@Ensures({ result == 'Hello' })
static String helloWorld() {
    groovy.concurrent.AsyncChannel<String> connect = groovy.concurrent.AsyncChannel.create(1)
    async { connect.send('Hello'); connect.close() }
    return connect.first()
}
```

The *literal* `ProduceHW` / `ConsumeHW` pair — two messages, `"Hello"` then `"World"`, down one channel — was
the gallery's first named boundary; the bounded FIFO of Phase 247 proves it end to end, **in order** (read
them back the other way round and the claim is refuted with a counterexample):

<!-- doclint:case p246-kerridge-gallery/the-literal-two-write-producehw-consumehw-proves-in-order -->
```groovy
@Ensures({ result == 'Hello World' })
static String produceHW() {
    groovy.concurrent.AsyncChannel<String> connect = groovy.concurrent.AsyncChannel.create(2)
    async { connect.send('Hello'); connect.send('World'); connect.close() }
    String first = connect.first()
    String second = connect.first()
    return first + ' ' + second
}
```

The plugAndPlay stages port the same way: **GSquares** is a `map { it * it }` stage whose per-element
transform proves; **GPlus** joins one value from each of two input channels and proves the sum (fan-in done
right: each producer owns its own channel); **GDelta** is `BroadcastChannel` fan-out, both branches proved
to see the element; **GPrint**'s drain-until-end-of-stream is certified to finish because its `close()`
dependency is satisfiable. With a *literal* trip count the whole c03 network certifies: `GNumbers` as a `for (n in 1..3)` producer loop
unrolls (Phase 248), `GSquares` composes, and `GPrint`'s drain proves the printed sum — deadlock-freedom
included, since the drain's `close()` dependency is satisfiable:

<!-- doclint:case p246-kerridge-gallery/c03-gnumbers-gsquares-gprint-bounded-the-sum-proves -->
```groovy
@Ensures({ result == 14 })
static int squaresPipeline() {
    groovy.concurrent.AsyncChannel<Integer> n2s = groovy.concurrent.AsyncChannel.create(4)
    groovy.concurrent.AsyncChannel<Integer> s2p = n2s.map { it * it }
    async {
        for (n in 1..3) {
            n2s.send(n)
        }
        n2s.close()
    }
    int printed = 0
    for (v in s2p) {
        printed = printed + v
    }
    return printed
}
```

And the shape his tradition cares most about — the **client–server exchange**,
whose deadlock-freedom the Welch/Martin design rules argue by ordering — is certified here by the same
theorem, mechanised (the wait-for order is well-founded), *and* its value proves:

<!-- doclint:case p246-kerridge-gallery/client-server-request-reply-certified-and-proved -->
```groovy
@Ensures({ result == x + 1 })
static int clientServer(int x) {
    groovy.concurrent.AsyncChannel<Integer> request = groovy.concurrent.AsyncChannel.create(1)
    groovy.concurrent.AsyncChannel<Integer> reply = groovy.concurrent.AsyncChannel.create(1)
    request.send(x)
    async { int r = request.first(); reply.send(r + 1) }
    return reply.first()
}
```

## The student mistakes are named compile errors

The book teaches deadlock by *running into it* — build the network, watch it hang, discuss. Here the same
exercises refuse to compile, each with its cause spelled out:

<!-- doclint:case p246-kerridge-gallery/the-deadlock-exercise-a-mutual-receive-cycle-is-refuted -->
```groovy
static int deadlockExercise() {
    groovy.concurrent.AsyncChannel<Integer> aToB = groovy.concurrent.AsyncChannel.create(1)
    groovy.concurrent.AsyncChannel<Integer> bToA = groovy.concurrent.AsyncChannel.create(1)
    async { int x = bToA.first(); aToB.send(x) }
    async { int y = aToB.first(); bToA.send(y) }
    return 0
}
```

> Process-network deadlock in 'deadlockExercise': circular wait: the receive on 'bToA' … which waits for
> the send on 'bToA' … which waits for the receive on 'aToB' … which waits for the send on 'aToB' …
> which waits for the first.

The **missing poison pill** — a consumer draining a stream nobody ends — errors as *"the iteration over
'stream' can never finish — no close()"*. **Two producers on one one2one channel** — the discipline
JCSP polices at runtime — is a compile-time "Channel linearity violation": the element order is a race. And
**reading more than was written** — a consumer that takes a second message from a producer that sent one —
is *"the 2nd receive on 'src' can never be satisfied — only 1 send"* (Phase 247): the process would block
forever, and the FIFO pairing knows it.

## The honest boundary, loudly

One port stays *deliberately* out of reach, and says so. **GNumbers** as the book means it — the *infinite*
(or symbolically bounded) generator behind every pipeline — is *streaming*: the checker's channel model is a
**bounded FIFO** whose element count is static (Phase 247), and only a *literal* loop bound unrolls into it
(Phase 248 — bounded model checking, ≤ 32 iterations). A `while (true)` generator or a `for (i in 0..<n)`
with symbolic `n` refuses the model outright and its value claims skip loudly. That frontier is precisely the ladder's recorded next rung
(symbolic send/receive counts carried by loop invariants; session-typed channel protocols) — which makes
"pick a streaming example and see what certification takes" a research conversation, not a demo: the same
guarantees GPP establishes offline by formal methods, issued incrementally by the compiler.

As everywhere in the [concurrency gallery](concurrency.md): the scheduler, the JMM, and atomicity remain
the [three runtime rungs](../CONCURRENCY.md) — these certificates are action-grained and above the memory
model, exactly as CSP's own semantics are.
