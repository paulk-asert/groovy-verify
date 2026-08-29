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
| `Channel.one2one()` | `val c = AsyncChannel.<Integer>create(n)` | one live process per end, checked (Phase 241); a bounded FIFO — the *k*-th write is the *k*-th read (Phase 247) |
| a `CSProcess` under `PAR` | an `async { }` task | fork-window disjointness, checked (Phase 240) |
| typed channel discipline | Bean Validation bounds on the element type | checked at sends, assumed at opaque receives (Phase 242) |
| the client-server design rule | the wait-for order | deadlock-freedom proved as well-foundedness; a cycle is a spelled-out error (Phase 243) |
| poison pill / formal termination | `close()` | a drain provably finishes; a missing close is a named error (Phase 245) |
| `GDelta` (copy to every branch) | `BroadcastChannel.subscribe()` | every subscriber sees the element — fan-out *proves* |
| `GNumbers` with a literal count | a `for (n in 1..N)` producer loop | unrolled: the stream is bounded traffic, the pipeline proves (Phase 248) |
| `GNumbers(n)`, symbolic | a `while (i < n) { … i = i + 1 }` producer loop with `@Invariant` / `@Decreases` + `close()` | termination certified (Phase 250); the drained sequence proves element by element — the channel is the list the loop builds (Phase 251) |
| a looping process (`GPrint`, `GSquares` as a `while` reading its input) | a `while (i < n) { v = in.first(); … }` loop with `@Invariant` / `@Decreases` | reads element *k*; reading past the producer "may block forever" (Phase 252) |
| a process that never stops (`GNumbers`, `GPrint`, a server, as the book writes them) | `while (true) { … }` with an `@Invariant` | safety certified — invariant, send contracts, received values; termination not claimed; liveness reported as the assumption it is (Phase 254) |
| `ALT` | `await ChannelSelect.from(a, b).select()` | a choice among the branches that can be ready — value *and* index proved; an OR node in the wait-for order (Phase 249) |
| `ALT` in a loop (the multiplexer, the fair server's read side) | `while (j < n) { Result r = await ChannelSelect.from(a, b).select(); … }` | ghost cursors per branch; the merged count proves, the order is nondeterministic, one iteration too many "may block forever" (Phase 253) |

A note on spelling: the ports use Groovy 6's `val` (or `def` / `var`) with the factory's **type witness** —
`val c = AsyncChannel.<Integer>create(n)`. The witness is what tells static type checking (and the checker)
the element type; a bare `AsyncChannel.create(n)` under `def` is an `AsyncChannel<Object>` and neither can
say anything about its elements. Two places still want a declared type: an element *contract*
(`AsyncChannel<@PositiveOrZero Integer> c = …`, Phase 242 — the constraint has to sit on the generic), and an
ALT's result (`ChannelSelect.Result r = await …`, Phase 249).

## The one-shot shapes verify end to end

The book's first network — c02's `RunHelloWorld`, a producer and consumer under `PAR` over a one2one
channel — with the exchanged value *proved*:

<!-- doclint:case p246-kerridge-gallery/c02-hello-world-the-one-message-exchange-proves -->
```groovy
@Ensures({ result == 'Hello' })
static String helloWorld() {
    val connect = AsyncChannel.<String>create(1)
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
    val connect = AsyncChannel.<String>create(2)
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
    val n2s = AsyncChannel.<Integer>create(4)
    val s2p = n2s.map { it * it }
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

And with a *symbolic* count — `GNumbers(n)` as the book means it, `n` a parameter — the same network proves
its drained sequence element by element (Phase 251): the channel is modelled as the list the generator loop
builds, its size and element facts injected into the loop's spec, so the author writes only the generator's
own `@Invariant` / `@Decreases`:

<!-- doclint:case p246-kerridge-gallery/c03-gnumbers-n-gsquares-symbolic-the-k-th-square-proves -->
```groovy
@Requires({ n >= 0 })
@Ensures({ result.size() == n && Forall.range(0, result.size(), { int k -> result[k] == (k + 1) * (k + 1) }) })
static List<Integer> squares(int n) {
    val n2s = AsyncChannel.<Integer>create(4)
    val s2p = n2s.map { it * it }
    async {
        int i = 1
        @Invariant({ 1 <= i && i <= n + 1 })
        @Decreases({ n + 1 - i })
        while (i <= n) {
            n2s.send(i)
            i = i + 1
        }
        n2s.close()
    }
    return s2p.toList()
}
```

And c03 **as the book writes it** — a `PAR` of three *looping* processes, each with its own loop, `GSquares`
receiving *and* sending — proves the printed squares for symbolic `n` (Phase 252): every process carries
only its own `@Invariant` / `@Decreases`; the channels' sequence facts, the block-forever obligation on each
receive, and the renaming-apart of the three loops' counters are the checker's:

<!-- doclint:case p246-kerridge-gallery/c03-as-three-looping-processes-symbolic-the-printed-squares-prove -->
```groovy
@Requires({ n >= 0 })
@Ensures({ result.size() == n && Forall.range(0, result.size(), { int k -> result[k] == (k + 1) * (k + 1) }) })
static List<Integer> network(int n) {
    val n2s = AsyncChannel.<Integer>create(4)
    val s2p = AsyncChannel.<Integer>create(4)
    async {                                              // GNumbers
        int i = 1
        @Invariant({ 1 <= i && i <= n + 1 })
        @Decreases({ n + 1 - i })
        while (i <= n) {
            n2s.send(i)
            i = i + 1
        }
        n2s.close()
    }
    async {                                              // GSquares
        int i = 0
        @Invariant({ 0 <= i && i <= n })
        @Decreases({ n - i })
        while (i < n) {
            int v = n2s.first()
            s2p.send(v * v)
            i = i + 1
        }
        s2p.close()
    }
    List<Integer> printed = []                           // GPrint
    int j = 0
    @Invariant({ printed != null && 0 <= j && j <= n && printed.size() == j && Forall.range(0, printed.size(), { int k -> printed[k] == (k + 1) * (k + 1) }) })
    @Decreases({ n - j })
    while (j < n) {
        int s = s2p.first()
        printed.add(s)
        j = j + 1
    }
    return printed
}
```

And c03 **as the book actually writes it** — every process `while (true)`, nothing ever stopping — is
certified for **safety** (Phase 254): every value `GPrint` accumulates is a square, `GPrint`'s own invariant
preserved through `GSquares`' and `GNumbers`' relations; termination is not claimed, and that each receive is
eventually served is reported, loudly, as the liveness assumption it is:

<!-- doclint:case p246-kerridge-gallery/c03-forever-gnumbers-gsquares-and-gprint-as-non-terminating-processes-safety-proved -->
```groovy
static void network() {
    val n2s = AsyncChannel.<Integer>create(4)
    val s2p = AsyncChannel.<Integer>create(4)
    async {                                              // GNumbers
        int i = 1
        @Invariant({ i >= 1 })
        while (true) {
            n2s.send(i)
            i = i + 1
        }
    }
    async {                                              // GSquares
        int i = 0
        @Invariant({ i >= 0 })
        while (true) {
            int v = n2s.first()
            s2p.send(v * v)
            i = i + 1
        }
    }
    List<Integer> printed = []                           // GPrint
    int j = 0
    @Invariant({ printed != null && j >= 0 && printed.size() == j && Forall.range(0, printed.size(), { int k -> printed[k] == (k + 1) * (k + 1) }) })
    while (true) {
        int s = s2p.first()
        printed.add(s)
        j = j + 1
    }
}
```

And the shape his tradition cares most about — the **client–server exchange**,
whose deadlock-freedom the Welch/Martin design rules argue by ordering — is certified here by the same
theorem, mechanised (the wait-for order is well-founded), *and* its value proves:

<!-- doclint:case p246-kerridge-gallery/client-server-request-reply-certified-and-proved -->
```groovy
@Ensures({ result == x + 1 })
static int clientServer(int x) {
    val request = AsyncChannel.<Integer>create(1)
    val reply = AsyncChannel.<Integer>create(1)
    request.send(x)
    async { int r = request.first(); reply.send(r + 1) }
    return reply.first()
}
```

And **ALT** — occam's alternation, the construct every multiplexer and fair-server in the books is built on —
is `ChannelSelect`. One-shot, it is a nondeterministic choice among the producers that can be ready, so the
spec must cover both; which branches *can* be ready is decided exactly (a producer that only runs after the
choosing process moves on is never the one taken), and the wait-for order treats the ALT as an OR node —
a deadlock only if *every* guard is stuck:

<!-- doclint:case p246-kerridge-gallery/alt-take-whichever-producer-is-ready -->
```groovy
@Ensures({ result == x || result == y })
static int alt(int x, int y) {
    val left = AsyncChannel.<Integer>create(1)
    val right = AsyncChannel.<Integer>create(1)
    async { left.send(x); left.close() }
    async { right.send(y); right.close() }
    ChannelSelect.Result chosen = await ChannelSelect.from(left, right).select()
    int v = (int) chosen.value
    return v
}
```

And the **multiplexer** — `ALT` *in a loop*, the shape every merging process and fair server in the books is
built on — over two generators: the merged count proves for symbolic counts, the interleaving stays what it
is (an order claim is refuted, honestly), and one iteration too many is the named hang (Phase 253):

<!-- doclint:case p246-kerridge-gallery/the-multiplexer-alt-in-a-loop-merges-two-generators-count-proved -->
```groovy
@Requires({ na >= 0 && nb >= 0 })
@Ensures({ result.size() == na + nb })
static List<Integer> multiplex(int na, int nb) {
    val left = AsyncChannel.<Integer>create(4)
    val right = AsyncChannel.<Integer>create(4)
    async {
        int i = 0
        @Invariant({ 0 <= i && i <= na })
        @Decreases({ na - i })
        while (i < na) {
            left.send(i)
            i = i + 1
        }
        left.close()
    }
    async {
        int i = 0
        @Invariant({ 0 <= i && i <= nb })
        @Decreases({ nb - i })
        while (i < nb) {
            right.send(i)
            i = i + 1
        }
        right.close()
    }
    val merged = AsyncChannel.<Integer>create(8)
    int j = 0
    @Invariant({ 0 <= j && j <= na + nb })
    @Decreases({ na + nb - j })
    while (j < na + nb) {
        ChannelSelect.Result taken = await ChannelSelect.from(left, right).select()
        int v = (int) taken.value
        merged.send(v)
        j = j + 1
    }
    merged.close()
    return merged.toList()
}
```

## The student mistakes are named compile errors

The book teaches deadlock by *running into it* — build the network, watch it hang, discuss. Here the same
exercises refuse to compile, each with its cause spelled out:

<!-- doclint:case p246-kerridge-gallery/the-deadlock-exercise-a-mutual-receive-cycle-is-refuted -->
```groovy
static int deadlockExercise() {
    val aToB = AsyncChannel.<Integer>create(1)
    val bToA = AsyncChannel.<Integer>create(1)
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

What stays out of reach says so. Streaming is covered on both sides for **specified unit-counter loops**
(`while (i < n) … i = i + 1`, or C-style, carrying the loop's `@Invariant` / `@Decreases`, the counter the
variable the guard tests): the generator's termination (Phase 250) and sequence (Phase 251), and the looping
consumer's reads with their block-forever obligations (Phase 252). A `while (true)` process, a range
`for`-in with a symbolic bound, two sends or two receives of one channel per iteration, or a `first()`
outside such a loop refuses the value model with the reason named; the accumulating `for (v in ch)` drain
is the loop engine's own boundary, so drained values are spelled `toList()` or collected in a loop. The
looping `ALT` — the multiplexer — is covered too (Phase 253), with the interleaving left exactly as
nondeterministic as it is.

The **non-terminating process** — `while (true) { … }`, which is how the book actually writes `GNumbers`,
`GPrint` and every server — is covered for its **safety half** (Phase 254): the loop's invariant preserved
per iteration, every send meeting its channel contract, every received value carrying its producer's
relation; termination is not claimed, and the one thing that cannot be proved this way — that a receive from
an infinite producer is *eventually served* — is assumed and said so in a network note. Every certificate on
this page rests on a count or an invariant, and that is exactly the line. What remains is the **liveness**
half: every element sent is eventually received, the server eventually answers every client, the network
as a whole never deadlocks over an infinite run. That is not a count and not an invariant: it needs a
*fairness* assumption about the scheduler and about `ALT`'s choice, and a temporal argument (the
"eventually") that the sequential fragment has no word for. That, and the session-typed protocol view of a
channel, is the research conversation, not a demo: the same guarantees GPP establishes offline by formal
methods, issued incrementally by the compiler.

As everywhere in the [concurrency gallery](concurrency.md): the scheduler, the JMM, and atomicity remain
the [three runtime rungs](../CONCURRENCY.md) — these certificates are action-grained and above the memory
model, exactly as CSP's own semantics are.
