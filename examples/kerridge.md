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
| `Channel.one2one()` | `AsyncChannel<Integer> c = AsyncChannel.create(n)` | one live process per end, checked (Phase 241); a bounded FIFO — the *k*-th write is the *k*-th read (Phase 247) |
| a `CSProcess` under `PAR` | an `async { }` task | fork-window disjointness, checked (Phase 240) |
| typed channel discipline | Bean Validation bounds on the element type | checked at sends, assumed at opaque receives (Phase 242) |
| the client-server design rule | the wait-for order | deadlock-freedom proved as well-foundedness; a cycle is a spelled-out error (Phase 243) |
| poison pill / formal termination | `close()` | a drain provably finishes; a missing close is a named error (Phase 245) |
| `GDelta` (copy to every branch) | `BroadcastChannel.subscribe()` | every subscriber sees the element — fan-out *proves* |
| `GNumbers` with a literal count | a `for (n in 1..N)` producer loop | unrolled: the stream is bounded traffic, the pipeline proves (Phase 248) |
| `GNumbers(n)`, symbolic | a `while (i < n) { … i = i + 1 }` producer loop with `@Invariant` / `@Decreases` + `close()` | termination certified (Phase 250); the drained sequence proves element by element — the channel is the list the loop builds (Phase 251) |
| a looping process (`GPrint`, `GSquares` as a `while` reading its input) | a `while (i < n) { v = in.first(); … }` loop with `@Invariant` / `@Decreases` | reads element *k*; reading past the producer "may block forever" (Phase 252) |
| a process that never stops (`GNumbers`, `GPrint`, a server, as the book writes them) | `while (true) { … }` with an `@Invariant` | safety certified — invariant, send contracts, received values (Phase 254); liveness certified under weak fairness — a receive-first cycle is a circular wait in every iteration, a priming send breaks it (Phase 255) |
| `ALT` | `await ChannelSelect.from(a, b).select()` | a choice among the branches that can be ready — value *and* index proved; an OR node in the wait-for order (Phase 249) |
| `ALT` in a loop (the multiplexer, the fair server's read side) | `while (j < n) { Result r = await ChannelSelect.from(a, b).select(); … }` | ghost cursors per branch; the merged count proves, the order is nondeterministic, one iteration too many "may block forever" (Phase 253); modelled as the runtime selects — lowest ready index, losers re-sent — with starvation hazards named (Phase 256) |
| the history of a channel (a trace) | `c.taken` / `c.sent` in a loop `@Invariant` | the elements this loop has taken from / sent on `c` so far, lists the invariant quantifies over — `Forall.range(0, i, { int k -> c.taken[k] == 2 * k + 1 })`, `Forall.range(0, c.sent.size(), { int k -> c.sent[k] == Fib.of(k) })` (Phases 259/260); bound a law a *partner* relies on by the ghost's own size |
| starvation-freedom in the large (served within a bound) | `@ServedWithin(n)` on the method | certified for a held `fair()` over k <= n branches (the rotation's own arithmetic); refuted with the policy's reason otherwise (Phase 265) |
| end-to-end latency through a pipeline | `@DeliveredWithin(value = n, from = 'c', to = 'd')` | the head-of-line service bound, summed hop by hop (a stage is 1, a held `fair()` ALT its branch count), the worst path deciding; queueing is loudly not claimed (Phase 266) |
| a protocol / a session (Kerridge's process interfaces as a conversation) | `@Protocol({ loop { request: client >> server; reply: server >> client } })` on the method — plain Groovy, parsed by Groovy (`text = '''…'''` keeps the string form; `./gradlew nuscrCheck` exports the corpus as real Scribble for the MPST tools, the mixed choice refused as outside their fragment) | the network's global type, projected onto each role and checked against every process's control flow — a violation named with its trace; `par { … } and { … }` interleaves independent sub-sessions, which types the fair server (Phases 263/264) |
| `fairSelect` / `priSelect` | `ChannelSelect alt = ChannelSelect.from(a, b).fair()` held before the loop / plain `select()` | from Groovy 6.0.0-beta-4 (GROOVY-12320): a held `fair()` rotates from the last winner — the fair server's per-client liveness is certified; before it, withheld with the runtime's reason (Phases 256/257) |

A note on spelling: the ports declare their channels with the **element type on the left** —
`AsyncChannel<Integer> c = AsyncChannel.create(n)` — because that is what tells static type checking (and
the checker) what flows through the channel: `create(n)` has no argument that could fix `T`, so a bare
`def c = AsyncChannel.create(n)` is an `AsyncChannel<Object>` and neither side can say anything about its
elements. (`def` / `var` / `val` with a type witness, `val c = AsyncChannel.<Integer>create(n)`, is also supported
and pinned by a case; but an element *contract* — `AsyncChannel<@PositiveOrZero
Integer>`, Phase 242 — has to sit on a declared generic anyway.) The one place a declared type is required
rather than merely idiomatic is an ALT's result, `ChannelSelect.Result r = await …` (Phase 249).

## The one-shot shapes verify end to end

The book's first network — c02's `RunHelloWorld`, a producer and consumer under `PAR` over a one2one
channel — with the exchanged value *proved*:

<!-- doclint:case p246-kerridge-gallery/c02-hello-world-the-one-message-exchange-proves -->
```groovy
@Ensures({ result == 'Hello' })
static String helloWorld() {
    AsyncChannel<String> connect = AsyncChannel.create(1)
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
    AsyncChannel<String> connect = AsyncChannel.create(2)
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
    AsyncChannel<Integer> n2s = AsyncChannel.create(4)
    AsyncChannel<Integer> s2p = n2s.map { it * it }
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
    AsyncChannel<Integer> n2s = AsyncChannel.create(4)
    AsyncChannel<Integer> s2p = n2s.map { it * it }
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
    AsyncChannel<Integer> n2s = AsyncChannel.create(4)
    AsyncChannel<Integer> s2p = AsyncChannel.create(4)
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
preserved through `GSquares`' and `GNumbers`' relations — and for **liveness under weak fairness** (Phase 255):
no receive in the pipeline waits on itself within an iteration, so every one is eventually served. Termination
alone is not claimed; none is meant:

<!-- doclint:case p246-kerridge-gallery/c03-forever-gnumbers-gsquares-and-gprint-as-non-terminating-processes-safety-proved -->
```groovy
static void network() {
    AsyncChannel<Integer> n2s = AsyncChannel.create(4)
    AsyncChannel<Integer> s2p = AsyncChannel.create(4)
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

And the **server that answers forever** — the client sending a request then waiting for its reply, the
server waiting for a request then replying, both `while (true)` — is certified **live under weak
fairness** (Phase 255): the request is always one message ahead of the wait for its reply. Let the client
wait before asking and it is the mutual-receive deadlock — *in every iteration*, spelled out:

<!-- doclint:case p246-kerridge-gallery/client-and-server-forever-live-under-weak-fairness -->
```groovy
static void clientServer() {
    AsyncChannel<Integer> request = AsyncChannel.create(4)
    AsyncChannel<Integer> reply = AsyncChannel.create(4)
    async {                                              // the server
        int j = 0
        @Invariant({ j >= 0 })
        while (true) {
            int q = request.first()
            reply.send(q + 1)
            j = j + 1
        }
    }
    int i = 0
    @Invariant({ i >= 0 })
    while (true) {                                       // the client
        request.send(i)
        int r = reply.first()
        i = i + 1
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
    AsyncChannel<Integer> request = AsyncChannel.create(1)
    AsyncChannel<Integer> reply = AsyncChannel.create(1)
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
    AsyncChannel<Integer> left = AsyncChannel.create(1)
    AsyncChannel<Integer> right = AsyncChannel.create(1)
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
    AsyncChannel<Integer> left = AsyncChannel.create(4)
    AsyncChannel<Integer> right = AsyncChannel.create(4)
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
    AsyncChannel<Integer> merged = AsyncChannel.create(8)
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

And the **fair server** — two clients, a server taking whichever request is ready and replying on that
client's own channel — is where the gallery meets the runtime's own selection semantics. On a runtime
whose select races receives (priority by list order, a losing branch's element re-sent to the back of its
queue, no fair selection), the checker models exactly that and *withholds* per-client liveness with the
reason:

<!-- doclint:case p246-kerridge-gallery/the-fair-server-per-client-liveness-withheld-with-the-runtime-s-reason -->
```groovy
static void fairServer() {
    AsyncChannel<Integer> reqA = AsyncChannel.create(4)
    AsyncChannel<Integer> reqB = AsyncChannel.create(4)
    AsyncChannel<Integer> replyA = AsyncChannel.create(4)
    AsyncChannel<Integer> replyB = AsyncChannel.create(4)
    async {                                              // client A
        int i = 0
        @Invariant({ i >= 0 })
        while (true) {
            reqA.send(i)
            int r = replyA.first()
            i = i + 1
        }
    }
    async {                                              // client B
        int i = 0
        @Invariant({ i >= 0 })
        while (true) {
            reqB.send(i)
            int r = replyB.first()
            i = i + 1
        }
    }
    int j = 0
    @Invariant({ j >= 0 })
    while (true) {                                       // the server
        ChannelSelect.Result r = await ChannelSelect.from(reqA, reqB).select()
        int q = (int) r.value
        if (r.index == 0) {
            replyA.send(q + 1)
        }
        if (r.index == 1) {
            replyB.send(q + 1)
        }
        j = j + 1
    }
}
```

> Skipped network well-formedness check … the receive on 'replyB' … is served only when the ALT in the loop
> at line N takes branch 1 — ChannelSelect prefers the lowest ready index, so whether this client is ever
> chosen depends on timing; per-client liveness is not certified (a fair selection needs GROOVY-12320, Groovy
> 6.0.0-beta-4+).

On a runtime with the claim-based select (see the [version note](#groovy-version-note)) `select()`
dequeues exactly one branch, losers untouched, and offers `fair()`: hold the instance — the rotation state
lives in it — and the same server's per-client liveness is **certified**: every ready client is taken
within two selects (the rotation's own arithmetic), each request precedes the wait for its reply (a client
that waits before asking is withheld, with that reason), and the server loop is live, so every client is
served under weak fairness. The reply's *value* is proved too: the guarded `replyA.send(q + 1)` is a
**conditional stream** — one element per choice of its branch, its k-th element `q + 1` over the k-th
request taken from `reqA` — and the cycle (clients waiting on the server, the server waiting on the
clients) is argued by rely/guarantee, each loop reading its partner's stream through a view constrained by
the partner's invariants and the FIFO law. So the server below verifies whole, and a client that asserts
`r == i + 1` after its receive proves it — while `r == i + 2` is refuted with a counterexample. Call
`.fair()` on a fresh instance inside the loop instead and the checker names the mistake — no rotation
state, priority in effect:

<!-- doclint:case p246-kerridge-gallery/the-fair-server-with-a-held-fair-select-per-client-liveness-certified-groovy-6-0-0-beta-4 -->
```groovy
static void fairServer() {
    AsyncChannel<Integer> reqA = AsyncChannel.create(4)
    AsyncChannel<Integer> reqB = AsyncChannel.create(4)
    AsyncChannel<Integer> replyA = AsyncChannel.create(4)
    AsyncChannel<Integer> replyB = AsyncChannel.create(4)
    async {                                              // client A
        int i = 0
        @Invariant({ i >= 0 })
        while (true) {
            reqA.send(i)
            int r = replyA.first()
            i = i + 1
        }
    }
    async {                                              // client B
        int i = 0
        @Invariant({ i >= 0 })
        while (true) {
            reqB.send(i)
            int r = replyB.first()
            i = i + 1
        }
    }
    ChannelSelect alt = ChannelSelect.from(reqA, reqB).fair()   // held: the rotation state lives here
    int j = 0
    @Invariant({ j >= 0 })
    while (true) {                                       // the server
        ChannelSelect.Result r = await alt.select()
        int q = (int) r.value
        if (r.index == 0) {
            replyA.send(q + 1)
        }
        if (r.index == 1) {
            replyB.send(q + 1)
        }
        j = j + 1
    }
}
```

## The student mistakes are named compile errors

The book teaches deadlock by *running into it* — build the network, watch it hang, discuss. Here the same
exercises refuse to compile, each with its cause spelled out:

<!-- doclint:case p246-kerridge-gallery/the-deadlock-exercise-a-mutual-receive-cycle-is-refuted -->
```groovy
static int deadlockExercise() {
    AsyncChannel<Integer> aToB = AsyncChannel.create(1)
    AsyncChannel<Integer> bToA = AsyncChannel.create(1)
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

## How deadlock, liveness and starvation are certified

The certificates above rest on a small number of mechanisms, each worth knowing by name.

**Deadlock is well-foundedness of the wait-for order.** Every receive waits for a send, every drain waits
for a close; the checker builds that graph and demands it be well-founded. For a one-shot network the graph
must be acyclic — a cycle *is* the deadlock, and the error spells out the loop of waits, receive by receive
(the mutual-receive student exercise above). An `ALT` enters the graph as an **OR node**: it is stuck only
if *every* branch is stuck, which is why a multiplexer over live producers certifies while a knot whose
every branch waits on its own output does not.

**Forever processes lift the same graph to the iteration index.** A `while (true)` network has no final
state to be safe in, so the wait-for graph is built *per iteration*: an edge of weight 0 means "waits for
the partner's send in the same round", and a cycle in the weight-0 subgraph is a circular wait in **every**
round — the receive-first pair. A priming send before a loop is one message of head start — a negative
edge that breaks the cycle — which is exactly why the token ring with `ab.send(0)` is live and the same
ring without it deadlocks in round one. Liveness then follows by a completion fixpoint under one stated
assumption, **weak fairness**: a process whose next operation is enabled eventually executes it. Nothing
else about scheduling is assumed, and nothing about cross-process ordering — a multiplexer's interleaving
stays exactly as nondeterministic as it is. A *terminating* partner adds an obligation instead of an
assumption: reading element `k` from a producer that sends `m` in all is refuted unless `k < m` — the read
that would block forever is named, with the total ("a `while (true)` server of a bounded client waits
forever for the request after the last").

**Values cross processes as streams and, in cycles, by rely/guarantee.** A specified producer loop makes
its channel *be* the list the loop builds, so a consumer's k-th receive is that list's k-th element and
element-wise claims prove. When two loops answer each other — client and server, a ring — no sequential
order of the loops exists, so each reads its partner through a view constrained by the partner's own loop
invariant plus one law of the channel itself: what a consumer has *taken* is a prefix of what its producer
sent. The histories in that argument are nameable in specs as the ghosts `c.taken` and `c.sent`:

<!-- doclint:case p259-taken-ghost/the-primed-cycle-what-a-has-taken-is-2k-1-so-what-it-reads-is-2i-1-proved -->
```groovy
static void primed() {
    AsyncChannel<Integer> aToB = AsyncChannel.create(4)
    AsyncChannel<Integer> bToA = AsyncChannel.create(4)
    async {                                              // A: one message ahead
        aToB.send(0)
        int i = 0
        @Invariant({ i >= 0 && Forall.range(0, i, { int k -> bToA.taken[k] == 2 * k + 1 }) })
        while (true) {
            int x = bToA.first()
            assert x == 2 * i + 1
            aToB.send(x + 1)
            i = i + 1
        }
    }
    int j = 0
    @Invariant({ j >= 0 })
    while (true) {                                       // B
        int y = aToB.first()
        bToA.send(y + 1)
        j = j + 1
    }
}
```


The token goes round with a value: A primes `0`, B answers `y + 1`, A reads `2i + 1` at its i-th turn —
proved because A's invariant says what it has *taken* so far, B's law says what it sends is what it took
plus one, and the FIFO law binds B's taken to A's sent. The three-process ring proves `3i + 2` the same
way, and `2k` in place of `2k + 1` is refuted at its base case. The twin ghost `c.sent` serves a producer
whose values are loop-written — a counting server, a Fibonacci generator — which states its own stream law
(`Forall.range(0, c.sent.size(), { int k -> c.sent[k] == Fib.of(k) })`) for its readers to prove against.
And the cycle that ends cleanly — a client that closes its request channel after its loop, a server that
*drains* it until the close — verifies whole, the drain's termination being the client's close.

**Starvation and service bounds are the selection policy's own arithmetic.** A branch listed after an
always-ready one under a priority select may wait forever — a named hazard, not a warning. A *held*
`fair()` select rotates from the last winner, so over k branches a ready branch is taken within k selects:
that arithmetic certifies `@ServedWithin(n)` for n ≥ k, refutes it under priority ("no bound at all"),
`random()` ("fair in expectation only") and a fresh-instance `fair()` ("keeps no rotation state"), and
composes across hops — `@DeliveredWithin(value = n, from = 'c', to = 'd')` sums one step per plain stage
and k per fair merge along every path, the worst path deciding. These are **head-of-line** service bounds;
queueing behind a backlog is deliberately outside the claim.

**Protocols are session types, checked by projection.** A `@Protocol` closure is the network's global
type; the checker projects it onto each role and checks every process's control flow against its
projection, naming a violation with the trace that reaches it:

<!-- doclint:case p263-session-types/the-primed-token-ring-follows-a-three-role-protocol-that-says-the-priming -->
```groovy
@Protocol({
    ab: a >> b                       // the priming token
    loop {
        bc: b >> c
        ca: c >> a
        ab: a >> b
    }
})
static void ring() {
    AsyncChannel<Integer> ab = AsyncChannel.create(4)
    AsyncChannel<Integer> bc = AsyncChannel.create(4)
    AsyncChannel<Integer> ca = AsyncChannel.create(4)
    async {                                              // b
        int j = 0
        @Invariant({ j >= 0 })
        while (true) {
            int y = ab.first()
            bc.send(y + 1)
            j = j + 1
        }
    }
    async {                                              // c
        int m = 0
        @Invariant({ m >= 0 })
        while (true) {
            int z = bc.first()
            ca.send(z + 1)
            m = m + 1
        }
    }
    ab.send(0)                                           // a
    int i = 0
    @Invariant({ i >= 0 })
    while (true) {
        int x = ca.first()
        ab.send(x + 1)
        i = i + 1
    }
}
```


Leave the priming out of the protocol and the first send is the violation ("sends on 'ab' (line 40) where
the protocol expects it to receives from 'ca'"); make a client wait before asking and the trace says so. A
choice belongs to one role (`choice at client { … } or { … }`, the client's `if`/`else` against the
server's ALT); `par { … } and { … }` interleaves independent sub-sessions — the fair server's type — and a
*mixed* choice (`choice { ping: left >> right } or { pong: right >> left }`, no `at`) is admitted with its
**coherence** checked across the processes, because each peer can conform alone while together they
collide: one opener and the choice degenerates to that role's, certified; a racing pair is certified only
where the race is genuinely arbitrated — every initiator opening through `offers(send(…), receive(…))
.select()` over **rendezvous** (capacity-0) channels, since a buffered send commits unilaterally and
re-creates the collision — and refused otherwise with the exact missing piece named.

## The honest boundary, loudly

Every certificate stops somewhere it can name, and the stops are these.

**The checker's fragment.** A streaming process is a *specified unit-counter loop* — `while (i < n)`,
`while (true)` or C-style, stepping one variable the guard tests by exactly one, carrying its `@Invariant`
(and `@Decreases` when it ends) — with one send per channel per iteration, one receive per channel per
iteration or one `ALT`, `int` elements, and the pipeline's map stages declared as variables. Anything else
refuses the value model *with the reason named*: a range `for`-in over a symbolic bound, two sends of one
channel in an iteration, a `first()` outside such a loop, a send under an `if` that is not the
`ALT`-guarded reply shape, a drain through a `filter`. Inside the fragment the certificates rest on three
stated facts: sends never block on a buffered channel (queued, the `Awaitable` discarded), the base case of
every loop is the straight-line code before it, and liveness assumes weak fairness — nothing more.

**What is genuinely outside today.** The *queueing* half of latency — delay behind a backlog, which needs
arrival-rate assumptions — is a calculus this gallery deliberately does not carry; its bounds are
head-of-line service bounds and say so. The arbitrated `offers(…)` select is certified at the session layer
(coherence, conformance) but sits outside the *value* model — a racing peer's loop values are honestly
skipped, not proved. And as everywhere in the [concurrency gallery](concurrency.md): the scheduler, the
JMM, and atomicity remain the [three runtime rungs](../CONCURRENCY.md) — these certificates are
action-grained and above the memory model, exactly as CSP's own semantics are.

## Groovy version note

A practical gotcha rather than a boundary: the checker **probes the runtime that hosts it** and models the
selection semantics it finds, so verdicts follow *your* Groovy. On Groovy 6 up to 6.0.0-beta-3 the select
races receives (priority by list order, losers re-sent) — the withheld fair server, the starvation
hazards, and the refuted positional claims above are that runtime's honest verdicts, and the beta-4
spellings are type errors there. From **6.0.0-beta-4** the claim-based select (GROOVY-12320: held
`fair()` / `random()`, losers untouched) makes the fair server certifiable end to end, and the arbitrated
select (GROOVY-12323: `offers(send(…), receive(…))`) makes the racing mixed choice certifiable over
rendezvous channels. Both features originated as findings of this checker — reproduced, drafted, and fixed
upstream — so the examples that need them are marked, and on an older runtime they fail loudly rather than
prove weakly. The same guarantees GPP establishes offline by formal methods, issued incrementally by the
compiler.
