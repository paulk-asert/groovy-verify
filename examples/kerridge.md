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

This gallery ports those teaching shapes onto Groovy 6's `groovy.concurrent` (channels as `AsyncChannel`,
`PAR` arms as `async {}` tasks, the delta as `BroadcastChannel`, `ALT` as `ChannelSelect`) and runs them
under the [SEQ/PAR ladder](concurrency.md) (Phases 240–271) — where the corresponding certificates are
issued **in the compiler**, as ordinary static type-checking errors, rather than established offline. The
shapes are **inspired by UCaPE, written ourselves** — the repository carries no licence and JCSP is LGPL, so
ideas are ported, never sources (the same rule as the jcstress-inspired examples).

**What is in it.** Twenty-one worked examples, every one linked to a case that runs in CI.
[Twelve shapes that verify](#the-one-shot-shapes-verify-end-to-end) — c02's hello-world; the literal
two-message `ProduceHW` / `ConsumeHW`, proved in order; `GSquares`, `GPlus`, `GDelta`, `GPrint`; c03 three
ways, with a literal trip count, with a symbolic `n`, and as three `while (true)` processes; client–server;
`ALT`; the multiplexer; the fair server, withheld and then certified. Then the
[student mistakes as named compile errors](#the-student-mistakes-are-named-compile-errors) — the
mutual-receive deadlock with its wait cycle spelled out receive by receive, the missing poison pill, two
producers on one one2one, reading past the last send — each shown with the compiler's verbatim message, and
[what a refuted value claim hands back](#and-a-wrong-claim-comes-back-with-a-counterexample): a
counterexample you can run. The primed token ring and a three-role protocol close the mechanism sections.

**What it covers, and what it does not.** The gallery is organised by *construct*, not by chapter: the
sixteen rows of the table below are the JCSP/occam vocabulary the books are built on, and the twenty-one
examples are the smallest programs that exercise each. Measured against the books' own corpus it is a thin
slice — UCaPE's examples run c02 to c25, with a parallel tree of exercises, and only c02 and c03 are ported
here by name; the client–server, `ALT`, multiplexer, fair-server and token-ring shapes recur across the
later chapters rather than belonging to any one of them. GPP is cited as the tradition this work answers,
not ported: its own vocabulary — `DataClass`, the worker and collector components, the CSPm/FDR
definitions — has no representation here.

**What is proved, and what is assumed.** Values end-to-end through the channels; deadlock-freedom as
well-foundedness of the wait-for order, with `ALT` as an OR node; safety of networks that never stop, and
liveness under **weak fairness** — [stated as an assumption](#how-deadlock-liveness-and-starvation-are-certified),
nothing more. `@ServedWithin` and `@DeliveredWithin` are head-of-line service bounds; queueing behind a
backlog is [deliberately outside the claim](#the-honest-boundary-loudly). The scheduler, the JMM and
atomicity stay below the line, exactly as CSP's own semantics are.

**Two findings went upstream.** Modelling `ALT` as Groovy 6 actually implemented it showed there was no fair
selection, and that a losing branch's element was re-sent to the back of its queue — now **GROOVY-12320**, a
held `fair()` / `random()`. The racing mixed choice needed real arbitration — now **GROOVY-12323**,
`offers(send(…), receive(…))` over rendezvous channels. Both merged for 6.0.0-beta-4; the
[version note](#groovy-version-note) says what each runtime can and cannot certify.

To run the gallery: `./gradlew verify -Pcases='P246 Kerridge gallery'`, with `VERIFY_VERBOSE=1` to see the
diagnostics and counterexamples rather than one line of pass/fail per case.

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
them back the other way round and the postcondition is refuted — [below](#the-student-mistakes-are-named-compile-errors)):

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

<!-- doclint:diagnostic p246-kerridge-gallery/the-fair-server-per-client-liveness-withheld-with-the-runtime-s-reason -->
```
[Static type checking] - Skipped network well-formedness check for fairServer (the receive on 'replyA'
(line 48) is served only when the ALT in the loop at line 62 takes branch 0 — ChannelSelect prefers the
lowest ready index, so whether this client is ever chosen depends on timing; per-client liveness is not
certified …). The deadlock-freedom certificate covers one-shot networks of unconditional sends and receives
on local channels; outside that the network is neither certified nor refuted.
```

(The elided tail is the one part of this message that moves with the runtime: before beta-4 it names
GROOVY-12320 as the missing feature, after it points at the held `fair()` instance you should have used.)

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
exercises refuse to compile, each with its cause spelled out. Every message below is what the compiler
really prints — `./gradlew docLint` compiles each case and fails the build if a quoted diagnostic drifts
from it — with two reading notes: a `…` marks text elided for length, and the line numbers are the compiled
file's, so they don't line up with the snippet above them.

**The deadlock exercise.** Two processes, each reading from the other before it writes:

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

<!-- doclint:diagnostic p246-kerridge-gallery/the-deadlock-exercise-a-mutual-receive-cycle-is-refuted -->
```
[Static type checking] - Process-network deadlock in 'deadlockExercise': circular wait: the receive on
'bToA' (line 41 in the task forked at line 41), which waits for the send on 'bToA' (line 42 in the task
forked at line 42), which waits for the receive on 'aToB' (line 42 in the task forked at line 42), which
waits for the send on 'aToB' (line 41 in the task forked at line 41), which waits for the first. A one-shot
channel network is deadlock-free exactly when its wait-for order is well-founded; this one blocks forever.
Move the send before the blocking receive, fork the producer before awaiting its consumer, or let a
concurrent task serve the channel.
```

The second half is the part a student can act on: the *theorem* the verdict rests on, then the three ways
out — which are the design rules the books teach, arriving at the moment the mistake is made.

**The missing poison pill.** A consumer draining a stream nobody ever ends:

<!-- doclint:case p246-kerridge-gallery/the-missing-end-of-stream-an-unclosed-drain-is-refuted -->
```groovy
static int missingPoison() {
    AsyncChannel<Integer> stream = AsyncChannel.create(4)
    stream.send(1)
    async {
        int seen = 0
        for (v in stream) {
            seen = seen + 1
        }
    }
    return 0
}
```

<!-- doclint:diagnostic p246-kerridge-gallery/the-missing-end-of-stream-an-unclosed-drain-is-refuted -->
```
[Static type checking] - Process-network deadlock in 'missingPoison': the iteration over 'stream' (line 43)
can never finish — no close() on 'stream' anywhere in the method. …
```

**Two producers on one one2one channel** — the discipline JCSP polices at runtime, here refused before the
program exists:

<!-- doclint:case p246-kerridge-gallery/two-producers-race-a-one2one-channel-refuted -->
```groovy
static int notOne2One() {
    AsyncChannel<Integer> connect = AsyncChannel.create(2)
    async { connect.send(1) }
    async { connect.send(2) }
    return connect.first()
}
```

<!-- doclint:diagnostic p246-kerridge-gallery/two-producers-race-a-one2one-channel-refuted -->
```
[Static type checking] - Channel linearity violation in 'notOne2One': two concurrent senders on 'connect' —
the async task forked at line 40 and the async task forked at line 41 both use its send-end, so the element
order is a race. A point-to-point channel has one live process per end — one sender, one receiver (FIFO
per-element reasoning depends on it). Make the conflicting uses sequential, give each producer its own
channel, or use a BroadcastChannel (subscribing before any sender starts) for one-to-many delivery.
```

**Reading more than was written.** A consumer that takes a second message from a producer that sent one —
the FIFO pairing of Phase 247 knows there is no send to match it:

<!-- doclint:case p247-bounded-fifo/a-receive-past-the-last-send-can-never-be-satisfied -->
```groovy
static int overReceive(int x) {
    AsyncChannel<Integer> src = AsyncChannel.create(2)
    async { src.send(x); src.close() }
    int a = src.first()
    int b = src.first()
    return a + b
}
```

<!-- doclint:diagnostic p247-bounded-fifo/a-receive-past-the-last-send-can-never-be-satisfied -->
```
[Static type checking] - Process-network deadlock in 'overReceive': the 2nd receive on 'src' (line 42) can
never be satisfied — only 1 send on 'src' anywhere in the method. …
```

**And the values, not only the structure.** `ConsumeHW` reading the two messages back the other way round
is a perfectly good *network* — nothing blocks, nothing races — and it still refuses to compile, because
the claim it makes about what comes out is false:

<!-- doclint:case p246-kerridge-gallery/consumehw-read-in-the-wrong-order-is-refuted -->
```groovy
@Ensures({ result == 'Hello World' })
static String produceHW() {
    AsyncChannel<String> connect = AsyncChannel.create(2)
    async { connect.send('Hello'); connect.send('World'); connect.close() }
    String first = connect.first()
    String second = connect.first()
    return second + ' ' + first
}
```

<!-- doclint:diagnostic p246-kerridge-gallery/consumehw-read-in-the-wrong-order-is-refuted -->
```
[Static type checking] - Cannot prove postcondition of produceHW holds on this return path
    ensured: (result == Hello World)
    fails on: produceHW()
```

No counterexample line there, and that is the honest output: `produceHW()` takes no parameters, so there is
nothing to instantiate — the failing call *is* the whole witness. Give a claim something to range over and
the next section is what comes back instead.

## …and a wrong claim comes back with a counterexample

The four refutations above carry no counterexample and need none: for a circular wait, a racing send-end or
an unmatched receive, the cited chain of waits **is** the witness — there is no model to exhibit, because
nothing about the values decides it. Every claim that ranges over *values*, though, is refuted the way the
rest of the verifier refutes: with an instantiation you can go and run.

**Reading one element past the producer** (Phase 252) — the off-by-one every teaching pipeline meets. The
consumer loops `n + 1` times over a generator that sends `n`:

<!-- doclint:case p252-streaming-consumers/a-consumer-reading-past-the-producer-may-block-forever -->
```groovy
@Requires({ n >= 0 })
@Ensures({ result == n + 1 })
static int overRead(int n) {
    AsyncChannel<Integer> out = AsyncChannel.create(4)
    async {
        int i = 0
        @Invariant({ 0 <= i && i <= n })
        @Decreases({ n - i })
        while (i < n) {
            out.send(i)
            i = i + 1
        }
        out.close()
    }
    int seen = 0
    int i = 0
    @Invariant({ 0 <= i && i <= n + 1 && seen == i })
    @Decreases({ n + 1 - i })
    while (i < n + 1) {
        int v = out.first()
        seen = seen + 1
        i = i + 1
    }
    return seen
}
```

<!-- doclint:diagnostic p252-streaming-consumers/a-consumer-reading-past-the-producer-may-block-forever -->
```
[Static type checking] - Assertion may not hold: the receive on 'out' (line 57) may block forever — the
element it reads may never be sent (the consumer loop reads past what the producer loop sends)
    counterexample: i = 0, … n = 0, …
    fails on: overRead(0)
```

`n = 0` is the smallest witness there is: a generator that sends nothing at all, and a consumer that still
reads once. It is the same shape as the wrap-around philosopher in the
[concurrency gallery](concurrency.md) — the verifier doesn't say "this might hang", it hands back the
trip count at which it does.

**Claiming an order the ALT does not give** (Phase 253). Strengthen the multiplexer's `@Ensures` from the
count to `result.size() == na + nb && result[0] == 0` — "the first merged element is the left producer's
first" — and the honest answer comes back:

<!-- doclint:diagnostic p253-looping-alt/the-merge-order-is-nondeterministic-an-order-claim-is-refuted -->
```
[Static type checking] - Cannot prove postcondition of merge holds on this return path
    ensured: ((result.size() == (na + nb)) && (result[0] == 0))
    counterexample: … na = 1, …
    fails on: merge(1, …
```

One element on the left and the select still free to take a right-hand one first — a scenario you can
picture, rather than a "not proved". The *count* claim, on the same network, proves: nondeterminism costs
you the order and nothing else.

The right-hand count is elided above because it is the solver's free choice, not a forced boundary — the
same case answers `merge(1, 7720)` on 6.0.0-beta-3 and `merge(1, 1)` on a beta-4 runtime, both valid
witnesses to the same gap. Contrast `overRead(0)` and `clientServer(0, 1)`: those *are* forced — the
obligation admits no smaller failure — and they come back identical on both runtimes.

**A server bounded above its clients** (Phase 261) — a cycle whose members both terminate, but not
together. The server loops `m` times, the client asks `n < m` times, and the server's last read waits for a
request that never comes:

<!-- doclint:case p261-finite-cycles/a-server-bounded-above-its-clients-waits-forever-for-a-request-refuted -->
```groovy
@Requires({ 0 <= n && n < m })
static void clientServer(int n, int m) {
    AsyncChannel<Integer> request = AsyncChannel.create(4)
    AsyncChannel<Integer> reply = AsyncChannel.create(4)
    async {                                              // the server
        int j = 0
        @Invariant({ 0 <= j && j <= m })
        while (j < m) {
            int q = request.first()
            reply.send(q + 1)
            j = j + 1
        }
    }
    int i = 0
    @Invariant({ 0 <= i && i <= n })
    @Decreases({ n - i })
    while (i < n) {                                      // the client
        request.send(i)
        int r = reply.first()
        assert r == i + 1
        i = i + 1
    }
}
```

<!-- doclint:diagnostic p261-finite-cycles/a-server-bounded-above-its-clients-waits-forever-for-a-request-refuted -->
```
[Static type checking] - Assertion may not hold: the receive on 'request' (line 46) may block forever — the
producer loop at line 52 sends n - 0 element(s) in all, and this loop reads past them
    counterexample: … m = 1, n = 0 …
    fails on: clientServer(0, 1)
```

`clientServer(0, 1)` — a client that asks nothing and a server that insists on answering once. The
diagnostic names the *total* the partner will send (`n - 0`), which is the fact the reader had to discharge
and couldn't, and the counterexample is the smallest mismatch of the two bounds.

A caveat worth stating, since it decides which of these are worth quoting. Counterexamples over a method's
own **parameters** read like the three above. The cycle proofs — rely/guarantee through the `taken` / `sent`
ghosts — are refuted just as sharply, but their models are stated in the encoder's own vocabulary
(`aToB$q.size()`, `reply$rely4.size()`, `loop$fuel1`), which is honest and unhelpful in equal measure. For
those, the message is the teaching material and the model is for whoever is debugging the encoding.

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
