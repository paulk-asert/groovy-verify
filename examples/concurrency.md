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

# Concurrency "lite" examples

> The **structural** half these proofs *assume* — mutual exclusion, interleaving-freedom, deadlock-freedom,
> delivery — is checked separately by Lincheck / TLA+ TLC / Fray / jcstress. See **[CONCURRENCY.md](../CONCURRENCY.md)**.
> Since the SEQ/PAR ladder (Phases 240–245, the later sections of this page), a substantial part of that
> structural half is **checked at compile time** for the one-shot channel fragment: task disjointness,
> channel-end linearity, channel contracts, deadlock-freedom, guarantee conformance, and drain termination.


groovy-verify is a *sequential* SMT-backed checker — it reasons about no thread interleavings, races, or
deadlock. Yet a surprising amount of concurrent code's correctness factors into two halves: a **local,
sequential obligation** the developer must get right, and a **structural guarantee** the runtime provides.
*Assume* the structural half and the local half is an ordinary sequential proof — and that half is usually the
one carrying the interesting bug. These examples prove the local half across eight of Groovy's concurrency
features, each assuming a different structural guarantee:

| Feature | Structural guarantee (assumed) | Local obligation (proven) |
| --- | --- | --- |
| Locks (`@WithWriteLock` / `@Synchronized`) | mutual exclusion | each critical section preserves the monitor invariant |
| Lock ordering (dining philosophers) | deadlock-freedom over all interleavings | each agent acquires its forks in one fixed global order (lower-index-first) |
| Check-then-act (naive `AtomicInteger` use) | atomicity of the *composite* read-then-act (which no single atomic op provides) | the sequential bounded-counter invariant (`count <= 1`) |
| Seqlock (optimistic read) | read-side snapshot atomicity (a validated read reflects a real consistent state under the JMM) | the parity protocol: a write restores `x == y` before republishing, a validated read returns a consistent snapshot |
| Agents / actors | serialization (one message at a time) | each handler preserves the invariant |
| Dataflow | single-assignment | the network computes the right value |
| Channels | FIFO delivery | each element gets the right per-element transform — and, since Phase 241, that each channel end has one live process (channel linearity, checked not assumed; `BroadcastChannel` fan-out proves) |
| `async`/`await` | safe (pure-value) tasks complete | the value an awaited task computes — and, since Phase 240, that nothing a task touches is concurrently written (fork-window disjointness, checked not assumed) |

For the eight rows above these are honest "prove half the property" results: the half SMT can discharge,
which is usually the functional one. The line has moved since they were written, though. What still stays
out is **mutual exclusion itself**, the **scheduler**, and the **JMM** — concurrent-separation-logic and
runtime-rung territory. But for the **one-shot channel fragment** the structural half is now *checked, not
assumed*: the SEQ/PAR ladder (Phases 240–245, the sections after the gallery) certifies task disjointness
(240), one live process per channel end (241), element contracts at every send and opaque receive (242),
**deadlock-freedom as well-foundedness of the wait-for order** (243), bodies honouring their declared
guarantees (244), and drain termination — every blocking operation in a clean network provably completes
(245). Outside that fragment the disclaimers above stand, loudly.

Groovy's **rely/guarantee** support goes further than the eight above — proving *both* halves on a concurrent
buffer, and combining with an information-flow lattice (Graeme Smith's Dafny approach):
**[Thread-local information flow & rely/guarantee (Smith)](smith.md)**.

### Locks — the monitor invariant

Like `@TailRecursive`, Groovy's **lock AST transforms** (`@WithReadLock` / `@WithWriteLock` / `@Synchronized`)
compose with the verifier — and not just trivially. They're *transparent*: the clean body is captured at the
`CONVERSION` phase, before the lock wrapper is woven in at `CANONICALIZATION`, so the verifier proves the
method's contract through the lock as if it weren't there. That lets the **class `@Invariant` stand in as the
lock's monitor invariant**. The classic example — a lock-guarded account that must never overdraw:

<!-- doclint:ignore README illustration: lock-guarded Account (monitor invariant) -->
```groovy
@Invariant({ balance >= 0 })                       // the monitor invariant the lock protects
class Account {
    int balance

    @Requires({ amount >= 0 })
    @Ensures({ balance == old.balance + amount })
    @WithWriteLock
    void deposit(int amount) { balance = balance + amount }

    @Requires({ 0 <= amount && amount <= balance }) // the guard that keeps the invariant
    @Ensures({ balance == old.balance - amount })
    @WithWriteLock
    void withdraw(int amount) { balance = balance - amount }

    @Ensures({ result == balance })
    @WithReadLock
    int currentBalance() { return balance }
}
```

Every critical section is verified to **preserve `balance >= 0`** — and drop the `amount <= balance` guard from
`withdraw` and it refutes (the overdraw is caught). This is exactly the lock-with-resource-invariant
methodology of Chalice/Viper, where *"acquiring a monitor is replaced by an inhale of the corresponding monitor
invariant, releasing by an exhale"* — here, the class `@Invariant` is assumed on method entry and checked
restored on exit. It's the standard reduction of a concurrent safety property to a **per-critical-section
sequential proof**.

**What this is, and isn't.** We verify the sequential half — each critical section maintains the lock
invariant — which, *given* the lock provides mutual exclusion and all access goes through it, is what makes the
invariant a global safety property. We do **not** verify that mutual exclusion (no race on unlocked access,
no deadlock, no lock-ordering); that needs concurrent separation logic with fractional permissions — the
Verus / Viper / VerCors machinery — which is out of scope for an SMT-backed sequential checker.
So this is an honest *monitor-invariant* proof, not a from-scratch proof of thread safety.

Those two disclaimed halves are exercised on this exact example by the runtime checkers in [the structural rungs](../CONCURRENCY.md): a
**Lincheck** spike (`./gradlew lincheckTest`) shows a `synchronized` `Account` is linearizable while an
unlocked one races, and a **Fray** spike (`./gradlew frayCheck`) drives the JVM scheduler over a two-account
bank transfer to confirm ordered locking is deadlock-free — and to catch the lock-ordering deadlock when it
isn't. Same boundary, made concrete; see [`CONCURRENCY.md`](../CONCURRENCY.md).

### Dining philosophers — deadlock-freedom by resource ordering

The bank's two-account lock ordering scales: **dining philosophers** is the N-fork case — and here the verifier
proves the *ordering discipline itself*, not a data invariant. The **resource-hierarchy theorem**: if every agent
acquires its locks in one fixed global order, the wait-for graph is acyclic, so no deadlock. That order is a
thread-local discipline — "philosopher *i* takes the lower-indexed of its two forks first" — and it's pure integer
arithmetic, so the verifier proves it:

<!-- doclint:case p-philosophers/resource-hierarchy-lower-fork-first-is-deadlock-free -->
```groovy
@Requires({ n >= 2 && i >= 0 && i < n })
@Ensures({ result })
static boolean hierarchy(int i, int n) {
    int left = i
    int right = (i + 1) % n
    int first = left < right ? left : right
    int second = left < right ? right : left
    return first < second
}
```

Every philosopher provably acquires its forks low-index-first (`result` — that `first < second` — holds for all
`i`). The **naive** left-then-right scheme — `i < (i + 1) % n` — *refutes*, and the counterexample is the punchline:

```
counterexample: i = 2, n = 3       fails on: naive(2, 3)
```

`i = n-1` is the **wrap-around philosopher**, the one that grabs fork `n-1` then fork `0`, closing the cycle. The
verifier doesn't just flag "deadlock possible" — it names the exact philosopher whose acquisition order is the
local root cause.

**What this is, and isn't.** We prove the *local* ordering discipline; the *global* deadlock-freedom it implies
(the resource-hierarchy theorem's consequence over all interleavings) is the structural half — exercised for real
by **Fray** (`./gradlew frayCheck`), which drives the JVM scheduler over three hand-threaded philosophers and
confirms the ordered version never deadlocks while the naive one does. See [`CONCURRENCY.md`](../CONCURRENCY.md).
*(Dining philosophers is one of [jcstress](https://github.com/openjdk/jcstress)'s classic samples — credited as the
source of the problem; the code here is our own.)*

### Check-then-act — a verified invariant that concurrency breaks

The sharpest illustration of the boundary. A bounded counter: increment only while below the limit. Sequentially
it is bulletproof — `if (count < 1) count = count + 1` can only ever leave `count` at 0 or 1 — and the verifier
**proves** exactly that (drop the bound to `<= 0` and it refutes, so the checker really ran):

<!-- doclint:case p-check-then-act/bounded-counter-sequential-invariant-verifies -->
```groovy
@Invariant({ count <= 1 })
class C {
    int count = 0
    void tryIncrement() { if (count < 1) count = count + 1 }
}
```

And yet it is **not thread-safe**: two threads can both read `count == 0`, both pass the guard, and both
increment — leaving `count == 2`, violating the very invariant just proved. That is **not unsoundness**:
groovy-verify reasons *above* the memory model (rung 1), so the invariant it proves is a *per-thread* property;
whether it composes into a concurrent guarantee is the structural rung's question, and a non-atomic check-then-act
doesn't compose. The killer detail: the verifier proves the **identical** invariant for the racy version and for
a `@WithWriteLock`-fixed `SafeBoundedCounter` (the lock is transparent to it) — **the proof cannot tell the broken
code from the fixed code.** Only the rung can.

**What this is, and isn't.** We prove the sequential invariant — true of any single thread. The concurrent
guarantee needs atomicity the verifier deliberately doesn't model, so it's exercised by **jcstress**
(`./gradlew jcstressCheck`): `BoundedCounterJCStress` runs the two actors billions of times and observes
`count == 2` on `BoundedCounter`, **never** on the locked one. The race is staggeringly rare — about **5 in 7
billion** runs — which is the whole point: a bug that testing would almost never surface, that a sequential proof
cannot see at all, is exactly the gap the rung closes. The inverse of [the buffer](#locks--the-monitor-invariant),
where the thread-local proof *does* compose; see [`CONCURRENCY.md`](../CONCURRENCY.md).

**"But I used an atomic class."** The reflex fix is to make `count` an `AtomicInteger` — and it *doesn't help*, not because
the type is at fault but because *using it naively* — `if (count.get() < 1) count.incrementAndGet()` — still composes
**two** atomic operations with a gap between them, so two threads can both read 0 and both increment. `AtomicBoundedCounter` is exactly this, and `AtomicBoundedCounterJCStress`
observes `count == 2` — but with a counter-intuitive sting in the tail: it races **far more readily** than the plain-`int`
version, not less. Measured here, the atomic check-then-act hits 2 in **~5–6% of samples** (millions of observations),
where the plain-`int` race is about **5 in 7 billion**. Two barriered atomic operations open a much wider interleaving
window than a single volatile read-then-write, so the *more* atomic-looking code is *more* exposed — the "I used an
atomic, so I'm safe" instinct gets it exactly backwards. The real fix is a single `compareAndSet` (its `casIncrement`),
one atomic transition, which is `FORBIDDEN` from reaching 2. On the verifier side, the atomic is **modelled as a wrapped
int** — `count.get()` reads a cell, `count.incrementAndGet()` / `set` / `addAndGet` / `compareAndSet` write it — so the
*sequential* `@Invariant({ count.get() <= 1 })` is **proved** for the check-then-act exactly as the plain-`int` version
is (and refutes at `<= 0`), atomicity being rung-1-transparent. `AtomicBoundedCounter` itself carries no annotation only
because its `casIncrement` retry-loop is outside the straight-line fragment; the verifiable half of the same shape is
pinned by the `P-check-then-act` cases and `SpscBufferVerifyTest`. So the atomic counter, like the plain one, is proved
sequentially safe and shown concurrently broken — the rung-1 boundary, twice.

### Seqlock — snapshot consistency by a parity protocol

Where the check-then-act counter's rung-1 proof is a *transparent* bounds check — the verifier proves the identical
`@Invariant` for the broken and the fixed version — the **seqlock** is the example where rung 1 has *characteristic,
non-transparent* work: a small two-state protocol the sequential checker is uniquely good at, that **discriminates the
correct shape from the broken one**. A `SeqLock` protects two fields `x`, `y` that are one logical record (always
`x == y`) behind a sequence counter whose *parity* is the protocol — **even = unlocked / consistent, odd = a write in
progress** — and that is exactly an *implication-guarded* class invariant:

<!-- doclint:ignore README illustration: SeqLock parity protocol (faithful excerpt of SeqLock.groovy) -->
```groovy
@Invariant({ seq % 2 == 0 ==> x == y })          // unlocked (even) ⟹ the record is consistent
void write(int v) {
    seq = seq + 1      // odd: write in progress — the invariant's guard is now false, x/y may diverge
    VarHandle.releaseFence()   // JMM: the lock is taken before any half of the record moves
    x = v
    y = v
    seq = seq + 1      // even: publish — x == y restored, the guarded invariant holds again
}
```

The `releaseFence` (and the `acquireFence` in `tryRead`, before it re-samples `seq`) is the **memory-model** half, and
rung 1 cannot see it — a fence has no sequential semantics, so the verifier treats it as a no-op and this body proves
exactly as it would without it. It is there because **jcstress caught its absence** as a real torn read; the story is
in [`CONCURRENCY.md`](../CONCURRENCY.md#seqlock--the-torn-read-where-all-three-rungs-share-the-work).

The odd state is a *token that licenses breaking* `x == y`: the verifier proves `write` restores the relation before it
republishes (drops `seq` back to even), and that a successful reader — `tryRead`, whose guard `s1 == s2 && s1 % 2 == 0`
held — returns a consistent snapshot, because under that guard the entry invariant yields `x == y` so
`result[0] == result[1]`. Both halves have teeth (`SeqLockVerifyTest`): a writer that republishes **without** restoring
consistency refutes —

```
Cannot prove class invariant — counterexample: seq = 0, x = 7, y = 5   (republished torn)
```

— and a reader that drops the parity check (`if (s1 == s2)`, forgetting `s1 % 2 == 0`) refutes its
consistent-snapshot `@Ensures`, because it can hand back a snapshot taken while a write was in progress (`seq` odd),
where `x` and `y` need not agree.

**The fragment, honestly.** A real reader *spins* until the guard passes, and a spin loop has no well-founded measure,
so it is outside the straight-line fragment (like the [atomic counter's CAS loop](#check-then-act--a-verified-invariant-that-concurrency-breaks)).
The verified unit is therefore the single-attempt `tryRead` (snapshot or `null` = "retry") and the **spin is lifted to
the caller** — which is also how the runtime rungs use it (their actors loop on `tryRead`).

**What this is, and isn't.** We prove the parity protocol — the writer re-establishes consistency, a validated read
sees it — *above* the memory model. That a torn read is genuinely impossible on real bytecode across real schedules is
the structural half: **Lincheck** model-checks it (the validating read is linearizable; the unguarded read is caught)
and **jcstress** observes the torn `(1, 0)` / `(0, 1)` empirically on the leaky reader and never on the validating one
(`./gradlew lincheckTest jcstressCheck`). That "never" is *earned*, not assumed — jcstress once observed it on the
validating reader too, because the fences above were missing, and neither rung 1 nor Lincheck (whose model-check is
sequentially consistent) can see a reordering. It is the sharpest illustration in the repo of why the rungs don't
subsume each other. There is **no Fray** rung: a seqlock is lock-free, so there is no lock graph
to deadlock. The full three-rung writeup is in [`CONCURRENCY.md`](../CONCURRENCY.md#seqlock--the-torn-read-where-all-three-rungs-share-the-work).

### Agents & actors — the same invariant, a different paradigm

The lock trick isn't really about locks; it's "prove the local obligation, assume the structural guarantee."
An **Agent** or **Actor** is a monitor whose mutual exclusion comes not from a lock but from processing **one
message at a time** — so the class `@Invariant` is again the monitor invariant, and each handler is verified to
preserve it, with **no lock annotation at all**:

<!-- doclint:ignore README illustration: Agent buffer occupancy invariant -->
```groovy
@Invariant({ 0 <= count && count <= capacity })   // the invariant the Agent maintains
class Buffer {
    int count, capacity
    @Requires({ count < capacity })
    @Ensures({ count == old.count + 1 })
    void add()    { count = count + 1 }
    @Requires({ count > 0 })
    @Ensures({ count == old.count - 1 })
    void remove() { count = count - 1 }
}
```

Wrap it in an `Agent` and send it method calls — or update closures, `agent.send { inc(it) }`, where the update
function is likewise proven to preserve the invariant — and the runtime serializes them, so
`0 <= count <= capacity` holds under concurrent producers and consumers **without `@Synchronized` or any
lock**. The proof is identical to the lock-guarded `Account` above; only the *assumed* structural guarantee
changes — mutual exclusion → serialization. That's the point: the same local invariant proof carries across
**shared-memory locking *and* message-passing actors**. Drop the `count < capacity` guard and it refutes, lock
or no lock. (We still don't prove the runtime *is* serial — that's the agent's contract, the half we rely on.)

### Dataflow — the determinacy half via single-assignment

Locks and actors both assume *mutual exclusion / serialization*. A **dataflow** network assumes something
different: **single-assignment**. Every `DataflowVariable` is bound exactly once, and a read blocks until that
bind happens — so the network's *value* is independent of the order the concurrent tasks actually run. That's
the structural half we assume; the functional half — *what* value comes out — we prove:

<!-- doclint:ignore README illustration: GPars dataflow sum -->
```groovy
@Ensures({ result == a + b })
static int dataflowSum(int a, int b) {
    def x = new DataflowVariable<Integer>()
    def y = new DataflowVariable<Integer>()
    def z = new DataflowVariable<Integer>()
    async { x << a }                    // each variable bound once...
    async { y << b }
    async { z << x.get() + y.get() }    // ...reads block until the bind, so order can't change the value
    return z.get()
}
```

Because single-assignment makes the result order-independent, the verifier desugars the whole network into
straight-line **SSA**: `new DataflowVariable()` drops out, `x << v` is the single binding `x = v`, and
`x.get()` (or `await(x)`) is just `x`. The `async {}` blocks flatten inline — sound *precisely because*
single-assignment makes the schedule irrelevant. The functional value `a + b` then proves sequentially, and a
wrong claim (`result == a`) still refutes with a counterexample. As with locks and actors, we assume the
structural guarantee (here, that each variable really is bound once) and prove no deadlock-freedom or
termination for *dataflow* networks — only the value the network computes, given that it computes one.
(*Channel* networks are different since Phase 243: their deadlock-freedom is checked — see below.)

> [!NOTE]
> **The straight-line form the verifier actually sees.** That desugaring isn't pseudocode — the whole concurrent
> network above collapses to three assignments, and *that* is what the SMT backend reasons about:
>
> ```groovy
> int dataflowSum(int a, int b) {   // @Ensures({ result == a + b })
>     x = a            // `x << a`                  — the single binding (new DataflowVariable() drops out)
>     y = b            // `y << b`
>     z = x + y        // `z << x.get() + y.get()`  — `.get()` is just the bound value; the async{} blocks flattened
>     return z         // `z.get()`
> }
> ```
>
> `a + b` then proves by ordinary sequential reasoning — sound *precisely because* single-assignment makes every
> schedule produce this same body. (The `Channels` example below is the same trick over a pipeline: `src.send(x)`
> becomes `src = x`, each `map { f }` becomes `f` applied to the upstream value, so the network collapses to the
> composition `(x + 1) * 2`.)

### Channels — the per-element transform via FIFO

Go-style **channels** (`AsyncChannel`) carry the same trick into streaming pipelines. A channel's structural
guarantee is **FIFO delivery**: the i-th value received is the i-th value sent, run through the pipeline's pure
stages. So for a representative element the whole pipeline collapses to *function composition* — exactly the
combiner trick — and we prove the per-element transform:

<!-- doclint:ignore README illustration: async channel pipeline -->
```groovy
@Ensures({ result == (x + 1) * 2 })
static int pipe(int x) {
    def src = AsyncChannel.<Integer>create(1)
    def out = src.map { it + 1 }.map { it * 2 }   // each map stage is a pure transform...
    async { src.send(x); src.close() }            // ...FIFO: out's i-th element is the transform of src's i-th
    return out.first()
}
```

The verifier desugars the pipeline to that composition: `src.send(x)` is the single binding `src = x`, each
`map { f }` is `f` applied to the upstream value, and receiving one element (`first()`) is a read. (Pipeline
stages resolve lazily at the receive site, so a producer in a trailing `async {}` still binds the post-send
value.) The functional transform `(x + 1) * 2` proves; claim `result == x + 1` instead and it refutes with a
counterexample. As everywhere in this section, FIFO delivery is the assumed half — we prove *what each element
becomes*, not that the channel delivers or terminates.

### Channel-end linearity — one process per end (Phase 241)

The per-element proof above has its own side condition, and Phase 241 makes it real (slice 2 of the SEQ/PAR
ladder, the channel sibling of [the Phase 240 fork-window check](#par-disjointness--the-fork-window-interference-check-phase-240)):
a point-to-point channel has **one live process per end**. Two concurrent senders interleave
nondeterministically; two concurrent receivers split the stream (each element is delivered to exactly one).
Before this phase the scalar rewrite quietly *proved* scheduler-dependent values on both shapes — racing
senders proved the flatten order:

<!-- doclint:case p241-channel-linearity/two-concurrent-senders-race-the-element-order -->
```groovy
@Ensures({ result == 2 })
static int race() {
    AsyncChannel<Integer> src = AsyncChannel.create(2)
    async { src.send(1) }
    async { src.send(2) }
    return src.first()
}
```

> Channel linearity violation in 'race': two concurrent senders on 'src' — the async tasks forked at lines 5
> and 6 both use its send-end, so the element order is a race…

Conflicts are judged over the same fork-join windows as Phase 240, so *sequential* uses by two processes
stay legal, and the errors cover the whole discipline: send/send, receive/receive, a send into a
**pipeline-derived** channel (its upstream stage owns that end), and — for broadcasts — a `subscribe()`
while a sender is live (a late subscriber may miss elements). Errors, not skips: each is a race in the code.

Distinct from those races is the model's own capacity: the scalar rewrite carries **one in-flight element
per channel** — one send, one consumer (a receive or a pipeline stage). Sequential over-use is fine code the
model can't follow (two sends then `first()` would prove last-write-wins where the runtime is FIFO-first —
which is exactly what it *did* prove before this phase), so it now **skips loudly** with the channel named,
and the desugar refuses the rewrite so nothing downstream can prove a FIFO-false value.

**`BroadcastChannel` is the sanctioned one-to-many form, and it now proves.** Broadcast delivery means every
subscriber sees every element, so `subscribe()` is the identity stage for the representative element — and
legal fan-out verifies end-to-end:

<!-- doclint:case p241-channel-linearity/broadcast-fan-out-every-subscriber-sees-the-element -->
```groovy
@Ensures({ result == x + x })
static int fanOut(int x) {
    BroadcastChannel<Integer> b = BroadcastChannel.create()
    AsyncChannel<Integer> s1 = b.subscribe()
    AsyncChannel<Integer> s2 = b.subscribe()
    async { b.send(x); b.close() }
    int r1 = s1.first()
    int r2 = s2.first()
    return r1 + r2
}
```

Both subscribers read the broadcast element, `x + x` proves; a subscriber channel is an ordinary channel, so
it can feed a `map` pipeline and the composition proves too. The point-to-point fan-out alternative — each
producer owning its **own** channel — also stays green, pinning that the linearity rules are per-channel, not
per-method. Honest boundaries: uses are recognised at a direct channel-variable receiver (`send`/`close`,
`first`/`receive`, the pipeline ops, `subscribe`); `merge`/`tap` argument-side ends and channel iteration are
not yet tracked, and those shapes already fall outside the value model. Delivery and termination remain the
assumed structural half, as everywhere in this section.

### Channel contracts — the element type is the protocol invariant (Phase 242)

With the ends disciplined, the next rung is *what flows through them* (slice 3 of the SEQ/PAR ladder): a
channel's element type may carry Bean Validation bounds — `AsyncChannel<@PositiveOrZero Integer>` — and that
type IS the channel's contract, the monitor-invariant reduction transplanted to channels. The invariant is
**checked at each send** (an assert at the send site, refuting with a counterexample) and **assumed at each
receive from an opaque channel** — a channel-typed *parameter*, whose producer lives in another method and is
checked by its own compilation. Producer and consumer verify **separately against the type**, with no
whole-network analysis — the compositional rule in its simplest form:

<!-- doclint:case p242-channel-contracts/producer-and-consumer-compose-through-the-channel-type -->
```groovy
class C {
    static void produce(AsyncChannel<@PositiveOrZero Integer> ch, int x) {
        ch.send(x * x)
    }
    @Ensures({ result >= 0 })
    static int consume(@NotNull AsyncChannel<@PositiveOrZero Integer> ch) {
        int v = ch.first()
        return v
    }
}
```

`produce` discharges `x * x >= 0` at its send; `consume` binds its receive to a fresh value carrying the
bound, and `result >= 0` proves from the channel type alone. A send that can violate the bound
(`ch.send(x - 1)` on a `@Min(0)` channel, `ch.send(7)` on a `@Max(6)`) refutes with a counterexample; a
two-sided `@Min(1) @Max(6)` "die" contract flows whole to the receiver; the awaited `await ch.receive()`
spelling binds the same way. And the honesty case: an **unconstrained** channel has no contract to assume, so
the same consumer postcondition *refutes* — the channel may deliver any value — rather than skipping.
(`@NotNull` on the handle discharges the ordinary null-deref obligation; the handle's nullity is separate
from the element contract.) Local pipeline channels get the identical send assert inside the Phase 119
rewrite, so a `@Requires`-guarded producer proves and an unguarded one refutes.

Two model repairs shipped with this: the channel rewrite is now **single-assignment** (the send *declares*
the representative element; the old `def src = 0` placeholder is gone), which keeps whole pipelines — asserts
included — inside the value-flow fragment, and closes a quiet hole: a **never-sent** channel read previously
*proved* `result == 0`, the placeholder's value, where the runtime blocks forever; it now proves nothing.
And a channel receive is exempt from the collection non-empty obligation (`first()` on a channel *blocks* —
delivery is the assumed structural half; it never throws on "empty").

Honest boundaries: int/long elements with numeric bounds (`@Positive`/`@PositiveOrZero`/`@Negative`/
`@NegativeOrZero`/`@Min`/`@Max`; `@NotNull` is a no-op there) — any other jakarta constraint on a channel
element **skips loudly**, neither checked nor assumed. Receives bind at a local assignment
(`int v = ch.first()`); sends are checked at statement position. A bare `ch.receive()` without an await is an
`Awaitable`, not a value, and does not bind. Delivery and termination remain rungs 2/3.

### Network well-formedness — deadlock-freedom as well-foundedness (Phase 243)

Slice 4 closes the structural claim the section kept disclaiming — for the fragment where it can actually be
*exact*. In the one-element model a method's channel network is a tiny wait-for system: the **blocking**
operations are receives (`first()`, awaited `receive()`) and joins (`await t`) — a statement-position send
discards its `Awaitable` and does not block. A blocking read completes only after its root channel's send has
executed; an op runs only after its process passes its earlier blocking points (an arm's ops additionally
need main to reach the fork); a join completes only when the whole arm has. **The network is deadlock-free
exactly when that wait-for order is well-founded** — the same argument as `@Decreases` and the
dining-philosophers resource hierarchy, in its fourth appearance. So a cycle is not a "can't certify": it is
a **guaranteed deadlock**, and the checker spells it out:

<!-- doclint:case p243-network-well-formedness/awaiting-the-consumer-before-the-send -->
```groovy
static int joinWait() {
    AsyncChannel<Integer> src = AsyncChannel.create(1)
    def t = async { src.first() }
    await t
    src.send(1)
    return 0
}
```

> Process-network deadlock in 'joinWait': circular wait: the receive on 'src' (line 3, in the task forked at
> line 3), which waits for the send on 'src' (line 5), which waits for the await of the task forked at
> line 3, which waits for the first…

The other refuted shapes: a receive before the only send **in the same process**; a receive before the
producer task is even **forked**; two tasks in a **mutual receive cycle** (each reads from the other before
writing); and a receive whose root channel — directly or through a pipeline derivation — is **never sent to**
("can never be satisfied", the precise name for what Phase 242's never-sent repair could only refute). The
well-ordered twin verifies end to end — send the request (non-blocking), fork the replier, then block:

<!-- doclint:case p243-network-well-formedness/request-reply-in-the-right-order-proves -->
```groovy
@Ensures({ result == x + 1 })
static int reqReply(int x) {
    AsyncChannel<Integer> q = AsyncChannel.create(1)
    AsyncChannel<Integer> r = AsyncChannel.create(1)
    q.send(x)
    async { int v = q.first(); r.send(v + 1) }
    return r.first()
}
```

The certificate covers exactly what it says, loudly at the edges: a **conditional** channel op (inside an
if/loop/catch) makes the network uncertifiable — loud skip, no claim either way; an **escaping** channel (a
call argument, a return, an alias) and a channel-typed **parameter** may be served elsewhere, so they carry
no local claim — the modular assumption, same as Phase 242's receives. The check runs only when the Phase 241
linearity pass is silent (its findings already re-shape the network's meaning). What remains at rungs 2/3:
per-task termination, conditional/multi-element networks, and the scheduler itself.

### Drain discipline — iteration blocks until close (Phase 245)

The last slice of the SEQ/PAR ladder closes the termination story's drain side. `for (v in ch)` and the
drain ops (`toList()`, `each {}`, `collect {}`) are **whole-stream receives**: they block until the channel
is *closed*, not until an element arrives — a new dependency family in the Phase 243 wait-for graph. An
iteration completes only when its root channel's `close()` executes, so the classic forgotten-close hang is
now a named compile error, and a close *behind* the iteration is a circular wait like any other. The
well-ordered shape is certified silently:

<!-- doclint:case p245-channel-drain/iterate-with-a-closing-producer-finishes -->
```groovy
static int drain() {
    AsyncChannel<Integer> src = AsyncChannel.create(4)
    src.send(1)
    src.close()
    async {
        int total = 0
        for (v in src) {
            total = total + v
        }
    }
    return 0
}
```

Drop the `close()` and the checker names the hang — *"the iteration over 'src' can never finish — no
close() on 'src' anywhere in the method"*; put the close *after* the iteration in the same process, or in a
task forked only after main has blocked at the loop, and the circular wait is spelled out as a
Process-network deadlock. A **conditional** close is uncertifiable (loud skip), and two concurrent iterators
trip the Phase 241 receiver rule unchanged — an iteration is a receive-end use like any other.

Two honest boundaries shipped with it. The **value** of drained traffic stays unmodelled: the scalar
rewrite's guard now also refuses loops and drain ops outright, pinned by a loop-producer case whose
FIFO-false claim *skips loudly* instead of proving. And locally-constructed channels (`create()`,
`subscribe()`, pipeline stages) are recognised as factory results — never null, so the raw un-rewritten
calls in drain shapes carry no spurious deref obligations, while a channel *parameter* keeps its honest
`@NotNull` discharge. Together with Phase 243 this completes the ladder's termination claim: **in a clean
one-shot network every blocking operation — read, iteration, join — provably completes**, with per-task
loop termination (`@Decreases`) and the scheduler itself remaining rungs 2/3.

### Bounded FIFO traffic — the k-th send is the k-th receive (Phase 247)

The ladder's first rung *past* the one-shot fragment. Phases 119–246 carried **one in-flight element** per
channel and refused everything else; the Kerridge gallery's literal two-message `ProduceHW` was its named
boundary. Phase 247 widens the channel model to a **bounded FIFO**: the *k*-th send on a channel declares
its *k*-th element, the *k*-th receive on a stream reads it, a `map {}` stage transforms whichever element
flows through, and every broadcast subscriber has its own cursor over the same sequence. The pairing is
*exact* — FIFO delivery is the channel's contract — whenever one process owns each end and every
operation is one-shot, which is precisely what the guard admits. Multi-message exchanges now prove
FIFO-**true** values (and last-write-wins is refuted, with a counterexample):

<!-- doclint:case p247-bounded-fifo/two-receives-read-the-two-elements-in-order -->
```groovy
@Ensures({ result == 10 * x + y })
static int twoReceives(int x, int y) {
    AsyncChannel<Integer> src = AsyncChannel.create(2)
    async { src.send(x); src.send(y); src.close() }
    int a = src.first()
    int b = src.first()
    return 10 * a + b
}
```

Drains yield the sequence itself — the "drained values" boundary Phase 245 recorded. `toList()` and
`collect {}` become the element list; `for (v in ch)` **unrolls** over the known sequence, the body copied
once per element with its locals renamed apart — so an accumulating drain proves its sum with no loop
invariant at all (exact for a closed, bounded stream; the drain's *blocking* until `close()` is still
certified separately, by Phase 245 on the original body):

<!-- doclint:case p247-bounded-fifo/an-accumulating-for-in-drain-proves-its-sum -->
```groovy
@Ensures({ result == x + y + z })
static int total(int x, int y, int z) {
    AsyncChannel<Integer> src = AsyncChannel.create(4)
    async { src.send(x); src.send(y); src.send(z); src.close() }
    int sum = 0
    for (v in src) {
        int d = v
        sum = sum + d
    }
    return sum
}
```

The wait-for graph pairs the same way: the *j*-th receive on a stream waits for the *j*-th send on its
root, so a receive past the last send is no longer "beyond the model" but a named deadlock — *"the 2nd
receive on 'src' can never be satisfied — only 1 send on 'src' anywhere in the method"* — and a two-round
request–reply (two requests queued, the server answering each in turn) is certified deadlock-free *and*
proves both replies. What stays outside is still loud, now with the reason: a **conditional** send or
receive (inside an `if` / loop / catch / non-async closure), an end used by **two processes**, **two
consumer families** on one channel (direct receives *and* a derived stage), a drain through a
count-changing stage (`filter` / `split` / `merge` / `tap`), or an `each {}` drain (an accumulating `each`
carries no invariant — use `for (v in ch)` or `toList()`). The counts are *static*: a producer **loop** is
still the streaming frontier.

### Bounded streaming — literal-bounded channel loops unroll (Phase 248)

A loop that carries channel traffic is "not one-shot" to the ladder: its operations are conditional to the
structural walk and beyond the bounded FIFO. When the loop's bound is a **literal** — `for (i in 0..<3)`,
`for (i in 1..3)`, `for (int i = 0; i < 3; i++)`, nested — the trip count is static, and Phase 248 unrolls
it *before* the structural walk: the body is copied per iteration with the index frozen to its constant and
the body's locals renamed apart (async arms are rebuilt, never mutated — their nodes are shared with the
live AST). The stream becomes straight-line traffic that every later pass certifies exactly — the sends
indexed, the receives paired, the drains unrolled, the wait-for order well-founded. The book's first
plugAndPlay network, generator → squares → drain, proves its sum and is certified deadlock-free:

<!-- doclint:case p248-bounded-streaming/generator-squares-drain-the-pipeline-sum-proves -->
```groovy
@Ensures({ result == 5 })
static int pipeline() {
    AsyncChannel<Integer> nums = AsyncChannel.create(4)
    AsyncChannel<Integer> squares = nums.map { it * it }
    async {
        for (i in 0..<3) {
            nums.send(i)
        }
        nums.close()
    }
    int sum = 0
    for (v in squares) {
        sum = sum + v
    }
    return sum
}
```

A consumer loop unrolls the same way (`for (i in 0..<2) acc = 10 * acc + src.first()` reads the two
elements in order), and a producer loop of two against a consumer loop of three is the FIFO pairing's named
deadlock — *"the 3rd receive on 'src' can never be satisfied — only 2 sends"*. This is bounded model
checking in the compiler, and says so: literal bounds only, up to 32 iterations; a **symbolic** bound
(`for (i in 0..<n)`) stays a loop and skips loudly — the streaming frontier proper, where the send/receive
count would have to be carried by a loop invariant rather than counted.

### ALT — `ChannelSelect` as a nondeterministic choice among the ready branches (Phase 249)

occam's `ALT` (JCSP's `Alternative`) is the construct the gallery had left as future work. In
`groovy.concurrent` it is `ChannelSelect`: `await ChannelSelect.from(a, b).select()` blocks until *some*
branch has an element and returns which (`index`) and what (`value`). Phase 249 models the one-shot form on
both sides of the ladder. On the **value** side the choice is nondeterministic — `r.index` binds to one of
the branches that can be ready, `r.value` to that branch's head element, the two exactly correlated (an
if-then-else chain over the index), so a spec must hold for *every* possibly-ready branch, and a branch-wise
claim proves:

<!-- doclint:case p249-alt-select/index-and-value-are-correlated-a-branch-wise-claim-proves -->
```groovy
@Ensures({ result == x + 1 || result == y - 1 })
static int branchwise(int x, int y) {
    AsyncChannel<Integer> a = AsyncChannel.create(1)
    AsyncChannel<Integer> b = AsyncChannel.create(1)
    async { a.send(x); a.close() }
    async { b.send(y); b.close() }
    ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
    int v = (int) r.value
    if (r.index == 0) {
        return v + 1
    }
    return v - 1
}
```

"Can be ready" is decided *exactly*, by the same mechanism that now linearises the whole value model: the
flattened statements are no longer emitted in textual order but **scheduled by dataflow** — a process's next
statement runs once the channel elements it reads have been declared, an arm once main has passed its fork —
and an ALT runs only when nothing else can, over the branches whose element got defined by then. A branch
that can only be served *after* the ALT's process moves on is never the one taken, so in the shape below the
ALT provably takes `b` (`result == 2`, not merely `1 || 2`) — and, as a side effect, the CSP habit of listing
the reader before the writer now proves too (a consumer task textually ahead of its producer).

On the **structural** side the ALT is an OR node in the wait-for graph: it proceeds on *any* ready branch.
Well-foundedness becomes a **completion fixpoint** — an event completes once everything it waits for has,
an ALT additionally once any alternative has — which is exactly acyclicity when there is no ALT, and with one
makes a cycle a deadlock only if *every* branch is stuck:

<!-- doclint:case p249-alt-select/an-alt-with-one-free-branch-is-certified-and-takes-it -->
```groovy
@Ensures({ result == 2 })
static int freeBranch() {
    AsyncChannel<Integer> a = AsyncChannel.create(1)
    AsyncChannel<Integer> b = AsyncChannel.create(1)
    AsyncChannel<Integer> c = AsyncChannel.create(1)
    async { int v = c.first(); a.send(v) }
    async { b.send(2) }
    ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
    c.send(1)
    int v = (int) r.value
    return v
}
```

Remove the second task and every branch of the ALT waits on main passing it: *"circular wait: the ALT over
'a', 'b' … which waits for the send on 'a' … which waits for the receive on 'c' … which waits for the send on
'c' …"*. An ALT no branch of which is ever sent to "can never be satisfied — no send left on any of its
channels". The one-shot discipline is loud: a receive *after* an ALT on one of its channels (whether the ALT
consumed the element depends on its choice), two ALTs over one channel, a `ChannelSelect` held in a variable,
or a result used beyond `.index` / `.value` all skip with the channel and the reason named. The looping
multiplexer — `while (true) { alt.select() … }` — is the streaming frontier again.

### Streaming termination — a loop send never blocks (Phase 250)

The structural half of the streaming frontier, taken on its own. Phases 243/245 voided the network
certificate for *any* channel operation inside a loop or `if`; but a **send never blocks** — it stalls
nobody — so a conditional send only makes its channel's element *count* non-static. Phase 250 drops it from
the wait-for graph and remembers the root: an **iteration** (`for (v in ch)`, `toList()`), which waits for
the *close*, not for a count, is unaffected — so the book's generator as the book means it, `GNumbers(n)`
with symbolic `n`, feeding `GPrint`, is certified to terminate for every `n`, deadlock-freedom included:

<!-- doclint:case p250-streaming-termination/a-symbolic-producer-loop-with-a-close-certifies-its-drain -->
```groovy
static int numbersToPrint(int n) {
    AsyncChannel<Integer> out = AsyncChannel.create(4)
    async {
        for (i in 0..<n) {
            out.send(i)
        }
        out.close()
    }
    int seen = 0
    for (v in out) {
        seen = seen + 1
    }
    return seen
}
```

The forgotten close is still the named hang, a close *inside* the loop is still conditional (uncertifiable),
and a blocking `first()` on a channel whose count is not static — `n` may be zero — is a named skip rather
than a silent pass or a spurious "no send" error: *"the receive on 'out' is served by a send inside a loop —
the element count is not static, so the receive cannot be paired with a send"* (an ALT branch on such a
channel likewise). What this certificate does **not** say is anything about the drained *values*: the value
model still refuses loop traffic loudly (`Skipped channel verification … not one-shot`), and carrying the
count symbolically — the channel as a sequence the producer's loop invariant describes — is the value half
of the frontier, now the only half left.

### Symbolic streaming — the channel as the sequence its producer loop builds (Phase 251)

The value half of the streaming frontier, and the last rung of the ladder's second run. A channel whose
*only* send is the send statement of a unit-counter loop carrying `@Invariant` / `@Decreases` is modelled as
the **list that loop builds**: `send` appends, a `map {}` stage appends its transform in lockstep, `toList()`
reads the list, `close()` is the marker drains are scheduled behind. The sequence facts are **injected into
the loop's spec** — `size == counter − entry` and, when the sent expression is a function of the counter and
loop constants, the *k*-th element's value — so the user writes only the generator loop's own invariant and
never names the shadow list. `GNumbers(n)` as the book means it, with `n` a parameter, proves its drained
list element by element, through `GSquares`:

<!-- doclint:case p251-symbolic-streaming/gnumbers-n-gsquares-drained-the-k-th-element-is-k-squared -->
```groovy
@Requires({ n >= 0 })
@Ensures({ result.size() == n && Forall.range(0, result.size(), { int k -> result[k] == k * k }) })
static List<Integer> squares(int n) {
    AsyncChannel<Integer> nums = AsyncChannel.create(4)
    AsyncChannel<Integer> sq = nums.map { it * it }
    async {
        int i = 0
        @Invariant({ 0 <= i && i <= n })
        @Decreases({ n - i })
        while (i < n) {
            nums.send(i)
            i = i + 1
        }
        nums.close()
    }
    return sq.toList()
}
```

Everything else is the loop engine's own proof, unchanged: the user's invariant carries the counter's bounds,
the loop VCs verify the body — the send-side channel contract included, so `AsyncChannel<@PositiveOrZero
Integer>` with `send(i - 1)` refutes at the first iteration — and the drained list's claims follow (a wrong
size refutes; a parameter start `int i = lo` proves `n − lo`; a C-style producer in the body works the same).
Two details earned their comments: a loop's spec inside an `async {}` arm is now captured at CONVERSION (the
flattening puts the arm's loop at the body's top level), and the injected text never spells `(entry) + k` —
Groovy parses a parenthesised bare identifier before an operand as a *cast*.

The boundaries, loud and named: a one-at-a-time `first()` on a streaming channel ("drain it instead"), a
producer loop without a spec, a second send, a non-unit counter or a range `for`-in (the model rides a
`while` / C-style unit-counter loop), a non-int element type — and the accumulating `for (v in ch)` drain of
a stream, which is the loop engine's own "a loop after a list-building loop" skip: `toList()` is the
drained-value spelling. What the ladder has *not* modelled remains the looping consumer proper — the ALT
multiplexer, the fair server — where the count is not the whole story.

### Streaming consumers — the looping process (Phase 252)

The rung the gallery named last: the **looping consumer**. A specified unit-counter loop that receives once
per iteration from a streaming channel reads element *k* of the shadow list (`x.first()` → `x$q[i − a]`),
with the **block-forever obligation** asserted before it — the element it reads must exist — and the producer
loop's invariants, sequence facts and `¬guard` injected into the consumer's spec as *frame facts* (nothing in
the consumer writes the producer's counter or its list). A loop that both receives and sends is a **stage as
a process**: its sent expression's element relation goes through the receive. So the book's network as the
book writes it — a `PAR` of three looping processes, `GSquares` receiving and sending — proves the printed
list element by element, for symbolic `n`, each process carrying only its own `@Invariant` / `@Decreases`:

<!-- doclint:case p252-streaming-consumers/gnumbers-gsquares-gprint-as-three-looping-processes -->
```groovy
@Requires({ n >= 0 })
@Ensures({ result.size() == n && Forall.range(0, result.size(), { int k -> result[k] == k * k }) })
static List<Integer> network(int n) {
    AsyncChannel<Integer> nums = AsyncChannel.create(4)
    AsyncChannel<Integer> sq = AsyncChannel.create(4)
    async {
        int i = 0
        @Invariant({ 0 <= i && i <= n })
        @Decreases({ n - i })
        while (i < n) {
            nums.send(i)
            i = i + 1
        }
        nums.close()
    }
    async {
        int i = 0
        @Invariant({ 0 <= i && i <= n })
        @Decreases({ n - i })
        while (i < n) {
            int v = nums.first()
            sq.send(v * v)
            i = i + 1
        }
        sq.close()
    }
    List<Integer> printed = []
    int j = 0
    @Invariant({ printed != null && 0 <= j && j <= n && printed.size() == j && Forall.range(0, printed.size(), { int k -> printed[k] == k * k }) })
    @Decreases({ n - j })
    while (j < n) {
        int s = sq.first()
        printed.add(s)
        j = j + 1
    }
    return printed
}
```

Read one element more than the producer sends and the diagnostic is the runtime's hang, spelled: *"the
receive on 'out' (line N) may block forever — the element it reads may never be sent (the consumer loop
reads past what the producer loop sends)"*. Two enablers fell out. The loop engine can now summarise a loop
**after a list-building loop** (Phase 207's sequential loops had refused a predecessor that mutates a
collection: size and contents are havoc'd, then its invariant characterises the list), and **arm locals are
renamed apart** before the flattening — both loops naturally count with `i`, and the flattened
single-assignment model had conflated them since Phase 119. Loud boundary: a receive in a loop without a
spec or a unit counter, or twice per iteration on one channel, is named — as before, the counter is the
variable the guard tests. The ALT multiplexer as a *looping* process stays the frontier: its per-iteration
choice is the one-shot ALT's, but its readiness across iterations is not a count.

### The looping ALT — the multiplexer (Phase 253)

The last shape the gallery had left open. A specified unit-counter loop whose body takes one element per
iteration from whichever of its streaming inputs has one — `Result r = await ChannelSelect.from(a, b).select()`
— is the **multiplexer**. Readiness now changes per iteration, so the model gives each branch a **ghost
cursor** (`a$c`, `b$c`, declared before the loop): the choice ranges over the branches whose cursor is below
their list's size, the value is an element of the chosen branch at or beyond its cursor (Phase 256 — the runtime re-sends a
losing branch's element to the back of its queue, so within a contended branch the order of taking is not
FIFO), the chosen cursor steps, and the injected invariant `0 ≤ a$c ≤ |a| ∧ 0 ≤ b$c ≤ |b| ∧ a$c + b$c == i − a₀`
ties the cursors to the iterations. "No branch
has an element left" is the block-forever obligation, asserted before every choice:

<!-- doclint:case p253-looping-alt/the-multiplexer-merges-every-element-count-na-nb -->
```groovy
@Requires({ na >= 0 && nb >= 0 })
@Ensures({ result.size() == na + nb })
static List<Integer> merge(int na, int nb) {
    AsyncChannel<Integer> a = AsyncChannel.create(4)
    AsyncChannel<Integer> b = AsyncChannel.create(4)
    async {
        int i = 0
        @Invariant({ 0 <= i && i <= na })
        @Decreases({ na - i })
        while (i < na) {
            a.send(i)
            i = i + 1
        }
        a.close()
    }
    async {
        int i = 0
        @Invariant({ 0 <= i && i <= nb })
        @Decreases({ nb - i })
        while (i < nb) {
            b.send(i + 100)
            i = i + 1
        }
        b.close()
    }
    AsyncChannel<Integer> out = AsyncChannel.create(8)
    int j = 0
    @Invariant({ 0 <= j && j <= na + nb })
    @Decreases({ na + nb - j })
    while (j < na + nb) {
        ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
        int v = (int) r.value
        out.send(v)
        j = j + 1
    }
    out.close()
    return out.toList()
}
```

The merged count proves for symbolic `na`, `nb`; a forwarded element contract (`AsyncChannel<@PositiveOrZero
Integer> out`) proves *through* the choice, whichever branch it takes, and one an input violates is refuted;
one iteration too many is *"the ALT over 'a', 'b' (line N) may block forever — no branch may have an element
left"*. And the **order** claim `result[0] == 0` is refuted — honestly: the interleaving is nondeterministic,
and the model says exactly that (per-iteration nondeterminism, the ALT's own semantics, is what a merged
*order* would need a fairness assumption to sharpen). The `$channelSelect` marker terms now translate inside
loop bodies too, so the loop engine's VCs see the choice directly.

What remains after this rung is a different kind of boundary: the **non-terminating** process
(`while (true)`), whose properties are safety-per-iteration and *liveness under fairness* — not a count, and
not something a `@Decreases` can carry.

### Non-terminating processes — the safety half of `while (true)` (Phase 254)

The book's processes do not stop: `GNumbers` counts forever, `GPrint` prints forever, a server answers
forever. A `while (true)` loop with an `@Invariant` (no `@Decreases` — none is possible) is now certified for
**safety**: its invariant is preserved per iteration, its send-side channel contract is checked per
iteration, and what its consumers receive carries its element relation. Termination is not claimed, and the
one thing a consumer of an infinite stream cannot be *proved* by safety alone — that its next receive is
eventually served — is **assumed and said so**, as a network note: *"… is served by a non-terminating
producer — that it is eventually served is a liveness property, not certified here (…); the safety of the
values received is certified under that assumption"* (Phase 255, next, discharges that note wherever its
fairness argument applies — as it does here). The book's network, as the book writes it:

<!-- doclint:case p254-non-terminating-processes/gnumbers-gsquares-gprint-all-forever-safety-proved-liveness-certified-under-weak-fairness -->
```groovy
static void network() {
    AsyncChannel<Integer> nums = AsyncChannel.create(4)
    AsyncChannel<Integer> sq = AsyncChannel.create(4)
    async {
        int i = 0
        @Invariant({ i >= 0 })
        while (true) {
            nums.send(i)
            i = i + 1
        }
    }
    async {
        int i = 0
        @Invariant({ i >= 0 })
        while (true) {
            int v = nums.first()
            sq.send(v * v)
            i = i + 1
        }
    }
    List<Integer> printed = []
    int j = 0
    @Invariant({ printed != null && j >= 0 && printed.size() == j && Forall.range(0, printed.size(), { int k -> printed[k] == k * k }) })
    while (true) {
        int s = sq.first()
        printed.add(s)
        j = j + 1
    }
}
```

Every value `GPrint` accumulates is a square — `GPrint`'s own invariant, preserved through the two stages'
relations; make `GSquares` send `v * v + 1` and that invariant is refuted. The soundness point is the
**flattened model**: after a `while (true)` the loop engine's summary is `inv ∧ ¬true`, i.e. *false* — fine
for the method's own unreachable tail, unsound for the *other processes* the flattening places after the
loop. So in the rewrite an infinite loop gets a **free guard** (`loop$fuel > 0`, an unassigned name): the
process may be observed at any iteration boundary, and what follows is reasoned about under its invariant
alone — a false claim after an infinite producer is refuted, never vacuously proved (pinned). Two more facts
travel with it: a consumer's *read bound* (`counter − a ≤ in$q.size()`, so a stage's output count is bounded
by its input count without any exit fact), and the classic hang is still caught the other way round — an
**infinite consumer of a finite producer** "may block forever". The forever multiplexer forwards its output
contract through the choice as before.

What is left after this is the **liveness** half proper — eventual delivery, a server answering every
client, network-wide deadlock-freedom over infinite runs — which needs a fairness assumption about the
scheduler and about `ALT`, and a temporal argument the sequential fragment has no word for.

### Liveness under weak fairness — the lifted wait-for graph (Phase 255)

The last half. **Assumption:** *weak fairness* — a process whose next operation is enabled eventually
executes it. Under it, a looping network is live — every receive eventually served, every process making
progress forever or to its own end — exactly when no operation waits, *in every iteration*, on something that
transitively waits on itself in the same iteration. Lift the Phase 243 wait-for graph to the iteration
index: a receive of element *k* waits on the producer's iteration *k − pre* (*pre* = the producer's priming
sends before its loop), program order within an iteration has weight 0, the wrap to the previous iteration
weight −1. Every weight is ≤ 0, so a cycle of weight ≥ 0 — a deadlock — exists iff the **weight-0 subgraph
has a cycle**. That is the existing DFS, on a graph whose nodes are `(loop, operation)`:

<!-- doclint:case p255-liveness/a-forever-client-server-loop-is-live-the-request-precedes-the-wait-for-its-reply -->
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

The client's wait for reply *k* depends on the server's iteration *k*, which depends on request *k* — sent
*before* the wait, weight −1 through the wrap: live. Let the client wait before asking and the cycle closes
at weight 0 — *"circular wait in every iteration: the receive on 'reply' … which waits for the send on
'reply' … which waits for the receive on 'request' … which waits for the send on 'request' …, which waits
for the first — no message is ever ahead of this cycle (a priming send before one of the loops would break
it)"*. A three-process ring deadlocks bare and is live with one token sent before a loop; **priming sends**
now enter the stream model too (element *k* of the loop is list index *k + pre*, the priming element's
value carried by the invariant). A looping `ALT` is live when a branch is fed by a *pure generator* — a
producer loop with no receives of its own; over dependent branches only it is left undecided, loudly,
because that would need a fairness assumption about the ALT's *choice*, which is not made.

Where the analysis certifies, the Phase 254 "liveness not claimed" note is discharged: the book's forever
`GNumbers → GSquares → GPrint` now compiles clean — safety per iteration *and* liveness under weak
fairness, with termination alone unclaimed because none is meant. What the certificate rests on is stated
in one line: the scheduler is weakly fair, sends never block, and the base case is the pre-loop
straight-line code.

### Selection semantics — the runtime's ALT, modelled as it is (Phase 256)

The rung that was to be "fairness of the ALT's choice" turned into something more useful: reading what
`ChannelSelect.select()` actually does (Groovy 6.0.0-beta-3; bytecode-identical in beta-2). It issues a `receive()` on every branch and
completes with the first; when several are ready the **lowest index wins** (priority by list order), and a
losing branch's consumed element is **re-sent to the back of its queue** — no loss, but "may reorder values
within a channel". Fair selection is therefore not an assumption the checker can make; it models the runtime:

- A looping ALT takes **some remaining element** of the chosen branch (`$channelSelect.valueAny`): the count
  stays exact, element-wise contracts still forward, and positional claims through a contended branch do not
  prove — which is right, because the runtime does not deliver them.
- A branch behind one fed by an infinite pure generator is a named **selection starvation hazard**: the
  generator never blocks, so that branch is always ready, and the lowest ready index is always taken.
- A reply guarded by the choice — `if (r.index == i) { replyX.send(…) }`, the fair server's shape — leaves
  its client's liveness **withheld with the runtime's reason**: *"served only when the ALT … takes branch i —
  ChannelSelect prefers the lowest ready index, so whether this client is ever chosen depends on timing;
  per-client liveness is not certified (a fair selection would need runtime support)"*.

ALT-*loop* liveness itself needs no choice fairness at all: the weight-0 completion fixpoint of Phase 255
treats the ALT as an OR node (Phase 249's rule, per iteration), so a multiplexer over dependent stages is
certified live, and an ALT whose every branch waits on its own output is a circular wait in every iteration:

<!-- doclint:case p256-selection/an-alt-whose-branches-all-wait-on-its-own-output-circular-wait-in-every-iteration -->
```groovy
static void knot() {
    AsyncChannel<Integer> a = AsyncChannel.create(4)
    AsyncChannel<Integer> b = AsyncChannel.create(4)
    AsyncChannel<Integer> out = AsyncChannel.create(4)
    async {                                              // one stage feeds both branches from the ALT's own output
        int i = 0
        @Invariant({ i >= 0 })
        while (true) {
            int v = out.first()
            a.send(v)
            b.send(v)
            i = i + 1
        }
    }
    int j = 0
    @Invariant({ j >= 0 })
    while (true) {
        ChannelSelect.Result r = await ChannelSelect.from(a, b).select()
        int v = (int) r.value
        out.send(v)
        j = j + 1
    }
}
```

What this left was a **runtime frontier**, and it has since moved: GROOVY-12320 (Groovy 6.0.0-beta-4) makes
`select()` claim-based — exactly one branch dequeues, losers are untouched, a select over closed channels
fails fast — and adds `fair()` (rotating from the last winner, on a *held* instance) and `random()`. The
checker probes the runtime it runs on and models what it finds (Phase 257): under the claim-based select a
looping ALT takes the chosen branch's head again, a held instance is a supported shape, the starvation hazard
fires only where priority is in effect — including `fair()` on a *fresh* instance each iteration, which keeps
no rotation state — and the fair server with a held `fair()` has its per-client liveness *certified* under
weak fairness. Phase 258 then made the guarded replies *conditional streams* and the cycle itself a
rely/guarantee argument, so the fair server verifies whole and each client proves `r == i + 1` — the
request–reply law — with a wrong claim refuted; and Phase 259's `c.taken` (the elements a loop has taken
so far, a ghost its `@Invariant` can quantify over) lets a token ring prove its closed form, and Phase 260's
`c.sent` lets a producer whose values are loop-written — a counting server, a Fibonacci generator — state
its own stream law for its readers; Phase 261 admits a terminating member to the cycle, refuting the read
that would block forever past a partner's total, and Phase 262 verifies the cycle that ends cleanly — a
server draining its client's requests until the close, and Phase 263 adds the session-typed view — a
`@Protocol` global type on the method — with `par` interleaving independent sub-sessions, the fair
server's type — projected onto each role and checked against every process's control flow, and Phases 265/266's
`@ServedWithin(n)` / `@DeliveredWithin(n, from, to)` make "served within a bound" and the pipeline's
end-to-end head-of-line latency certified or refuted claims; Phase 267 admits the mixed choice and checks
its coherence — one opener certifies, a racing pair is refused — and since Phase 269 the protocol is a
Groovy closure, parsed by Groovy itself (see `examples/kerridge.md`). Before beta-4 the verdicts
above stand, and all of them were reproduced, not read: `repro/ChannelSelectRepro.groovy` run against 6.0.0-beta-3 shows index 0 winning
100/100 in either listing order, a losing branch delivering `[b2, b1]`, a thousand selects leaving a thousand
pending receivers on a quiet branch (and one later element bounced a thousand times), and a select over two
closed channels never completing.

### async/await — the value a task computes

The dataflow and channel examples above used `async { }` as plumbing. Groovy 6 also makes `async`/`await` a
first-class way to write concurrent code in a sequential style — and the same split applies in its purest form. A
**safe** async closure — one that returns a *pure value*, the discipline the async guide prescribes
(*"prefer returning values over mutating shared state"*) — is observationally just its value, driven to completion.
So `await` reads that value out, and the functional contract proves by ordinary sequential reasoning:

<!-- doclint:case p153-async-await/await-an-async-value-compute -->
```groovy
@Ensures({ result == (x + 1) * 2 })
static int compute(int x) {
    def fa = async { x + 1 }
    int a = await fa
    return a * 2
}
```

`async { e }` lowers to `AsyncSupport.async({ e })` and `await x` to `AsyncSupport.await(x)`; the verifier
recognises the pair and resolves `await fa` back to `fa`'s pure body `x + 1`, so `(x + 1) * 2` proves. The bug
[bmc4j](https://github.com/bmc4j/bmc4j)'s `computeBuggy` plants — an off-by-one *after* the await
(`return a * 2 + 1`) — refutes with a counterexample, and chained awaits thread the value through
(`int a = await async { x + 1 }; int b = await async { a + 1 }` gives `x + 2`).

Beyond chaining, **`Awaitable.all`** (and its multi-arg `await(a, b, c)` sugar) *gathers* independent tasks — and
because `all` waits for *every* task, the gathered result is order-independent, so the verifier models it as the
value **list** and folds element access:

<!-- doclint:case p153-async-await/gather-all-then-combine-await-all -->
```groovy
@Ensures({ result == 6 })
static int sumThree() {
    def r = await(async { 1 }, async { 2 }, async { 3 })
    return ((int) r[0]) + ((int) r[1]) + ((int) r[2])
}
```

A wrong total refutes. (The `def` and element casts are a surface wart — multi-arg `await` is typed `List<Object>` —
not a verifier limit.) `Awaitable.all` waits for everyone, so its result is fixed.

The **racing** combinators `Awaitable.any` / `Awaitable.first` instead return whichever task *wins* — but that's just
an **if/else over an unknown selector**: the result is one of the task values, so the verifier binds it to a
nondeterministic choice and proves the postcondition holds for *every possible winner*:

<!-- doclint:case p153-async-await/racing-any-verifies-when-the-spec-covers-every-winner -->
```groovy
@Ensures({ result == 1 || result == 2 })
static int race() {
    def x = await Awaitable.any(async { 1 }, async { 2 })
    return (int) x
}
```

Whichever task wins, the result is `1` or `2`, so the disjunction proves; tighten the spec to `result == 1` and it
**refutes** (the other task might win) — exactly how an if/else discharges all its branches. When the tasks compute
the *same* value, the race is determinate (`Awaitable.first(async { 42 }, async { 42 })` gives `42`), so no scheduler
assumption is even needed.

The **timing** combinators split the same way, on whether timing changes the *value*. `Awaitable.delay(ms)` is a
non-blocking pause — no value, no state effect — a **no-op** for a logic proof. `orTimeoutMillis` is **transparent**:
under the completion assumption (the deadline is the structural half we assume away, like mutual exclusion for locks)
`await(task.orTimeoutMillis(ms))` reads out the task's value. But its fallback sibling
`completeOnTimeoutMillis(task, fallback, ms)` returns the value *or* the fallback — genuinely nondeterministic — so it
**skips**, exactly like a race.

Put together, the pieces compose — fan out independent tasks, pause, gather, combine — and the gather threads the
*symbolic* task values, not just constants:

<!-- doclint:case p153-async-await/fan-out-delay-gather-combine -->
```groovy
@Ensures({ result == (a + 1) + (b + 1) + (c + 1) })
static int gather(int a, int b, int c) {
    def t1 = async { a + 1 }
    def t2 = async { b + 1 }
    def t3 = async { c + 1 }
    await Awaitable.delay(5)
    def r = await(t1, t2, t3)
    return ((int) r[0]) + ((int) r[1]) + ((int) r[2])
}
```

The three tasks run independently over the inputs, the `delay` drops out (a no-op), and `all` gathers them into the
value list `[a+1, b+1, c+1]` — so `(a + 1) + (b + 1) + (c + 1)` proves over symbolic `a, b, c`. Drop one task's
`+ 1` from the contract and it refutes.

The assumed structural half is exactly that safe discipline: the awaited tasks complete and don't interfere.
Awaiting a task whose *value* the verifier can't see — an `Awaitable` *parameter*, a foreign `CompletableFuture`, a
value-or-fallback `completeOnTimeoutMillis` — isn't a determinate read-out, so it skips rather than guess. And a
closure that *mutates shared state* (the unsafe pattern the docs warn against) is the genuine race — the structural
half, Lincheck/Fray territory, not this proof. That half is exercised for real in [the structural rungs](../CONCURRENCY.md):
a Lincheck stress test confirms the safe fan-out/gather is deterministic on actual threads, and catches the
shared-mutation race on the unsafe twin.

### PAR disjointness — the fork-window interference check (Phase 240)

"The tasks don't interfere" stopped being an assumption and became a **checked side condition** — the
disjointness premise of the Hoare/CSL PAR rule, and slice 1 of the SEQ/PAR ladder. The safe-value model above
resolves a task's captured reads against the bindings in scope *at the read-out site*; if the enclosing body
writes a captured variable **between the task's fork and its join**, that model is unsound — the task may run
before or after the write, so its value is scheduler-dependent. Before this phase the checker quietly *proved*
the post-write value on that shape. Now it errors:

<!-- doclint:case p240-par-interference/stale-read-body-writes-a-captured-local-between-fork-and-await -->
```groovy
@Ensures({ result == 101 })
static int stale() {
    int s = 0
    def fa = async { s + 1 }
    s = 100
    int a = await fa
    return a
}
```

> Parallel interference in 'stale': the async task forked at line 5 captures 's', which the body writes at
> line 6 before the task's join…

This is an **error, not a skip** — the race is a bug in the code, not a limit of the model. The check is
window-precise: the join is the first mention of the task's handle after its fork, so the same write placed
*after* the join — or between one task's join and the next task's fork — is ordinary sequential code and still
proves:

<!-- doclint:case p240-par-interference/a-write-between-sequential-fork-join-pairs-is-safe-proves -->
```groovy
@Ensures({ result == 102 })
static int sequentialPairs() {
    int s = 0
    def fa = async { s + 1 }
    int a = await fa
    s = 100
    def fb = async { s + 1 }
    int b = await fb
    return a + b
}
```

`fa` reads `s` at 0, `fb` reads it at 100 — `a == 1`, `b == 101`, and `102` proves, because each write falls
outside every live task's fork-join window.

All four interference directions are covered: the body writing what a live task reads (above), the body
*reading* what a live task **writes**, and two tasks with overlapping windows conflicting write-vs-write
(the `RacyGather` shape rung 3 catches at runtime — two concurrent `s = s + 1` — now refuted at compile
time) or write-vs-read. The **synchronisation media are exempt**, exactly as channels are exempt in the CSP
PAR rule: `DataflowVariable` locals (write-once, reads block until the bind), `AsyncChannel` pipeline vars
(FIFO), and the `Awaitable` handles themselves — so the dataflow and channel examples above pass unchanged.
A method (or class) declaring `@Rely`/`@Guarantee`/`@UnderRely` suppresses the check: that machinery models
interference *deliberately*.

Honest boundaries: the join is the first handle mention after the fork (any use counts — an `await`, a
gather, an `orTimeout` wrapper); a task never mentioned again is treated as live to the end of the body
(conservative). Accesses are name-grained over params, body locals, and fields of the enclosing class —
effects behind foreign receivers or operators (`sb << x` on a shared builder) are not tracked, and such
arms already fall outside the safe-value model. What remains assumed is **completion** (every forked task
finishes) — the deadline/liveness half, which stays rung 2/3 territory.

