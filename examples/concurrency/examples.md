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
> delivery — is checked separately by Lincheck / TLA+ TLC / Fray. See **[README.md](README.md)**.


groovy-verify is a *sequential* SMT-backed checker — it reasons about no thread interleavings, races, or
deadlock. Yet a surprising amount of concurrent code's correctness factors into two halves: a **local,
sequential obligation** the developer must get right, and a **structural guarantee** the runtime provides.
*Assume* the structural half and the local half is an ordinary sequential proof — and that half is usually the
one carrying the interesting bug. These examples prove the local half across four of Groovy's concurrency
features, each assuming a different structural guarantee:

| Feature | Structural guarantee (assumed) | Local obligation (proven) |
| --- | --- | --- |
| Locks (`@WithWriteLock` / `@Synchronized`) | mutual exclusion | each critical section preserves the monitor invariant |
| Agents / actors | serialization (one message at a time) | each handler preserves the invariant |
| Dataflow | single-assignment | the network computes the right value |
| Channels | FIFO delivery | each element gets the right per-element transform |

What we *never* prove is the structural half itself — no mutual exclusion, no deadlock-freedom, no delivery or
termination; that needs concurrent separation logic, out of scope for a sequential checker. These are honest
"prove half the property" results: the half SMT can discharge, which is usually the functional one.

The *rely/guarantee* story goes further than the four above — here we prove **both halves**. First, the
**compatibility lemmas** are pure logic: `@Rely('T')` / `@Guarantee('T')` two-state predicates over shared state,
with the verifier auto-discharging that each rely is reflexive and transitive, each guarantee reflexive, and every
thread's guarantee implies every *other* thread's rely (`G_i ⟹ R_j`) — certifying the rely/guarantee *conditions*
compose. Second — and this is newer — the per-thread **interleaving proof** itself now runs for Int shared state:
a rely-step is `@Modifies` (havoc the shared frame) + `@Ensures` over `old` (assume the rely), so each thread's
*code* is checked to stay safe across the environment's interference. The concurrent bounded buffer below proves a
real memory-safety property — no out-of-bounds access under a concurrent peer — both ways. What still stays out is
the *scheduler* itself: that the threads really are concurrently interleaved with the assumed atomicity.

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

Those two disclaimed halves are exercised on this exact example by the runtime checkers in [the structural rungs](README.md): a
**Lincheck** spike (`./gradlew concurrentTest`) shows a `synchronized` `Account` is linearizable while an
unlocked one races, and a **Fray** spike (`./gradlew frayCheck`) drives the JVM scheduler over a two-account
bank transfer to confirm ordered locking is deadlock-free — and to catch the lock-ordering deadlock when it
isn't. Same boundary, made concrete; see [`README.md`](README.md).

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
structural guarantee (here, that each variable really is bound once) and never prove deadlock-freedom or
termination — only the value the network computes, given that it computes one.

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

### Rely/guarantee — the conditions compose, and the bodies uphold them

The producer/consumer is the capstone case study of the information-flow paper this work follows — Graeme Smith's
[*A Dafny-based approach to thread-local information flow analysis*](https://staff.itee.uq.edu.au/smith/recent/dafny.pdf)
(FormaliSE 2023). Most of that case study is machine-checked by
the [information-flow examples](../information-flow.md) further down: the buffer element's
classification is *value-dependent* on `head`/`tail`, advancing `tail` is a *secure-update* on a control variable,
and the producer *declassifies* what it releases. The one concurrency-specific piece is the **rely/guarantee**
coupling (the paper's §IV) — `head`/`tail` are shared, so each thread reasons locally by *relying* on how its
neighbour behaves. Those conditions are two-state predicates (the parameters split into a pre-state and a
post-state). One `Buffer` class carries both them and the thread bodies that run under them:

<!-- doclint:case p-ring/readme-flagship-rely-guarantee-buffer-read-write -->
```groovy
@Invariant({ 0 <= head && head <= tail && tail <= values.length })   // the bounded-buffer invariant
class Buffer {
    int head, tail
    int[] values

    @Rely('Consumer')      static boolean rCons(int oldHead, int oldTail, int head, int tail) {
        head == oldHead && oldTail <= tail       // the producer keeps my read pointer, only grows the buffer
    }
    @Guarantee('Producer') static boolean gProd(int oldHead, int oldTail, int head, int tail) {
        head == oldHead && oldTail <= tail       // I never move head; I only append
    }
    @Rely('Producer')      static boolean rProd(int oldHead, int oldTail, int head, int tail) {
        tail == oldTail                          // the consumer keeps my write pointer
    }
    @Guarantee('Consumer') static boolean gCons(int oldHead, int oldTail, int head, int tail) {
        tail == oldTail && oldHead <= head       // I never move tail; I only advance head
    }

    @Requires({ head < tail })                   // an element is available
    @UnderRely('Consumer')                       // run under the consumer's rely (rCons) — synthesised + framed
    int read() {
        int v = values[head]                     // ← PROVEN in bounds despite the concurrent producer
        head = head + 1
        return v
    }
    @Requires({ tail < values.length })          // room to append
    @UnderRely('Producer')                       // run under the producer's rely (rProd)
    void write(int x) {
        values[tail] = x                         // ← PROVEN in bounds despite the concurrent consumer
        tail = tail + 1
    }
}
```

**Both halves of §IV, on one class.** The four predicates are the *compatibility conditions* — each thread's
`@Rely` is its neighbour's `@Guarantee` — and the verifier discharges them as pure logic: `gProd ⟹ rCons` and
`gCons ⟹ rProd` both hold, and every rely is reflexive and transitive, the lemmas that justify analysing each
thread alone. Weaken `gProd` to drop `head == oldHead` (let the producer move the consumer's read pointer) and it
no longer implies the consumer's rely:

```
[Static type checking] - Rely/guarantee compatibility does not hold: guarantee 'gProd' (Producer) implies rely 'rCons' (Consumer)
```

That is the **gluing logic** of thread-local reasoning. The *other* half — that each thread's **code** upholds
its rely — is the `read` / `write` bodies above, a *real* safety property: each is proven free of **out-of-bounds
access** under a concurrent peer. `@UnderRely('Consumer')` runs `read()` under the consumer's rely: a CONVERSION
transform **synthesises the rely-step from `rCons`** — the very predicate that drives the lemma — by havocing the
shared frame, assuming `rCons` rewritten over `old`, and conjoining the class invariant; then it frames every
shared access with that step, so `head` / `tail` are re-havoced wherever the environment could have run. The body
stays pure logic, as `@WithWriteLock` replaces a manual `lock()`.

This **verifies**. At `values[head]` the obligation is `0 <= head < values.length`; the synthesised rely gives
`head == old.head` (the producer never touched my read pointer) and the entry invariant
`old.head < old.tail <= values.length`, so `head < values.length` — in bounds *across the concurrent write*.
`read()` re-establishes the invariant on exit; `write()` is the mirror image under `rProd`. **Weaken a rely and
the safety is gone**, and the load-bearing conjunct is exactly the neighbour's promise about *your* pointer: drop
`head == oldHead` from `rCons` and `values[head]` refutes; drop `tail == oldTail` from `rProd` and `values[tail]`
refutes — each with an out-of-bounds counterexample.

> [!NOTE]
> **We never checked the buffer actually *works*.** Readers may have noticed what's missing: nothing here proves
> `read()` returns the value `write()` stored, or that the queue is FIFO. The contracts assert *memory safety*
> (every access in bounds) — and, in the §VII capstone below, *information flow* (no leak) — but **not functional
> correctness**. There is deliberately no `@Ensures` relating a read to a prior write. That property — every value
> read was previously written, in order — is **linearizability**, and it is checked at a different tier: the
> Lincheck spike in [the structural rungs](README.md) exercises it on the real bytecode. Three rungs, three jobs: this checker
> proves bounds (and info-flow), Lincheck tests value-correctness, and neither subsumes the other.

So the whole loop closes on one buffer: **write the `@Rely` / `@Guarantee` predicates once, tag the methods,
done.** The lemmas certify the relies *compose* (`G_i ⟹ R_j`); the bodies prove each thread *upholds* its rely.
And the framing isn't limited to a single critical section: because synthesis knows which fields are shared, the
rely-step is inserted **before each shared access at any depth** — between statements, inside `if`/`else`
branches, and **per loop iteration** (so a loop verifies only under a *rely-stable* invariant — `tail == constant`
under a growing-tail rely correctly **fails** — and a write that transiently breaks the invariant mid-loop is
caught). The one thing that genuinely stays out is the scheduler itself — that the threads really interleave with
the assumed atomicity — a structural assumption, like the lock examples.

> [!NOTE]
> **What `@UnderRely` expands to — the interleaving, made visible.** The instrumentation just described is real
> but happens in an AST transform, so it's invisible in the source above. Here is the *actual desugared body* the
> verifier sees for `read()` (not pseudocode — it's what the transform emits). Each `@Rely('Consumer')` predicate
> is synthesised into a rely-step method that **havocs the shared frame and assumes the rely**: `relyConsumer()`
> below is `$rely$Consumer`, carrying `@Modifies({ [this.head, this.tail] })` and
> `@Ensures({ head == old.head && old.tail <= tail && /* class invariant */ })`.
>
> ```groovy
> int read() {                 // @Requires({ head < tail })  @UnderRely('Consumer')
>     relyConsumer()           // ← env step: havoc head/tail; assume head==old.head, old.tail<=tail, + invariant
>     int v = values[head]     //   still in bounds: env kept head, only grew tail ⇒ head < tail <= values.length
>     relyConsumer()           // ← env step AGAIN: the producer may run right here, before the write
>     head = head + 1
>     assert 0 <= head && head <= tail && tail <= values.length   // ← masking-fix: the write kept the invariant
>     return v                 //   (a local-only statement gets no rely-step — only shared accesses do)
> }
> ```
>
> A rely-step sits before *each* shared access — not one at entry — and the transform recurses into `if`/`else`
> and loop bodies the same way; the post-write `assert` stops a transiently-broken invariant from being masked by
> the step that follows. That is the Smith/Dafny interleaving shape: environment interference modelled wherever
> the environment could actually run. (Only the frameless hand-written `@UnderRely('someRelyStep')` shorthand,
> with no `@Rely` predicate to read the frame from, falls back to a single rely-step at entry.)

> [!NOTE]
> **The atomicity grain — and where it bites.** Look at the desugaring above: the rely-steps sit *between*
> statements, so a single statement like `head = head + 1` (or `head++`) is modeled as one **atomic**
> read-modify-write — no environment step runs between reading `head` and storing it back. On the JVM that is
> *not* true: `head++` compiles to a non-atomic read / modify / write, and another thread genuinely can interleave
> in that window. So statement-atomicity is an assumption the proof *makes*, not a fact it *establishes* — which is
> exactly why the finer tiers exist (the Lincheck schedule explores the real interleavings; a TLA+ model can split
> the statement to expose the read/write gap). Two honest ways to close it where a use case demanded it, neither
> done here because we are only outlining the approach: model the field as an `AtomicInteger` so the
> read-modify-write really is atomic and the assumption holds, or apply finer-grained interleaving — hand-split the
> statement into `t = head; head = t + 1` so a rely-step lands in the middle and the lost-update window is
> *verified* rather than assumed.

This same shape now runs inside the *full* §VII body, where each access also carries an information-flow
obligation (the consumed element must be `Low`, the producer *declassifies* what it releases) — and that
intersection is **machine-checked**, both properties on one class.

### The full §VII capstone — info-flow × rely/guarantee, verified together

Smith's culminating example has plain *and secret* messages produced and consumed concurrently. The buffer above
proved bounds-safety under interference; the same `Buffer`, given a **value-dependent positional label**, now also
proves **no secret leaks** — the two obligations discharged on one body, each step's info-flow check evaluated
*through* the rely-step's havoc. This is the composition the whole arc built toward.

<!-- doclint:case p-vii/readme-capstone-info-flow-x-r-g-buffer -->
```groovy
@Invariant({ 0 <= head && head <= tail && tail <= values.length })
class Buffer {
    enum L { Low, High }
    static boolean leq(L a, L b) { a == L.Low || b == L.High }
    static L join(L a, L b) { leq(a, b) ? b : a }
    int head, tail
    @Label(by = 'level') int[] values                              // each slot's level depends on POSITION…
    static L level(int i, int head, int tail) { (head <= i && i < tail) ? L.Low : L.High }   // …the region [head,tail) is Low

    @Rely('Consumer')      static boolean rCons(int oldHead, int oldTail, int head, int tail) { head == oldHead && oldTail <= tail }
    @Guarantee('Producer') static boolean gProd(int oldHead, int oldTail, int head, int tail) { head == oldHead && oldTail <= tail }
    @Rely('Producer')      static boolean rProd(int oldHead, int oldTail, int head, int tail) { tail == oldTail }
    @Guarantee('Consumer') static boolean gCons(int oldHead, int oldTail, int head, int tail) { tail == oldTail && oldHead <= head }

    @Ensures({ true }) static void deliver(@Label('Low') int x) { }   // a PUBLIC sink — only accepts Low

    @Requires({ head < tail })
    @UnderRely('Consumer')                 // runs under the producer's interference: head pinned, tail grows
    int consume() {
        int v = values[head]               // in [head, tail) ⇒ Low (proven across the concurrent append)
        deliver(v)                         // Low → Low public sink: NO LEAK
        head = head + 1
        return v
    }
    @Requires({ tail < values.length })
    @UnderRely('Producer')                 // runs under the consumer's interference: tail pinned, head grows
    void produce(@Label('High') int secret) {
        int msg = Declassify.to('Low', secret)   // §III-E controlled release
        values[tail] = msg                       // a Low value at the boundary slot
        tail = tail + 1                          // §III-A array secure-update: old.tail ENTERS the Low region
    }
}
```

This **verifies** — and verifies *both* properties on each body. `consume()` is proven free of out-of-bounds
access under the concurrent producer (the R/G half above) **and** free of leaks: `values[head]` is `Low` (the
label says so when `head < tail`, which the rely re-establishes), so the public `deliver` accepts it; advancing
`head` pushes the just-read slot back to `High` (re-securing — always safe). `produce()` declassifies, writes the
`Low` value, and advances `tail` — the **array secure-update** obligation `leq(Γ(values[tail]), level(tail, head,
tail+1))`, discharged under the invariant that makes the new level `Low` for **any** `head ≤ tail`.

**Why it is sound under interleaving.** The info-flow obligations are discharged *through* the rely-step's havoc,
not on a frozen snapshot. A rely-step forgets every tracked array slot whose index names a field the environment
may move — but keeps the ones the rely *pins*: the producer's `rProd` holds `tail == old.tail`, so the value
written at `values[tail]` survives the step and the secure-update sees it. Because `level(tail, head, tail+1)` is
`Low` for *every* `head ≤ tail` the consumer could leave behind, the release is secure against all interleavings
the rely permits — not one lucky schedule. And the machinery does **not** mask a leak: drop the `Declassify` and
write the raw `secret`, and the secure-update **refutes** at `tail++` (`High → Low`) with the full R/G
instrumentation still in place.

**Honest framing.** This is §VII's *shape* reconstructed on the per-thread rely-step model already built for
bounds — the security lattice now rides the same havoc-under-rely interleaving the bounds proof uses. It is **not**
a machine-checked concurrency proof: that the threads genuinely interleave with the assumed atomicity stays a
*modelling assumption*, the same structural one as the lock / serial-agent examples. What is mechanical is the
decomposition — value-dependent `@Label(by = …)`, the secure-update on `tail`, `Declassify.to`, the four
compatibility lemmas, and the rely-step framing — all composing on one class, both properties at once.

**The other half — the structural guarantee — lives in [the structural rungs](README.md).** That is the part this checker
*assumes*, made runnable on this exact buffer by two complementary tools: a **TLA+** model (`Buffer.tla`)
that TLC explores across *every* interleaving — where the rely stops being an assumption and becomes a checked
theorem about the peer's action, and liveness is checkable too — and a **Lincheck** test
(`src/concurrent/`) that model-checks the *real bytecode* of a lock-free `SpscBuffer`, catching the same leak as
a linearizability violation. Three rungs — compile-time proof here, exhaustive model, tested bytecode — each
trading coverage for fidelity; see [`README.md`](README.md). Run them with `./gradlew tlcCheck` and
`./gradlew concurrentTest`.

The machinery isn't specific to the buffer's two pointers. A different shape — a shared scalar with a
**monotonicity** rely — works the same way: two threads only ever increment a `count`, each relying on the other
to do likewise, so a value once observed below the count stays below it.

<!-- doclint:case p-counter/monotonic-counter-observed-bound-persists -->
```groovy
@Invariant({ count >= 0 })
class Counter {
    int count
    @Rely('Other')   static boolean rOther(int oldCount, int count) { oldCount <= count }   // others only increment
    @Guarantee('Me') static boolean gMe(int oldCount, int count)    { oldCount <= count }    // I only increment

    @Requires({ k <= count })
    @UnderRely('Other')
    void atLeast(int k) {
        assert count >= k                        // ← STILL holds across concurrent increments
    }
}
```

`count >= k` survives because the rely says the environment only *raises* `count` — the synthesised rely-step
havocs it under `oldCount <= count`, so `k <= old.count <= count`. Make the rely non-monotonic and the bound is
gone; lift it into a loop and the loop invariant `k <= count` proves only because it is rely-stable (the rely-step
frames each iteration). Same `@Rely` / `@UnderRely`, a wholly different concurrent property.

