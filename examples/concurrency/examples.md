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
one carrying the interesting bug. These examples prove the local half across five of Groovy's concurrency
features, each assuming a different structural guarantee:

| Feature | Structural guarantee (assumed) | Local obligation (proven) |
| --- | --- | --- |
| Locks (`@WithWriteLock` / `@Synchronized`) | mutual exclusion | each critical section preserves the monitor invariant |
| Agents / actors | serialization (one message at a time) | each handler preserves the invariant |
| Dataflow | single-assignment | the network computes the right value |
| Channels | FIFO delivery | each element gets the right per-element transform |
| `async`/`await` | safe (pure-value) tasks complete without interfering | the value an awaited task computes |

What we *never* prove is the structural half itself — no mutual exclusion, no deadlock-freedom, no delivery or
termination; that needs concurrent separation logic, out of scope for a sequential checker. These are honest
"prove half the property" results: the half SMT can discharge, which is usually the functional one.

Groovy's **rely/guarantee** support goes further than the four above — proving *both* halves on a concurrent
buffer, and combining with an information-flow lattice (Graeme Smith's Dafny approach):
**[Thread-local information flow & rely/guarantee (Smith)](../smith.md)**.

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
**Lincheck** spike (`./gradlew lincheckTest`) shows a `synchronized` `Account` is linearizable while an
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
not a verifier limit.) `Awaitable.all` waits for everyone, so its result is fixed. The **racing** combinators
`Awaitable.any` / `Awaitable.first` return whichever task *wins* — but that's just an **if/else over an unknown
selector**: the result is one of the task values, so the verifier binds it to a nondeterministic choice and proves
the postcondition holds for *every possible winner*. `await Awaitable.any(async { 1 }, async { 2 })` satisfies
`result == 1 || result == 2` (whichever wins), but a spec of `result == 1` **refutes** (the other task might win) —
exactly how an if/else discharges all its branches. When the tasks compute the *same* value, the race is determinate
(`Awaitable.first(async { 42 }, async { 42 })` gives `42`), so no scheduler assumption is even needed.

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
half, Lincheck/Fray territory, not this proof. That half is exercised for real in [the structural rungs](README.md):
a Lincheck stress test confirms the safe fan-out/gather is deterministic on actual threads, and catches the
shared-mutation race on the unsafe twin.

