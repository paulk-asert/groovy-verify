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

# "the other half": the concurrency model

## The three rungs

groovy-verify takes the stance that a compile-time proof is *one rung* of a concurrency argument, not the
whole of it: the proof is local and sequential, and trusting it against a real running system means
climbing two further rungs. Each trades coverage for fidelity; none subsumes the others.

1. **Proof** (`groovy-verify`) — the local, sequential VC, discharged at compile time by Z3. Decidable,
   compositional, but *assumes* the interleaving model: that its local, sequential view of the code is
   faithful to real concurrent execution — whatever tames the interleaving (a *rely*/*guarantee* discipline,
   a lock, an await resuming with a ready value) actually holds — and that the steps it treats as atomic
   really are.
2. **Exhaustive model** (TLA+ / TLC) — every interleaving of an *abstract* state machine. Confirms the
   interference assumptions actually compose and the system makes progress; still sequentially consistent
   and action-grained.
3. **Tested real bytecode** (Lincheck, Fray) — bounded search over schedules of the *real* code. Lincheck
   model-checks an implementation's operations for linearizability; Fray drives the JVM scheduler over a
   hand-threaded scenario for deadlock / lock-ordering. Either way the atomicity/ordering assumption is
   discharged against an actual implementation, not a model.

The rest of this doc climbs the rungs in turn. The running example throughout is the **Smith/Dafny §VII**
information-flow buffer — the [§VII capstone](examples/smith.md) the checker proves at rung 1, modelled in
TLA+ at rung 2, and Lincheck-tested at rung 3. Rung 3 also explores a few more
concurrency examples with different shapes to the buffer:
lock-based bank accounts, Groovy 6 async/await, and a deadlocking transfer (the Fray case).

## Rung 1 — Proof

On the **§VII buffer**, `groovy-verify` proves the **local, sequential** obligations of its rely/guarantee
argument: each thread, run under an *assumed* rely, stays in bounds and leaks nothing (the
[§VII capstone](examples/smith.md)). What it deliberately does **not** do is establish that the
rely/guarantee abstraction is faithful to a real interleaved execution — the scheduler, the atomicity grain,
and liveness. That is a different class of tool.

## Rung 2 — Exhaustive model

The smallest honest artifact for that other half is a **TLA+** model of the §VII buffer that an exhaustive
model checker (TLC) explores across *every* interleaving.

### Files

The model + configs live in [`src/tlc/`](src/tlc) (alongside the other rung sources — `src/lincheck`, `src/fray`):

| File | What it is |
|------|------------|
| [`Buffer.tla`](src/tlc/Buffer.tla) | The §VII producer/consumer buffer as a state machine. Maps element-for-element to `class Buffer`: `head`/`tail`, `data[i]` = `values[i]`, `dlvl[i]` = each slot's true secrecy, `PosLabel(i)` = `level(i, head, tail)`. |
| [`Buffer.cfg`](src/tlc/Buffer.cfg) | The **secure** spec: producer declassifies. All invariants hold, the relies are theorems, progress holds. |
| [`BufferLeak.cfg`](src/tlc/BufferLeak.cfg) | The **leak** variant: producer skips `Declassify`. TLC reports `RegionSound`/`NoLeak` violated and prints the shortest interleaved trace that leaks. |

### Running it

From the build — the secure spec is wired as a task (resolves `tla2tools` from GitHub releases, runs
TLC in `build/tlc`, fails the build on any invariant/property violation):

```sh
./gradlew tlcCheck     # "Model checking completed. No error has been found."
```

Or directly from [`src/tlc/`](src/tlc), with
[`tla2tools.jar`](https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar) and any JDK:

```sh
# secure: all invariants + relies + Progress hold
java -cp tla2tools.jar tlc2.TLC Buffer.tla

# leak: "Error: Invariant RegionSound is violated." + the interleaved counterexample trace (TLC exits 12)
java -cp tla2tools.jar tlc2.TLC -config BufferLeak.cfg Buffer.tla
```

Validated with TLC 2.19 at `Cap = 3`, `Data = {0, 1}` (49 distinct states): the secure spec passes all
invariants and temporal properties; the leak variant fails `RegionSound` with a two-step trace
(`ProduceLeak` advances `tail` over an un-declassified `High` slot, pulling it into the `Low` region).

### What this checks that the compile-time checker does not

The pivotal difference is in **how the rely shows up**:

- In `groovy-verify`, `produce()` is verified *assuming* `rProd` — the rely-step havocs `head` and pins
  `tail`, and we never model the consumer. Cheap, compositional, decidable.
- In `Buffer.tla`, there is no assumption. `Next == Produce ∨ Consume ∨ Done`, and TLC enumerates all
  interleavings. The rely becomes a **checked theorem about the peer's action** — `RelyProd` confirms
  the consumer's step really does keep `tail` fixed (what `produce()` relied on), `RelyCons` the mirror.
  Our compatibility lemma `gProd ⟹ rCons`, discharged as standalone logic, is here just the observation
  that the `Produce` action's effect on the pointers *is* `rCons`.

It also checks **liveness** (`Progress`: once `n` items are produced, `n` are eventually consumed) —
something the sequential checker cannot express at all (`@Decreases` is per-call termination, not
system progress).

### Where this still stops

TLC explores interleavings at the **action grain you wrote** — each action is atomic and execution is
**sequentially consistent**. So this model closes the "all interference is the peer" and liveness gaps,
but:

- **Atomicity:** `tail' = tail + 1` is one atomic action here (same idealization as the checker). To test
  non-atomic increment you would split it into two actions — `t' = tail` (latch the read) then
  `tail' = t + 1` — and let TLC explore the new interleavings.
- **Weak memory (the JMM):** out of scope — TLA+ is sequentially consistent. Justifying the
  "statement-atomic, SC" abstraction against real hardware needs a weak-memory tool (GenMC, herd7) or
  actual synchronization proven sufficient (VerCors / Viper).

## Rung 3 — Tested real bytecode

The atomicity/ordering assumption, discharged against *real bytecode* across real schedules — several ways: the
lock-free §VII buffer, the lock-based accounts, and Groovy 6 async/await (all via **Lincheck**), and deadlock /
lock-ordering (via **Fray**).

### The Lincheck buffer examples

The **domain** buffers live in [`src/concurrent/groovy/concurrent/`](src/concurrent/groovy/concurrent) (the
same source the verifier consumes), and the Lincheck **test** in
[`src/lincheck/groovy/lincheck/`](src/lincheck/groovy/lincheck):

| File | What it is |
|------|------------|
| `concurrent/SpscBuffer.groovy` | A correct lock-free single-producer/single-consumer buffer, carrying the `@Invariant`/`@Requires` that **groovy-verify proves** (rung 1). The §VII discipline made real: write the value, **then** publish it by advancing `tail`. |
| `concurrent/SpscBufferLeaky.groovy` | The same buffer with publish-**before**-write — the runtime analogue of the `BufferLeak.cfg` variant and the checker's refutation at `tail++`. |
| `concurrent/Buffer.groovy` | The **full §VII capstone** buffer — the same source as the `class Buffer` in the rely/guarantee + information-flow examples — carrying not just the bounds `@Invariant` but the `@Rely`/`@Guarantee`/`@UnderRely` discipline and the `@Label`/`Declassify`/`deliver` no-leak argument. groovy-verify proves *all* of that (rung 1); Lincheck model-checks the same bytecode for linearizability (rung 3). |
| `lincheck/BufferLincheckTest.groovy` | Lincheck model-checks all three. The SPSC contract is pinned with `nonParallelGroup` (one producer, one consumer, free to interleave) — the exact rely/guarantee discipline the verified `Buffer` assumes. |

**How `SpscBuffer` works — and why it's correct.** It's a fixed-capacity **ring**: a producer appends at `tail`, a
consumer reads at `head`, both indices only ever advancing and wrapped onto the backing array by `% capacity`. The
entire safety argument is one ordering rule in `offer` — write the slot *first*, publish *second*:

<!-- doclint:ignore README illustration: SpscBuffer publish-after-write discipline (faithful excerpt of SpscBuffer.groovy) -->
```groovy
boolean offer(int x) {
    int t = tail
    if (t - head == capacity) return false      // full
    items[t % capacity] = x                     // 1. write the value into the slot…
    tail = t + 1                                // 2. …THEN publish it by advancing tail
}
```

A consumer only ever reads indices `< tail`, so it can never observe a slot before its value has landed. That
publish-after-write order is the **operational form of the §VII secure-update**: the datum becomes Low (consumable)
*only* when `tail++` pulls its slot into the `[head, tail)` region. `poll()` is the mirror — read at `head`, *then*
advance `head` to free the slot. `SpscBufferLeaky` swaps the two lines of `offer` (publish, then write), and that
single inversion *is* the leak the trace below catches.

**The SPSC contract — why it needs no lock.** Single-producer, single-consumer: `head` is advanced only by the
consumer, `tail` only by the producer, both `volatile`. Each side relies on the other not to move *its* index — the
rely/guarantee discipline of the §VII `Buffer`, made concrete. Lincheck pins exactly that shape with
`nonParallelGroup` (at most one `offer` and one `poll` live at a time, free to interleave), and the class
`@Invariant` — `0 <= head <= tail` and `tail - head <= capacity` — is what groovy-verify proves over the same two
indices on the same source. The ring's wrap (`% capacity`) is the one structural difference from the linear,
one-shot §VII `Buffer`: `SpscBuffer` refills indefinitely, so it exercises the wrap that the capstone deliberately
omits.

**The same source, both rungs. ** `SpscBuffer.groovy` carries the exact `@Invariant`/`@Requires`
that groovy-verify proves: [`SpscBufferVerifyTest`](src/test/groovy/SpscBufferVerifyTest.groovy) reads *this
file* and runs the checker on it (proving `items[t % capacity]` in bounds and the bounded-occupancy invariant
preserved). The same test reads `Buffer.groovy` and proves the *whole* §VII argument over it — bounds under
`@UnderRely` interference **and** the no-leak information-flow discipline — while `rgBufferIsLinearizable` Lincheck-checks
that same file. One source carries the bounds buffer; one carries the full capstone; both run both rungs.
For the Lincheck compile, groovy-contracts' AST transforms are **disabled** (see
`compileConcurrentGroovy` in `build.gradle`), so the contracts resolve but inject nothing — leaving the bare
lock-free bytecode Lincheck instruments. (Why disable the *transforms*, not just assertions? A contract-checked method
isn't bare bytecode: groovy-contracts renders each assertion through Groovy power-assert (`ValueRecorder`), shared
static trackers, and a per-call closure allocation. Lincheck faithfully *explores* all of that, so the managed run
hangs on machinery unrelated to the algorithm. Lincheck 3.6 offers a surgical alternative —
`opts().addGuarantee(forClasses(…).ignore())` to skip named classes, which suffices for the bounds buffer — but
fully covering the richer `Buffer` means excluding an open-ended, version-specific set of internals, so disabling the
transforms wins as the one-move way to get genuinely bare bytecode. Note 3.6 also *fixed* the old Lincheck 2.39
`SnapshotTracker.restoreValues` `ConcurrentModificationException` that originally forced this — it's now a cleanliness
choice, not a bug workaround.) So rung 1 and
rung 3 run on **one source**, differing only in *what* they establish and at what *level*: groovy-verify proves the
sequential invariant *above* the memory model (no JMM / `volatile` / atomicity — deliberately), Lincheck proves
linearizability *at* it. "None subsumes the others" — but now they share the code.

The buffers and the Lincheck operation-holder classes are **`@CompileStatic @POJO`** Groovy. `@CompileStatic`
makes `offer`/`poll` compile to direct field/array bytecode (no call-site caching or dynamic dispatch);
`@POJO` drops the `GroovyObject`/metaclass plumbing so the class is a plain POJO — leaving Lincheck nothing
Groovy-specific to instrument or explore. (One gotcha: the project compiles Groovy with `-parameters` for
the checker; that must be turned **off** for this source set, or Lincheck reads `offer(int x)` as a
reference to a named generator `"x"`. See `compileConcurrentGroovy` in `build.gradle`.)

> **Cost note.** `@CompileStatic` alone keeps the result correct but is slow — Lincheck instruments the
> residual `GroovyObject`/metaclass machinery, ~1.5 min for 30 iterations. Adding **`@POJO`** strips that
> machinery and brings it back in line with plain Java (~16 s), confirming the overhead was the Groovy
> runtime plumbing, not the method bodies. So the conversion is both feasible *and* cheap — the pair
> `@CompileStatic @POJO` is what makes Groovy a clean fit for a Lincheck-instrumented data structure.

```sh
./gradlew lincheckTest
```

Isolated in its own source set (**not** wired into `check`), on the same **JDK 25** as the main build —
**Lincheck 3.6** (`org.jetbrains.lincheck:lincheck`) instruments via ASM 9.9, which handles JDK 25 class files.
(The older 2.x line, `org.jetbrains.kotlinx:lincheck`, bundled a byte-buddy that couldn't transform JDK 25 and
*silently* missed the planted bugs — which is why this was pinned to Java 21 before; 3.x removes the need.) Two
tests: `correctBufferIsLinearizable` passes (no interleaving breaks FIFO); `leakyBufferIsCaught` confirms
Lincheck reports the bug. Run the leaky one unwrapped and Lincheck prints the minimal trace:

```
| Thread 1  |                 Thread 2                  |
|           | offer(1): true                            |
|           |     tail = 1            ← publish the slot |
|           |     switch                                |
| poll(): 0 |                        ← reads stale slot  |
|           |     IntArray[0] = 1    ← write arrives too late |
```

`poll()` returns `0` — a value never offered. That is the operational form of an un-finalized
(≈ un-declassified) value being observed once the slot "enters the consumable region", caught as a
**linearizability violation**. Same leak as rungs 1 and 2, now on real bytecode across real schedules.

What this still does **not** cover: Lincheck's managed strategy explores interleavings by inserting
thread switches at shared accesses — it is essentially sequentially-consistent and catches *ordering/
logic* bugs (like publish-before-write), not pure *memory-visibility* bugs (a missing `volatile`). For
that last layer you need a weak-memory checker (GenMC, herd7) or jcstress on real hardware.

### async/await — the safe pattern holds, the unsafe one races

The [async/await examples](examples/concurrency.md) prove the *functional* half — `await(async { e })` is `e`, gathered tasks
combine to the right value — *assuming* the safe discipline: pure-value tasks that complete and don't interfere.
[`AsyncLincheckTest`](src/lincheck/groovy/lincheck/AsyncLincheckTest.groovy) (`./gradlew lincheckTest`)
checks that assumption on the real bytecode.

One wrinkle: async runs on its own executor — threads Lincheck's *managed* strategy doesn't control — so this uses
the **stress** strategy (many real concurrent executions) rather than model-checking. That's the right fit for code
with genuine *internal* parallelism: each operation fans out real tasks, and a result that's deterministic across
every run is the linearizability witness.

| Holder | Pattern | Lincheck |
|---|---|---|
| `SafeGather` | fan out three pure-value tasks, gather, combine | **linearizable** — always `9`, the proven value |
| `RacyGather` | three tasks read-modify-write a shared field | **caught** — lost updates yield a value no sequential history explains |

`SafeGather` confirms the structural half groovy-verify *assumes* genuinely holds when the tasks run for real.
`RacyGather` is the counterpoint: the unsafe pattern the safe-value discipline excludes is a real race, and the
runtime checker catches it — the same safe-vs-unsafe split as the lock-guarded vs racy accounts below.

### The locks example — both disclaimed halves

The [*Locks — the monitor invariant*](examples/concurrency.md) example proves each critical section preserves `balance >= 0`
*given* mutual exclusion, and explicitly disclaims two things: "no race on unlocked access, no deadlock,
no lock-ordering." Each disclaimed half gets the tool that fits it.

**Race / atomicity, and logic ⊥ concurrency — Lincheck** (`AccountLincheckTest` in `src/lincheck/`, over the
`concurrent.locks` accounts, run via `./gradlew lincheckTest`). Three accounts make the division of labour concrete — the same truth table as
[bmc4j](https://github.com/bmc4j/bmc4j)'s *coroutines-and-Lincheck* example, on plain `synchronized` Groovy:

| account | logic (the checker, rung 1) | thread-safe (Lincheck) |
|---|---|---|
| `RacyAccount` | ✓ proven — a guarded `withdraw` preserves `balance >= 0` | ✗ a read-modify-write race loses an update / overdraws — a history no sequential order explains |
| `OverdraftAccount` | ✗ **refuted** — an unguarded `withdraw` breaks `@Invariant({ balance >= 0 })` ("Cannot prove class invariant") | ✓ `synchronized` ⇒ each operation atomic ⇒ linearizable |
| `Account` (safe) | ✓ proven | ✓ linearizable |

The two right-hand columns are **orthogonal**, and each tool is blind to the other's. `OverdraftAccount` is
`synchronized`, so Lincheck checks its concurrent histories against its *own* (wrong) sequential behaviour and
passes — the overdraft is invisible to it — while the checker refutes the invariant. `RacyAccount` is the mirror:
the checker proves the guarded-withdraw *logic* (it reasons *given* mutual exclusion), but Lincheck finds the race
the proof assumed away. Only `Account` clears both. That is the whole "we prove the thread-local half, Lincheck the
structural half" story in one example — **logic correctness and thread-safety are different properties, and you
need a tool for each.**

bmc4j's example has a second aspect: coroutine-runtime modeling — verifying a `suspend` function's logic across a
suspension point. We mirror that too, on Groovy 6's `async`/`await` (the async/await section above): the post-`await`
logic is proven, and a bug after the suspension point refutes. Here, though, the accounts are plain `synchronized`
methods, so their concurrency lives entirely in Lincheck's interleavings — the suspend-logic half is the
async/await section's job. (bmc4j's accounts are `@Synchronized` too.)

### Deadlock / lock-ordering — Fray

Run with `./gradlew frayCheck` (sources in `src/fray/groovy/`). Where Lincheck checks a
data structure's *operations*, [Fray](https://github.com/cmu-pasta/fray) (OOPSLA'25) drives the real JVM
scheduler over a *hand-threaded* scenario — two threads transferring between two accounts in opposite
directions. `orderedTransfer` (lock the lower-id account first → a global lock order) is **deadlock-free**
across every explored schedule; enable the disabled `naiveTransfer` test and Fray reports a clean
`DeadlockException`, both threads' stacks pointing at the nested `synchronized`:

```
Thread-31  monitorEnter  naiveTransfer(BankTransferFrayTest.groovy:58)   ← holds A, waits B
Thread-32  monitorEnter  naiveTransfer(BankTransferFrayTest.groovy:58)   ← holds B, waits A
Thread-30  Thread.join   naiveTransferCanDeadlock(...:95)
```

Two Groovy-specific gotchas were needed (both in `build.gradle` / the test):

- **`-Dgroovy.indy.callsite.cleaner.inline=true`** — Fray seizes *every* thread, and Groovy's runtime
  `PIC-Cleaner` daemon (`CacheableCallSite`) parks forever on a queue, which Fray reads as a deadlock. The
  flag (in the Groovy 6.0.0-SNAPSHOT on the ASF snapshot repo) cleans call sites inline so that thread is
  never started. *Lincheck tolerates the Groovy runtime; Fray does not* — without it, Fray fails every Groovy test.
- **`ignoreTimedBlock = true`** — treats a timed park as blocking, so a background `ForkJoinPool` worker's
  timed park doesn't keep Fray spinning (→ step-explosion OOM) while the app threads are deadlocked.

**Cost note.** Fray is the heavyweight rung: it downloads + jlinks its own Corretto JDK 25 (~800 MB, one
time), and the controlled-schedule run with per-iteration classloader reset is ~16 s for 200 iterations
(the default is 1000). Lincheck and TLC are seconds. So Fray earns its place only where it's *distinct* —
deadlock / lock-ordering on hand-threaded code, which Lincheck-on-operations doesn't exercise.

### Dining philosophers — the N-fork generalisation

The bank transfer is the two-resource case of a pattern that scales: **dining philosophers** is its N-fork
generalisation. Its *thread-local* half — the verifier proving each philosopher acquires its lower-indexed fork
first, and refuting the naive scheme at the wrap-around philosopher `i = n-1` — is [the lock-ordering
example](examples/concurrency.md#dining-philosophers--deadlock-freedom-by-resource-ordering). Here is the **structural**
half: `DiningPhilosophersFrayTest`, the N-fork twin of the bank test. `resourceHierarchyIsDeadlockFree` — three
philosophers locking lower-fork-first — completes across every explored schedule; the disabled
`naiveAcquisitionCanDeadlock` deadlocks the three-way cycle (enable it to watch Fray report it). Same two
Groovy/Fray gotchas as the bank; the 3-thread schedule search needs a little more heap (`maxHeapSize = '2g'`, 50
iterations rather than 200).

A pleasing footnote spanning the rungs: a resource hierarchy is a **well-founded order on the locks**, and "strictly
increasing acquisition ⇒ no cycle" is the *same* well-foundedness argument rung 1 uses for loop **termination** via
`@Decreases` ("strictly decreasing measure ⇒ no infinite descent"). Deadlock-freedom-by-ordering is termination,
lifted to the resource graph. *(Dining philosophers is one of [jcstress](https://github.com/openjdk/jcstress)'s own
classic samples — credited as the source of the problem; the code here is our own.)*

## Lineage — the same gap in Dafny

The Smith/Dafny paper this work follows sits at rung 1 too: Dafny's core is sequential, and it gets
thread-local IFC by *encoding* rely/guarantee as the same havoc-between-steps trick `groovy-verify` uses. So
the gap from a rung-1 proof to a memory-model-sound system is the same in both — what's different here is that
rungs 2 and 3 above make that gap explicit and discharge it on the *concrete* §VII buffer, rather than leaving
it as an assumption.
