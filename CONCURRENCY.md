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
3. **Tested real bytecode** (Lincheck, Fray, jcstress) — bounded or empirical search over schedules of the *real*
   code. Lincheck model-checks an implementation's operations for linearizability; Fray drives the JVM scheduler over
   a hand-threaded scenario for deadlock / lock-ordering; jcstress stress-runs the actors billions of times on real
   JIT/hardware and tallies the *outcomes* — the Java-Memory-Model publication grain. Either way the atomicity /
   ordering assumption is discharged against an actual implementation, not a model.

The rest of this doc climbs the rungs in turn. The running example throughout is the **Smith/Dafny §VII**
information-flow buffer — the [§VII capstone](examples/smith.md) the checker proves at rung 1, modelled in
TLA+ at rung 2, and Lincheck-tested at rung 3. Rung 3 also explores a few more
concurrency examples with different shapes to the buffer:
lock-based bank accounts, Groovy 6 async/await, and a deadlocking transfer (the Fray case).
Rung 2 additionally carries a **second** TLA+ model — Leino's [ticket lock](examples/dafny.md) — a different
kind of pairing, where rung 1 already proves *both* safety and liveness and TLC corroborates them and pushes
past the proof's two-process bound (see [the ticket-lock subsection](#a-second-rung-2-artifact--leinos-ticket-lock-where-rung-1-already-owns-both-halves)).

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

### A second rung-2 artifact — Leino's ticket lock, where rung 1 already owns *both* halves

The §VII buffer splits cleanly: rung 1 proves the local half, rungs 2–3 the structural half it disclaims. The
**ticket lock** ([`examples/dafny.md`](examples/dafny.md), the KRML260 port, Phases 170–175) is different —
here rung 1 SMT-*proves* the structural properties themselves: **mutual exclusion** (safety) and, for two
processes, the **fair-schedule eventually-eats** (liveness). So its rung-2 companion plays a different but
still-substantive role — **corroboration, assumption-validation, and reach beyond the fragment** — rather than
covering a disclaimed half.

| File | What it is |
|------|------------|
| [`Ticket.tla`](src/tlc/Ticket.tla) | Leino's ticket system as a state machine (his Model 2, §7.2): `(ticket, serving, cs, t)` with `Request`/`Enter`/`Leave` as two-state actions. Maps directly to the groovy-verify events. |
| [`Ticket.cfg`](src/tlc/Ticket.cfg) | The **correct** system at N = 3: `MutualExclusion` + the strengthened `Valid` invariant hold on every reachable state, and `Liveness` (`Hungry ~> Eating`, weak-fair) holds. |
| [`TicketBad.cfg`](src/tlc/TicketBad.cfg) | The **broken-dispenser** variant: `RequestBad` fails to advance `ticket`, so two processes draw the same one. TLC reports `MutualExclusion` violated and prints the trace. |

`./gradlew tlcTicket` model-checks the correct system at N = 3 (**179 distinct states**): all three properties
pass. The broken variant (a manual run — `java -cp tla2tools.jar tlc2.TLC -config TicketBad.cfg Ticket.tla`)
prints a **five-state trace ending with two processes Eating at `serving = 0`** — both handed ticket 0 by the
stuck dispenser, the step-by-step twin of groovy-verify's mutual-exclusion refutation (Phase 170).

**What this does that rung 1 does not:**

- **Validates the proof's assumptions.** The liveness proof (Phases 174–175) *assumes* the frame / serving-
  stability / fairness facts as `@Requires` hypotheses. TLC builds the transition system and checks them by
  exhaustive enumeration — confirming those assumptions really are consequences of the state machine, not
  vacuous or over-strong. That is a soundness check the proof cannot self-provide.
- **Reaches N > 2.** Rung 1's fair-schedule liveness is bounded to two processes (the ≤ 1 measure bound is what
  lets it avoid an unbounded trace loop). TLC checks safety *and* fair liveness at **N = 3** — the general-N
  frontier the proof can't yet make.
- **The same invariant, exhaustively.** `Valid` — the strengthened invariant rung 1 shows *inductive* — is
  confirmed true on all 179 reachable states, by a wholly independent method.

Same rung-2 limits as the buffer: action-grained, sequentially consistent, finite N and a bounded dispenser.

## Rung 3 — Tested real bytecode

The atomicity/ordering assumption, discharged against *real bytecode* across real schedules — several ways: the
lock-free §VII buffer, the lock-based accounts, and Groovy 6 async/await (all via **Lincheck**), deadlock /
lock-ordering (via **Fray**), and the memory-model publication grain (via **jcstress**). Three tools, three methods —
model-checking, controlled scheduling, empirical stress — *none subsumes the others*. The **seqlock** (below) is the
example where all three — rung 1 included — do *distinct* work, on the torn-read bug class.

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
(Since Phase 240 the *disjointness* half of that discipline is also checked at rung 1: an async task whose
captured state is concurrently written — the RacyGather shape in checker-visible source — refutes at compile
time as "Parallel interference", so what remains for this rung is completion and the real scheduler; see
[the fork-window check](examples/concurrency.md#par-disjointness--the-fork-window-interference-check-phase-240).)

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
  flag (released in Groovy 6.0.0-beta-1) cleans call sites inline so that thread is
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

### Empirical stress — jcstress

The third tested-bytecode sibling, and a *different method* from the other two. Where Lincheck model-checks the
operations for linearizability and Fray drives the scheduler for deadlock, [jcstress](https://github.com/openjdk/jcstress)
(OpenJDK's Java Concurrency Stress harness) runs the actors **billions of times on real JIT and hardware** and tallies
which *outcomes* occur — the canonical Java-Memory-Model test, reaching the **publication grain** the others approach
differently. It runs on the *same* `SpscBuffer` the checker proves and Lincheck checks (the `Correct` / `Leaky` pair,
named for `BufferLincheckTest`).

The test is two actors on a capacity-1 buffer: a producer `offer(1)`, a consumer `poll()`. The slot's array default
is `0`, so the observed value separates three worlds — `-1` (consumer first, empty), `1` (saw the published value),
and `0` (saw `tail` advanced but read the slot *before the value was written*: the publication race). The correct
buffer writes the slot then publishes via the `volatile tail`, so `0` is **forbidden — and never observed**; the leaky
one publishes first, so jcstress **observes** it:

```
RESULT      SAMPLES     FREQ       EXPECT  DESCRIPTION
    -1  154,926,095   51.23%   Acceptable  Consumer ran first — buffer empty.
     0       58,179    0.02%  Interesting  THE LEAK: tail advanced before the slot was written…
     1  147,415,480   48.75%   Acceptable  Consumer saw the fully published value.
```

58,179 hits in ~300 M runs — the leak, caught **empirically**. (The leaky `0` is marked `ACCEPTABLE_INTERESTING` so
`jcstressCheck` stays green while *reporting* the race; the correct buffer's `0` is `FORBIDDEN` and lands in "Failed
tests: No matches".) This overlaps Lincheck — both catch the leaky buffer — but by a different route: Lincheck
*model-checks* the interleaving space against a sequential spec, while jcstress *stress-tests* raw outcomes on real
hardware, where a JIT or weak-memory reordering the model abstracts away would surface. Same buffer, complementary
fidelity.

**The Java wrinkle.** jcstress generates its harness from `@JCStressTest` / `@Actor` / `@Outcome` via a **javac
annotation processor**, which won't fire on Groovy — so the test holder is Java (`src/jcstress/java`, like jcstress's
own samples), wrapping the same Groovy `@CompileStatic @POJO` buffer. A **second** test, `BoundedCounterJCStress`,
covers a different bug class — the **check-then-act** race ([the verified-invariant-that-concurrency-breaks
example](examples/concurrency.md#check-then-act--a-verified-invariant-that-concurrency-breaks)): `BoundedCounter`'s
`if (count < 1) count = count + 1` produces `count == 2` about **5 in 7 billion** runs, while the `@WithWriteLock`
`SafeBoundedCounter` never does — and groovy-verify proves the *identical* invariant for both, so only this rung
separates them. A **third** test, `AtomicBoundedCounterJCStress`, answers the obvious objection — *"use an
`AtomicInteger`"* — and shows it doesn't help: `if (count.get() < 1) count.incrementAndGet()` composes two atomic
ops with a gap, so it still reaches `2`, while a single `compareAndSet` (`casIncrement`) is `FORBIDDEN` from doing
so. The sting: it races *more* readily, not less — measured at **~5–6%** of samples (millions of hits), because two
barriered atomic ops open a wider window than one volatile read-then-write, so even `quick` mode surfaces it at once.
On the verifier side the atomic is **modelled as a wrapped int** (`get()` reads a cell; `incrementAndGet`/`set`/`addAndGet`/`compareAndSet`
write it), so the *sequential* `@Invariant({ count.get() <= 1 })` is **proved** just like the plain-`int` one and
refutes at `<= 0` — pinned by `SpscBufferVerifyTest.atomicInteger_checkThenActInvariantVerifies` and the
`P-check-then-act` cases. (The plain-`int` counter's `5-in-7-billion` rarity is why the default, not `quick`, budget is
used.) Run `./gradlew jcstressCheck` (JDK 25; not in `check`). Inspired by jcstress's samples, written ourselves —
theirs is GPL, this repo Apache.

### Seqlock — the torn read, where all three rungs share the work

The buffer and the counter both lean hardest on the runtime rungs — the verifier proves their `@Invariant`, but it's a
bounds check it would prove for the safe and unsafe versions alike (the lock is transparent to it). The **seqlock**
(sequence lock) is the example where rung 1 has *characteristic, non-transparent* work, paired with a runtime bug class
none of the others reach — the **torn read**. `SpscBuffer` is a publication race (writer ordering); `BoundedCounter` a
check-then-act (read-modify-write atomicity); the seqlock is **read-side snapshot atomicity** — a reader observing a
multi-field record that was never written together.

`SeqLock` protects two fields `x`, `y` that are one logical record (always `x == y`) behind a sequence counter whose
*parity* is the protocol: **even = unlocked / consistent, odd = a write in progress**. Its **thread-local half** — the
verifier proving the *implication-guarded* class `@Invariant({ seq % 2 == 0 ==> x == y })`: that `write` re-establishes
`x == y` before it republishes, and that a validated `tryRead` returns a consistent snapshot, with both refuting when
the protocol is broken — is [the rung-1 example](examples/concurrency.md#seqlock--snapshot-consistency-by-a-parity-protocol).
Unlike the counter, this is a protocol proof that *discriminates* the correct shape from the broken one. A real reader
*spins* until the guard passes, and a spin loop is outside the straight-line fragment (like the atomic counter's CAS
loop), so the verified unit is the single-attempt `tryRead` (snapshot or `null` = "retry") and the **spin is lifted to
the caller** — which is exactly how the runtime rungs use it. Here are those **structural halves**:

**Rung 3a — Lincheck** (`SeqLockLincheckTest`, `./gradlew lincheckTest`) model-checks the operations. The exposed `read`
is the spin-in-the-caller (loop `tryRead` to a consistent snapshot), so it is linearizable — `correctSeqLockIsLinearizable`
passes; `SeqLockLeaky`'s unguarded read returns a torn pair (`[1, 0]`) that no sequential history of `{write, read}`
explains, caught as a linearizability violation (`leakySeqLockIsCaught`). A single-attempt `tryRead` returning `null` on
contention is deliberately *not* exposed to Lincheck — `null` has no sequential explanation either, so it isn't
linearizable as a standalone op (the caller's retry is what makes it one).

**Rung 3b — jcstress** (`SeqLockJCStress`, `./gradlew jcstressCheck`) stress-runs a writer (`write(1)`) against a reader
on real hardware and tallies the observed `(x, y)` pair via `II_Result`. The record's default is `(0, 0)`, so the pair
separates the worlds — and the torn `1, 0` / `0, 1` is **forbidden for the validating reader (never observed)** but
**observed for the leaky one**:

```
RESULT    SAMPLES     FREQ       EXPECT  DESCRIPTION  (SeqLockJCStress.Leaky, one fork)
  0, 0  32,472,120   66.41%   Acceptable  Reader ran before the write committed.
  0, 1         291   <0.01%  Interesting  THE TORN READ: saw the old x but the new y.
  1, 0       1,095   <0.01%  Interesting  THE TORN READ: saw the new x but the old y.
  1, 1  16,420,465   33.58%   Acceptable  Reader saw the fully published, consistent record.
```

The validating `Correct` actor only ever lands on `0,0` / `1,1` / `-1,-1` (contended → `tryRead` returned `null`, where
a real reader retries); its torn outcome is `FORBIDDEN` and lands in "No matches".

> **This is the rung that earned its keep.** That last sentence used to be false. The parity protocol was correct as an
> *algorithm* and wrong as *Java*: `tryRead` re-sampled `seq` with no fence between the two plain reads and the
> re-sample. A volatile read is an **acquire** — it stops later accesses drifting *before* it (which is why `rx`/`ry`
> can't float above `s1`), but it does **not** stop earlier accesses drifting *after* it. So the two data reads could
> be performed after `s2` was sampled, straddling a write the `s1 == s2` check had already blessed: guard passes, pair
> torn. The writer had the mirror gap — a volatile write is a **release**, so nothing stopped `x = v` / `y = v` moving
> *above* the lock-taking bump, exposing a half-written record while `seq` still read even.
>
> jcstress caught it, and only jcstress could: the reordering is invisible to rung 1 by construction (it doesn't model
> reordering) and to Lincheck, whose model-check is sequentially consistent. The fix is the textbook pair —
> `VarHandle.releaseFence()` after taking the write lock, `VarHandle.acquireFence()` before re-sampling `seq` — the
> same two barriers Linux's seqlock spells `smp_wmb()` / `smp_rmb()`, and the same `acquireFence()` that opens
> `StampedLock.validate`. With them the FORBIDDEN outcome is gone; `Leaky` still tears exactly as above, because its
> bug is the missing validation, not a memory-model subtlety.
>
> The fences are **invisible to rung 1** — a fenced body proves identically to its unfenced twin, since a fence has no
> sequential semantics at all (the engine treats it as a no-op, and a test pins that it can't launder a broken proof
> either). That asymmetry is the point: the proof was never *wrong*, it was *silent*, and the rung below it is what
> speaks. A three-rung story where every rung always agrees would be decorative; this is the case where it isn't.

Same source, three rungs, each doing
distinct work: rung 1 proves the parity protocol *above* the memory model, Lincheck catches the *logic* torn read (the
reader skipping its validation) under its sequentially-consistent model-check, and jcstress reaches the *empirical*
grain on real JIT/hardware — and, as above, catches what the two rungs above it structurally cannot.
**Why no Fray?** A seqlock is lock-free — the writer never blocks and the reader spins
without acquiring a blocking lock — so there is no lock graph to deadlock; Fray's specialty (deadlock / lock-ordering)
finds nothing here, which is why the bank-transfer and dining-philosophers got Fray and the buffer and seqlock do not.
Inspired by jcstress's samples, written ourselves — theirs is GPL, this repo Apache.

## Lineage — the same gap in Dafny

The Smith/Dafny paper this work follows sits at rung 1 too: Dafny's core is sequential, and it gets
thread-local IFC by *encoding* rely/guarantee as the same havoc-between-steps trick `groovy-verify` uses. So
the gap from a rung-1 proof to a memory-model-sound system is the same in both — what's different here is that
rungs 2 and 3 above make that gap explicit and discharge it on the *concrete* §VII buffer, rather than leaving
it as an assumption.
