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

1. **Proof** (`groovy-verify`) — the local sequential VC, discharged at compile time by Z3. Decidable,
   compositional, but assumes the interleaving model.
2. **Exhaustive model** (`Buffer.tla` + TLC, here) — every interleaving of an *abstract* state machine.
   Confirms the relies compose and the system makes progress; still SC, action-grained.
3. **Tested real bytecode** (Lincheck on an actual `SpscBuffer` — see below) — bounded search over
   schedules of the *real* code, discharging the atomicity/ordering assumption against an implementation.

Each rung trades coverage for fidelity to the running system. None subsumes the others.

## Rung 1 — Proof

`groovy-verify` proves the **local, sequential** obligations of a rely/guarantee argument: each
thread, run under an *assumed* rely, stays in bounds and leaks nothing (the [§VII capstone](../smith.md)).
What it deliberately does **not** do is establish that the rely/guarantee abstraction is faithful to a
real interleaved execution — the scheduler, the atomicity grain, and liveness. That is a different
class of tool.

## Rung 2 — Exhaustive model

This directory holds the smallest honest artifact for that other half: a **TLA+** model of the §VII
buffer that an exhaustive model checker (TLC) explores across *every* interleaving.

### Files

| File | What it is |
|------|------------|
| [`Buffer.tla`](Buffer.tla) | The §VII producer/consumer buffer as a state machine. Maps line-for-line to `class Buffer`: `head`/`tail`, `data[i]` = `values[i]`, `dlvl[i]` = each slot's true secrecy, `PosLabel(i)` = `level(i, head, tail)`. |
| [`Buffer.cfg`](Buffer.cfg) | The **secure** spec: producer declassifies. All invariants hold, the relies are theorems, progress holds. |
| [`BufferLeak.cfg`](BufferLeak.cfg) | The **leak** variant: producer skips `Declassify`. TLC reports `RegionSound`/`NoLeak` violated and prints the shortest interleaved trace that leaks. |

### Running it

From the build — the secure spec is wired as a task (resolves `tla2tools` from GitHub releases, runs
TLC in `build/tlc`, fails the build on any invariant/property violation):

```sh
./gradlew tlcCheck     # "Model checking completed. No error has been found."
```

Or directly, with [`tla2tools.jar`](https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar)
and any JDK:

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

The atomicity/ordering assumption, discharged against *real bytecode* across real schedules — three ways: the
lock-free §VII buffer and the lock-based accounts (both via **Lincheck**), and deadlock / lock-ordering (via **Fray**).

### The Lincheck buffer examples

A runnable JVM-level companion lives in [`src/concurrent/groovy/concurrent/`](../../src/concurrent/groovy/concurrent):

| File | What it is |
|------|------------|
| `SpscBuffer.groovy` | A correct lock-free single-producer/single-consumer buffer. The §VII discipline made real: write the value, **then** publish it by advancing `tail`. |
| `SpscBufferLeaky.groovy` | The same buffer with publish-**before**-write — the runtime analogue of the `BufferLeak.cfg` variant and the checker's refutation at `tail++`. |
| `BufferLincheckTest.groovy` | Lincheck model-checks both. The SPSC contract is pinned with `nonParallelGroup` (one producer, one consumer, free to interleave) — the exact rely/guarantee discipline the verified `Buffer` assumes. |

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
./gradlew concurrentTest
```

Isolated in its own source set on a **Java 21** toolchain (Lincheck's well-supported LTS), so the
JDK-25 main build and the z3 suite are untouched; it is **not** wired into `check`. Two tests:
`correctBufferIsLinearizable` passes (no interleaving breaks FIFO); `leakyBufferIsCaught` confirms
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

### The locks example — both disclaimed halves

The [*Locks — the monitor invariant*](examples.md) example proves each critical section preserves `balance >= 0`
*given* mutual exclusion, and explicitly disclaims two things: "no race on unlocked access, no deadlock,
no lock-ordering." Each disclaimed half gets the tool that fits it.

**Race / atomicity, and logic ⊥ concurrency — Lincheck** (`src/concurrent/groovy/concurrent/locks/`, in
`./gradlew concurrentTest`). Three accounts make the division of labour concrete — the same truth table as
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

The one thing this *doesn't* mirror from bmc4j's example is its coroutine-runtime modeling — verifying a `suspend`
function's logic across a suspension point. An async / coroutine runtime is outside our SMT fragment, so it
loud-skips; our accounts are plain `synchronized` methods and the concurrency lives entirely in Lincheck's
interleavings. (bmc4j's accounts are `@Synchronized` too — the coroutine part is a separate aspect of that example.)

### Deadlock / lock-ordering — Fray

Run with `./gradlew frayCheck` (sources in `src/fray/groovy/`). Where Lincheck checks a
data structure's *operations*, [Fray](https://github.com/cmu-pasta/fray) (OOPSLA'25) drives the real JVM
scheduler over a *hand-threaded* scenario — two threads transferring between two accounts in opposite
directions. `orderedTransfer` (lock the lower-id account first → a global lock order) is **deadlock-free**
across every explored schedule; enable the disabled `naiveTransfer` test and Fray reports a clean
`DeadlockException`, both threads' stacks pointing at the nested `synchronized`:

```
Thread-31  monitorEnter  naiveTransfer(BankTransferFrayTest.groovy:57)   ← holds A, waits B
Thread-32  monitorEnter  naiveTransfer(BankTransferFrayTest.groovy:57)   ← holds B, waits A
Thread-30  Thread.join   naiveTransferCanDeadlock(...:93)
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

> **Note.** The Smith/Dafny paper this work follows sits at rung 1 too: Dafny's core is sequential, and
> the paper gets thread-local IFC by *encoding* rely/guarantee as the same havoc-between-steps trick we
> use. So the gap from rung 1 to a memory-model-sound system is the same gap in both — this directory is
> where it is made explicit.
