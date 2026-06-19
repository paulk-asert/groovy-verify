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

# Thread-local information flow & rely/guarantee — Smith's Dafny approach

This gallery reconstructs Graeme Smith's [*A Dafny-based approach to thread-local information flow
analysis*](https://staff.itee.uq.edu.au/smith/recent/dafny.pdf) (FormaliSE 2023) on groovy-verify — thread-local
information-flow control via rely/guarantee. **§III** is an information-flow
lattice with a noninterference obligation; **§IV** is rely/guarantee for reasoning under a concurrent peer; the
**§VII** capstone combines them (info-flow × rely/guarantee) on one bounded buffer. The buffer's *structural*
half — that the threads truly interleave at the assumed grain — is the deliberate non-goal, validated separately
by the [three structural rungs](concurrency/README.md).

## §III — Information flow: noninterference over a lattice



Compile-time **taint analysis** — Ballerina's `@tainted`/`@untainted`, the OWASP-style trackers — labels data and
refuses to let it reach a sink it shouldn't, at zero runtime cost. The same idea, on this engine, is one
*instance* of a more general construction: a security **lattice** (a proved `enum` of levels) plus a `@Label` on
each source and sink. The verifier discharges the **noninterference** obligation —
`leq( join(ΓE(e), PC), L(sink) )` — over the class's *own* lattice, by the same Z3 backend that proves the
contracts. No new solver theory; the obligation is just a lattice formula. (The Γ/lattice encoding follows [Smith](https://staff.itee.uq.edu.au/smith/recent/dafny.pdf),
§III. The paper's concurrent rely/guarantee story is *reconstructed* on the per-thread rely-step model — see the
rely/guarantee section — but the underlying concurrency/atomicity soundness, that threads truly interleave at the
assumed grain, stays a deliberate non-goal.)

That label-propagate-check shape is not unique to security. [Units of measurement](units.md) run it over a **free
abelian group** instead of a lattice: the label is a *dimension*, `×` adds its exponent vector and `/` subtracts,
and the forbidden point is an unchecked `as Quantity<K>` cast — same engine, same obligation skeleton, only the
label algebra changes.

A two-point `Low ⊑ High` is the taint lattice — read `High` as "secret" for confidentiality, or "untrusted" for
integrity; they're duals. **The leak that matters most is into a sink** — a value reaching a parameter classified
below it. This is the injection shape, and it refuses to compile:

<!-- doclint:ignore README illustration: cross-class info-flow leak (Service/Audit) -->
```groovy
class Service {
    enum L { Low, High }
    static boolean leq(L a, L b) { a == L.Low || b == L.High }
    static L join(L a, L b) { leq(a, b) ? b : a }

    static void handle(@Label('High') int secret) {
        Audit.log(secret)                                       // REFUTED — a secret reaches a public sink
    }
}

class Audit {                                                   // the sink, in its own class
    static void log(@Label('Low') int x) { /* … to a public channel … */ }
}
```

```
[Static type checking] - Possible information leak: 'secret' may carry data above the 'Low' classification of parameter 'x' of log
    obligation: leq(level(secret), Low)
```

The sink lives in another class; `Service` carries the lattice and the labelled source. Laundering through a local
doesn't help — `int t = secret; Audit.log(t)` refutes just the same. The label rides the *value*, not the
variable name.

**The part most taint checkers skip: implicit flows.** A secret can leak *without ever being assigned to the
sink* — through control flow. Branching on a secret raises a program-counter label inside both arms, so anything
assigned (or any sink called) there is tainted by *which branch ran*:

<!-- doclint:case pl1-infoflow/1c-implicit-flow-assign-under-secret-branch-refuted -->
```groovy
    @Label('Low')
    static int implicit(@Label('High') boolean secret,
                        @Label('Low') int a, @Label('Low') int b) {
        int t = a
        if (secret) t = a else t = b                             // t now reveals `secret`…
        return t                                                 // REFUTED — though only Low values are ever assigned
    }
```

Neither `a` nor `b` is secret, yet `t`'s value tells you `secret` — and the verifier refuses it. **And it
doesn't cry wolf:** the PC is *scoped* to the branch, so a low value that doesn't depend on the secret is still
fine afterwards:

<!-- doclint:ignore README illustration: PC-scoped info-flow (untouched value) -->
```groovy
    @Label('Low')
    static int scoped(@Label('High') boolean secret, @Label('Low') int pub) {
        int t = pub
        if (secret) { int unused = pub }                         // branch on a secret, but t is untouched
        return t                                                 // VERIFIED — t never depended on it
    }
```

That precision is the whole game: a tool that rejects every branch near a secret is useless. It falls out of a
syntax-directed walk that pushes the PC entering a branch and pops it on exit, threading a `Γ` environment (value
→ level) through assignments, returns, and call arguments alike.

**Beyond taint entirely: a classification that depends on state.** A taint label is fixed — a value is tainted or
it isn't. Here a value's *classification* can be a function of program state, reasoned about path-sensitively.
Declare `data` secret *unless authenticated*:

<!-- doclint:case pl1-infoflow/value-dependent-release-under-the-guard-verifies -->
```groovy
    static L classifyData(boolean authed) { authed ? L.Low : L.High }   // value-dependent classification

    @Label('Low')
    static int get(boolean authed, @Label(by = 'classifyData') int data,
                   @Label('Low') int fallback) {
        if (authed) return data                                  // VERIFIED — under the check, L(data) == Low
        return fallback
    }
```

Releasing `data` *under* the authentication check verifies; releasing it unguarded — `return data` with no
`if (authed)` — refutes, with the unauthenticated state (`authed = false`) as the counterexample, and a guard on
an unrelated condition doesn't help. No taint analysis can express "secret only sometimes"; here it's just a
classification function the SMT backend evaluates under the path conditions.

And the dual bug — changing the *control* variable to make the classification public while the data is still
secret — is caught too:

<!-- doclint:case pl1-infoflow/secure-update-flipping-the-flag-public-refuted -->
```groovy
    static void declassify(boolean authed, @Label(by = 'classifyData') int data) {
        authed = true                                            // REFUTED — L(data) becomes Low, but data may hold High
    }
```

Flipping the flag the other way (`authed = false`, *raising* the classification) verifies. That's the §III-A
secure-update rule: assigning a control variable mustn't strand a value it controls above its new level.

Sometimes a release is *intended* — a password checker must reveal whether the guess was right. That's
**declassification**, and here it's an explicit, greppable act rather than an invisible cast:

<!-- doclint:case pl1-infoflow/declassify-password-check-releases-the-equality-bit-verifies -->
```groovy
    @Label('Low')
    static boolean check(@Label('High') int password, @Label('Low') int guess) {
        return Declassify.to('Low', password == guess)           // release one bit — verified
    }
```

Drop the `Declassify.to` and the same method refutes (`password == guess` carries `High`); release the secret
itself (`Declassify.to('Low', password)`) and a reviewer sees exactly what escaped. Every release point is in the
source, by name.

Where it stops, it says so. Straight-line code, `if`/`else`, and `while`/`for` loops (with an inferred
Γ-invariant), sinks resolved both same-class and cross-class within the compilation unit; an unlabelled source, a
`for`-each over a collection, or a construct outside the fragment skips loudly. The whole *sequential* fragment of
Smith §III is in place; the named next steps are the refinements — sinks in a **precompiled/imported** class,
classification over a field, array element labels, and the predicate-gated (two-state) form of declassification.


## §IV — Rely/guarantee: the conditions compose, and the bodies uphold them

The *rely/guarantee* story goes further than the four above — here we prove **both halves**. First, the
**compatibility lemmas** are pure logic: `@Rely('T')` / `@Guarantee('T')` two-state predicates over shared state,
with the verifier auto-discharging that each rely is reflexive and transitive, each guarantee reflexive, and every
thread's guarantee implies every *other* thread's rely (`G_i ⟹ R_j`) — certifying the rely/guarantee *conditions*
compose. Second, the per-thread **interleaving proof** itself runs for Int shared state:
a rely-step is `@Modifies` (havoc the shared frame) + `@Ensures` over `old` (assume the rely), so each thread's
*code* is checked to stay safe across the environment's interference. The concurrent bounded buffer below proves a
real memory-safety property — no out-of-bounds access under a concurrent peer — both ways. What still stays out is
the *scheduler* itself: that the threads really are concurrently interleaved with the assumed atomicity.


The producer/consumer is the capstone case study of [Smith](https://staff.itee.uq.edu.au/smith/recent/dafny.pdf).
Most of that case study is machine-checked by
the **§III** information-flow examples above: the buffer element's
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
> Lincheck spike in [the structural rungs](concurrency/README.md) exercises it on the real bytecode. Three rungs, three jobs: this checker
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


## §VII — The capstone: info-flow × rely/guarantee, verified together


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

**The other half — the structural guarantee — lives in [the structural rungs](concurrency/README.md).** That is the part this checker
*assumes*, made runnable on this exact buffer by two complementary tools: a **TLA+** model (`Buffer.tla`)
that TLC explores across *every* interleaving — where the rely stops being an assumption and becomes a checked
theorem about the peer's action, and liveness is checkable too — and a **Lincheck** test
(`src/concurrent/`) that model-checks the *real bytecode* of a lock-free `SpscBuffer`, catching the same leak as
a linearizability violation. Three rungs — compile-time proof here, exhaustive model, tested bytecode — each
trading coverage for fidelity; see [`concurrency/README.md`](concurrency/README.md). Run them with `./gradlew tlcCheck` and
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

