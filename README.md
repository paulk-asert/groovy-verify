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

# groovy-verify

groovy-verify **proves your code can't hit whole classes of bug — at compile time, before you run
it.** An array index out of bounds, a null dereference, a divide-by-zero, a broken class invariant,
or simply *the wrong answer*: you say what should be true with stock
[`groovy.contracts`](https://github.com/spockframework/groovy-contracts) annotations
(`@Requires` / `@Ensures` / `@Invariant` / `@ThrowsIf` — the last one an annotation this project
prototyped and then contributed upstream as GROOVY-12135), compile under

<!-- doclint:case pl-truth/truth-assert-non-zero-int-literal-verifies -->
```groovy
@TypeChecked(extensions = 'verification.VerifyChecker')
```

and the [Z3](https://github.com/Z3Prover/z3) solver — an automated theorem prover — checks those
contracts hold for *every possible* input, or fails the build with a concrete counterexample (the
exact arguments that break it). It's a verification extension built on the standard `@TypeChecked`
extension mechanism, and the check runs *before* the contracts' own runtime assertions would ever
fire — so a bug that would surface as an exception in production surfaces as a compile error instead.

This started life as the verification spike in the *groovy6-functional* blog
companion repo. It was split out so it can grow on its own; that repo now
consumes it (via a Gradle composite build) rather than vendoring it.

## Where this sits

groovy-verify is an **auto-active verifier** — contracts as annotations, an SMT solver
discharging proof obligations at compile time, failed proofs surfacing as compile errors with
concrete counterexamples. Same family as Dafny, SPARK, Why3, Verus, and OpenJML; *not* an
interactive proof assistant in the Isabelle / Lean / Rocq style, nor a dependently-typed
language in the Idris / Agda style.

Within that family, the closest structural analogue isn't Dafny but
[**Verus**](https://github.com/verus-lang/verus): Dafny is a new language with its own compiler,
whereas Verus verifies an existing mainstream language by embedding in its native extension
mechanism — Rust attribute macros there, Groovy's `@TypeChecked` type-checking-extension SPI
here. The working one-liner: *experimental Verus for the JVM, with Dafny-style specifications.*

**The distinctive angle — executable specs.** The contracts are stock
[`groovy.contracts`](https://github.com/spockframework/groovy-contracts) annotations and the
quantifiers are plain GDK idioms (`(0..<n).every { … }`, `xs.any { … }`) — so they *also* execute
as ordinary runtime checks when verification is off. Write the spec once: what Z3 discharges is
**proven**, and anything it couldn't discharge degrades to a **runtime assertion**, not to
nothing. Design-by-Contract (the Eiffel lineage) with verification layered on top — neither
demanding a new language nor a comment-dialect spec. The graceful-degradation story isn't really
shared by anyone else in the auto-active family.

**Prior art on the JVM.** [JML](https://www.openjml.org/) (OpenJML), KeY, and
historically Krakatoa cover Java; JML is a comment-embedded spec dialect with aging tooling and
KeY leans interactive. Arguably, the JVM lacks a modern,
ergonomic, **auto-active** option: native annotation syntax, executable specs,
counterexamples-as-compile-errors, all delivered via the standard type-checking-extension SPI
rather than a separate build tool. The cross-language picture: Dafny (new language), SPARK
(Ada subset), Verus/Prusti (Rust), Frama-C/ACSL (C), OpenJML/KeY (Java), groovy-verify
(Groovy/JVM).

**Loudly partial, not silently sound.** Verification is sound *within* a deliberately **modest
fragment** — the subset of Groovy it models, grown not by size but by *alignment with the proofs people
actually write* — and **loudly unsound outside it**: anything the encoder can't model emits a "skipped:
outside fragment" diagnostic, never passes silently. The failure
mode the verifier family fears most is a silent *vacuous* pass — a "proof" that succeeds only because its
assumptions can never all hold, so it proves nothing. Saying *loudly partial* directly is the credible
position, and it's the one this tool holds.

**Known limitations — named, not hidden.** Consistent with that, every gap is called out: per capability
in the "deferred"/"residual" notes of the [capability table](CAPABILITIES.md), and as the
[ROADMAP](ROADMAP.md)'s non-goals. Three boundaries are worth stating up front. **Integer overflow** is
**opt-in** via `@CheckOverflow` (Verus parity, width-aware for `int`/`long`) — by default integers are
unbounded mathematical values.
**Floating point** is a *straight-line* IEEE-754 sub-fragment (bit-exact NaN / ±∞ / rounding, plus
`Math.sqrt`/`abs`), but FP loops and the transcendentals stay out. **Heap aliasing** has a deliberately
drawn line — *flat object fields* are modelled (two references' fields are identity-keyed, so a write
through one is seen through another exactly when they are the same object, `a === b`), while the *shape* of
object graphs — reachability, linked structures, separation logic — stays an explicit non-goal.

**Depth that vouches for the architecture.** A fully verified in-place insertion sort
(*sorted ∧ permutation*) under sound `@Modifies` framing, and a DFS over a functional graph
with **termination, soundness, unconditional coverage, and completeness** all machine-checked —
the benchmark proofs the Dafny community uses as credentials, here as worked examples below.

**A JVM-specific bonus.** Composability with sibling type-checking extensions: groovy-verify
sits alongside `NullChecker`, `PurityChecker`, `RegexChecker`, `FormatStringChecker`, and others
from `groovy-typecheckers` — each owning a property the others don't, all under the same
`@TypeChecked(extensions = […])` SPI. Pluralism of checkers over one language is itself an
interesting model — see [Relationship to Groovy's other checkers](#relationship-to-groovys-other-checkers).

> **Positioning sentence.** groovy-verify is an experimental auto-active verifier for a fragment
> of Groovy — Verus-style (embedded in the host language, SMT-backed, counterexample-producing)
> with Dafny-style specifications, distinctive in that:
> * its specs are ordinary executable `groovy.contracts`, so unproven obligations degrade to runtime checks rather than disappearing.
> * the verify type checker is composable with other type-checking extensions.
>
> "Dafny for Groovy" works as the informal shorthand.

## What's demonstrated

**The shapes this shows up in** — all within the modest fragment below, so these are the forms real code takes that
the engine proves end-to-end, not "point it at anything":

- **Money & conservation** — `BigDecimal` sums and scale, and N-account transfers that neither create nor destroy
  value (`bal.sum() == old.bal.sum()`).
- **Buffers, windows & search** — index arithmetic kept in bounds: ring buffers, sliding windows, binary search,
  pagination.
- **Validation & clamping** — range / non-null / size preconditions (your own `@Requires`, or a Jakarta
  `@Positive` / `@Size`), with opt-in integer-overflow checks.
- **Stateful objects & their rules** — a class `@Invariant` established by construction and preserved by every
  mutator; a transient or unreachable bad state refutes.
- **Ordering & algebraic laws** — sortedness and `compareTo`-shaped ordering, plus monoid / monad / reducer laws
  proved from an annotation alone.
- **Past where most tools stop** — information-flow security (no secret reaches a public sink), lock-free
  rely/guarantee concurrency, a mutual-exclusion protocol proved safe **and live** (Leino's ticket lock — the
  fair-schedule "a hungry process eventually enters", at any process count, with each round's progress derived from the transition relation), **process-network
  certification** over Groovy 6's `groovy.concurrent` channels (one live process per channel end, the element
  type as the channel's contract, deadlock-freedom proved as well-foundedness of the wait-for order — a cycle
  or a forgotten `close()` is a named compile error), dimensional analysis of
  JSR 385 units, and termination.

Concretely, the engine proves these kinds of property at **compile time** — and when it can't, it **refutes with a
concrete counterexample** (Dafny/Verus-style) rather than passing silently:

- **Preconditions** — every `@Requires` is discharged at each call site.
- **Postconditions** — a method body is proved to satisfy its `@Ensures` on every path, including early returns.
- **Class invariants** — a `@Invariant` is established by construction and preserved by every mutator, so a whole
  data structure (a ring buffer, a bank account) verifies as a unit.
- **Loop invariants & termination** — a loop `@Invariant` is established and maintained, and `@Decreases` proves
  the loop *terminates* — the same measure turning a recursive call into proof by induction.
- **Memory & arithmetic safety** — array indices in bounds, dereferences non-null, divisors non-zero, and — opt-in
  — no integer overflow: the implicit obligations, discharged from the contracts in scope.
- **Rely/guarantee** — under concurrent interference each thread's steps uphold its `@Guarantee` while tolerating
  the others' `@Rely`, so a shared buffer stays in bounds without a lock — and a body declaring `@Guarantee` is
  *checked* to honour it (its own-step transition proved against the predicate, a violation refuted with a
  counterexample).
- **Information flow** — no secret (`@Label('High')`) reaches a public sink (noninterference), with explicit
  `Declassify` for controlled release.
- **Dimensional analysis** — a JSR 385 `Quantity`'s dimension (its `[Length, Mass, Time]` exponents) is propagated
  through `multiply` / `divide` and checked against an `as Quantity<K>` cast, catching the result-kind the generic
  type can't infer: `length / time as Quantity<Speed>` verifies, the `multiply` typo refutes. The same
  label-propagation shape as information flow, over a group (`×` adds exponents) instead of a lattice. A second
  layer tracks **value & scale** — a quantity built from known units has a definite SI magnitude, so `1 km + 50000
  cm` read back in metres verifies as exactly `1500`, and claiming that number while extracting in *kilometres*
  refutes (the Mars-orbiter scale bug — same dimension, wrong scale — which dimensions alone can't catch).
- **Behavioural subtyping (Liskov)** — an override may only *weaken* a precondition and *strengthen* a
  postcondition, never the reverse.
- **Algebraic laws** — a `@Reducer` combiner is proved to satisfy the monoid laws, and a `@Monadic` carrier the
  monad / functor laws — automatically, from the annotation alone.
- **Exceptional contracts & specs for code you don't own** — `@ThrowsIf` proves a method throws *exactly*
  when its condition holds; shipped JDK spec skeletons make `Math.abs`, `Objects.checkIndex`,
  `indexOf`-then-`charAt` and friends provable at call sites — including *survival facts*
  (`floorDiv(a, b)` returned ⟹ `b != 0`) and *catch-entry facts* (`catch (ArithmeticException)` after
  `floorDiv` knows `b == 0`). Every trusted fact is inventoried in the ledger.

The full per-capability table — each with a ✅ phase tag and its honest "deferred" edge — is in
**[CAPABILITIES.md](CAPABILITIES.md)**.

**It also runs backwards — debugging from the symptom.** When you know a bad state reached production — a total
that went negative, an `@Invariant` that got corrupted, a combination the code swore couldn't happen — but not
*which input* got there, state the bad state's **negation** (an inline `assert`, an `@Ensures`, or the class
`@Invariant` itself) and let the refutation find it. The `fails on:` line is the exact input that produces the bad
state, and `VERIFY_REFUTATION` renders it as a runnable failing test you can drop into your suite — so you don't
trace forward from input to symptom, you state the symptom and the engine hands you the cause.

## The fragment

Those proofs hold over a deliberately **modest** slice of Groovy — sound *within* it and **loudly unsound outside
it**: anything the encoder cannot model emits a "skipped" warning rather than passing silently. The slice, by what
you write:

- **Type forms** — `class`, `enum`, `record`, `trait`, and `interface`, with contracts flowing along the type
  hierarchy (inherited class invariants, `super` calls, Liskov subtyping, trait default methods, and a
  `@Requires` / `@Ensures` an `interface` declares being inherited by every implementer). The unit of proof is a
  *method* carrying contracts; the type *definitions* themselves — constructors, deconstruction/pattern-matching,
  generated `equals`/`hashCode` — aren't proof targets.
- **Numbers** — `int` / `long`, arbitrary-precision `BigInteger`, exact `BigDecimal`, and IEEE-754 `double` /
  `float`; the operators `+ - * /`, integer `intdiv` / `%` / `mod`, `**`, the bit-ops `& | ^ << >> >>>` and
  complement `~`, comparisons and `<=>`, `++` / `--`, and compound assignment — variable (nonlinear) products
  dispatch to a dedicated solver. *Out:* floating-point loops & transcendentals.
- **Text** — *querying / composing* a `String` reasons symbolically on Z3's native string theory: `length` /
  `charAt` / `substring` / `indexOf`, `startsWith` / `endsWith` / `contains`, `+` / `concat`, `matches` (regex),
  and GString interpolation. *Rewriting* a string — `replace` / `replaceFirst` / `replaceAll` / `toUpperCase` /
  `toLowerCase` / `reverse` — folds **constant** operands through the real JDK method (so `replace` is replace-*all*
  and a regex `replaceAll` resolves exactly), and keeps only sound weak axioms (e.g. length-preservation) on
  symbolic ones; a real regex over a symbolic receiver skips. *Out:* building a string char-by-char (use a
  `char[]`).
- **Collections & data** — arrays and lists (read, update, bounds), finite `Set` and `Map` (membership, mutation,
  cardinality, the full set algebra `∪ ∩ − ^`), `Tuple` / `TupleN` and Groovy's map-as-named-tuple returns,
  immutable factories, and a `.limit(n)` / `.take(n)`-bounded `every` / `any` over an infinite `Stream.iterate`
  (proven by induction over the prefix) — all reasoned over with bounded **universal *and* existential**
  quantifiers that nest. *Out:* `.keySet()` / `.values()` projection, nested-set mutation, and that same infinite stream
  `every` / `any` with no `.limit` (it never returns).
- **Control flow** — `if` / `else`; `while`, `do-while`, `for`, and `for (x in xs)` loops (optionally one level
  nested) with `@Invariant` / `@Decreases`; the `xs.each { x -> … }` / `xs.eachWithIndex { x, i -> … }` iteration
  forms (modelled as that same for-in — *safety-only*: per-element properties, no hand-written invariant); early
  `return`; and `switch` *expressions* — the arrow form (`case 1 -> …`, a block with `yield` too) with literal /
  range labels (since Groovy 6.0.0-beta-3 static type checking requires a switch expression to be exhaustive —
  a `default`, or an enum subject with every constant covered — and the verifier's part is knowing when that
  `default` is *dead* under the precondition); plus
  side-effecting assignment, `++` / `--`, and parallel swap; and `try` / `catch` (no `finally`) — the
  happy path walked exactly, each handler entered with sound catch-entry state (and, when the try's
  throw sources are spec-characterised, the *reason* it was entered: `catch (ArithmeticException e)`
  after `Math.floorDiv(a, b)` knows `b == 0`).
  *Out:* `finally`, an *accumulating* `.each` (needs an `@Invariant` a `.each` statement can't carry), the older colon-style `switch` *statement* (`case 1:` … `break`) and
  type-pattern cases (`case String s`); closures and lambdas appear only as specification predicates
  (`every` / `any` / `inject`) and as law-carriers (`@Monadic` / `@Reducer`).

**Spec sources** — beyond `@Requires` / `@Ensures` / `@Invariant`, a precondition can also be read off a Jakarta /
`javax.validation` constraint on a parameter or field — `@Positive`, `@Min` / `@Max`, `@Size`, `@NotEmpty` — so
code already annotated for *runtime* validation verifies as-is. Exceptional behaviour is contracted with
`@ThrowsIf` — an *iff* by default (throws exactly when the condition holds), one-directional
(JML-`signals`-style) with `exhaustive = false`. And contracts for **code you don't own** come from
external-specification skeletons (JML's `.jml` idea, in Groovy dialect) — shipped for a growing JDK
surface and consumable from any jar; see [External specifications](#external-specifications).

The full itemised enumeration — every operator, type, theory, phase, and honest boundary — is in
**[FRAGMENT.md](FRAGMENT.md)**. The worked examples below put it through its paces.

The *"sound within it"* half of that claim is itself cross-checked. Because `groovy.contracts` annotations are
also *runtime* assertions, a differential **runtime rung** (`./gradlew runtimeRung`) recompiles each proved
contract with the verifier off, runs it over an input grid, and confirms the proof holds when the same
annotation actually executes — corroborating any disagreement against the real returned value, so a genuine
verifier-vs-runtime divergence is *caught* rather than assumed (the few that exist, like `a[i] = ++i`
evaluation order, are catalogued semantic differences, not logic bugs). See
**[BUILD.md](BUILD.md#the-runtime-rung--a-differential-soundness-oracle)**.

That stance — a compile-time proof is *one rung*, only as good as what it assumes — carries over to concurrency,
where the thread-local proof is the first of **[three rungs](CONCURRENCY.md)**: the proof, an exhaustive TLA+/TLC
model of every interleaving, and Lincheck / Fray exercising the real bytecode. (One instructive exception runs the
other way: on [Leino's ticket lock](examples/dafny.md#ticket-lock--mutual-exclusion-leino-krml260), rung 1 proves
the structural properties themselves — mutual exclusion and fair-schedule liveness, both at any process
count — with TLC discharging the proof's fairness witnesses exhaustively for a concrete N rather than
covering a disclaimed half.)

## Examples

Each snippet is compiled under `@TypeChecked(extensions = 'verification.VerifyChecker')`, so the proof runs at
**compile time** — yet the contracts are stock `groovy.contracts` annotations that still execute as ordinary runtime
checks when verification is off. Verification is opt-in per class or method: prove the high-value parts, leave the
rest as ordinary Groovy.

**A proof is the spec.** Z3 checks the body satisfies `@Ensures` for *every* input — get it wrong and the build
fails with the exact arguments that break it:

<!-- doclint:ignore README illustration: @Ensures on max -->
```groovy
@Ensures({ result >= a && result >= b })
static int max(int a, int b) { a >= b ? a : b }
```

```
[Static type checking] - Cannot prove postcondition of max holds on this return path
    ensured: ((result >= a) && (result >= b))
    counterexample: a = -1, b = 0
    fails on: max(-1, 0)
```

**The same machinery catches real bugs.** This is [Joshua Bloch's binary-search bug](https://research.google/blog/extra-extra-read-all-about-it-nearly-all-binary-searches-and-mergesorts-are-broken/):
`(low + high) / 2` overflows once the array is large enough, returning a negative index — caught at compile time,
with the input that triggers it:

<!-- doclint:case p-bloch-binsearch/buggy-midpoint-low-high-intdiv-2-overflows -->
```groovy
@CheckOverflow
@Requires({ 0 <= low && low <= high })          // a valid index window
@Ensures({ low <= result && result <= high })   // the midpoint lies within it
static int mid(int low, int high) { (low + high).intdiv(2) }
```

```
Possible ArithmeticException: addition overflows 32-bit signed range
    obligation: Integer.MIN_VALUE <= (low + high) && (low + high) <= Integer.MAX_VALUE
    counterexample: high = 2147483647, low = 1
    fails on: mid(1, 2147483647)
```

**And it scales to a real algorithm** — a recursive in-place insertion sort proven **sorted _and_ a permutation**
of its input, under sound `@Modifies` framing (the `every` / `count` / `old` are all plain GDK Groovy):

<!-- doclint:ignore README illustration: recursive insertion sort (sorted+permutation+frame) -->
```groovy
@Requires({ 0 <= m && m < a.length &&
            (0..<m - 1).every { a[it] <= a[it + 1] } &&   // prefix sorted
            (0..<m + 1).every { a[it] <= hi } })           // active region bounded by hi
@Modifies({ this.a })
@Ensures({ (0..<m).every { a[it] <= a[it + 1] } &&         // a[0..m] now sorted
           (0..<m + 1).every { a[it] <= hi } &&            // bound preserved
           (m + 1..<a.length).every { a[it] == old.a[it] } && // suffix framed (untouched)
           a.count(v) == old.a.count(v) })                 // permutation
@Decreases({ m })
void insert(int m, int hi, int v) {
    if (m > 0 && a[m] < a[m - 1]) {
        int t = a[m]; a[m] = a[m - 1]; a[m - 1] = t
        insert(m - 1, a[m], v)                              // recurse with the pivot as the bound
    }
}

@Requires({ 0 <= n && n <= a.length && (0..<n).every { a[it] <= hi } })
@Modifies({ this.a })
@Ensures({ (0..<n - 1).every { a[it] <= a[it + 1] } &&
           (0..<n).every { a[it] <= hi } &&
           (n..<a.length).every { a[it] == old.a[it] } &&
           a.count(v) == old.a.count(v) })
@Decreases({ n })
void sort(int n, int hi, int v) {
    if (n > 1) { sort(n - 1, hi, v); insert(n - 1, hi, v) }
}
```

**The full tour** builds from a single proof to that algorithm in five acts, covering every kind of data Groovy
touches (arrays, lists, sets, maps, `BigDecimal`, IEEE-754 floats, objects, graphs) in the idiom you'd already write:

1. **What a proof looks like** — postconditions, loop invariants, termination, recursion, internal iteration.
2. **Bugs the compiler now catches** — bounds, null, divide-by-zero, overflow — each with a concrete counterexample.
3. **Whatever your data is** — the data zoo: arrays / lists / sets / maps / strings / numbers, set algebra, enums, bitwise.
4. **Change, tracked soundly** — mutation, `@Modifies` frames, aliasing, class-invariant preservation.
5. **All the way to a real algorithm** — nested loops, a matrix sum, the insertion sort above, and a verified DFS.

Read **[the five-act tour](examples/tour.md)** for all of it. More worked-and-verified examples by domain:

- **[HumanEval](examples/humaneval.md)** — an external benchmark (Verus' suite) of LeetCode-shape problems we didn't pick.
- **[Dafny ports & cross-tool credentials](examples/dafny.md)** — `SumMax` (VSComp'10), `Find`, `BinarySearch`; Hillel Wayne's *Theorem Prover Showdown* with full specs (leftpad — imperative **and** functional-by-induction — fulcrum's argmin, unique with a bidirectional spec); mergesort's `merge` proved sorted *and* a permutation (math-comp's `path.v`); and Leino's *Modeling Concurrency in Dafny* ticket lock, reproduced end to end: mutual exclusion in both of the paper's formulations (enum-bounded and symbolic-N), the fair-schedule liveness at any process count with per-round progress derived from the transition relation, and a TLA+/TLC model as the second rung.
- **[OpenJML ports](examples/openjml.md)** — `Max by elimination` and `ChangeCase`, from the JVM's closest prior art (CC BY-NC).
- **[Concurrency](examples/concurrency.md)** — the *local* half of locks, agents, dataflow, and rely/guarantee — and, for **channel networks**, the *structural* half too: the SEQ/PAR ladder (Phases 240–267) checks task disjointness, channel-end linearity, element contracts, **deadlock-freedom as well-foundedness**, guarantee conformance, drain termination, and — past the one-shot fragment — **bounded FIFO traffic** (the *k*-th send is the *k*-th receive; drained values prove), **bounded streaming** (literal-bounded loops unroll: generator → map → drain pipelines prove their sum) **ALT** (`ChannelSelect` as a choice among the ready branches; an OR node in the wait-for graph), **streaming termination** (a symbolic-count producer loop plus a close certifies its drain) **symbolic streaming** (the channel as the list its specified producer loop builds — `GNumbers(n)` proves its drained list element by element) **streaming consumers** (a looping process reads element *k*; a consumer reading past its producer "may block forever"; the book's three-process network proves for symbolic `n`) **the looping ALT** (the multiplexer: ghost cursors per branch, the merged count proved, the order honestly nondeterministic) **non-terminating processes** (`while (true)` certified for safety — invariant, send contracts, received values) **liveness under weak fairness** (the wait-for graph lifted to the iteration index: the forever client–server is live, mutual receive-first loops a circular wait in every iteration) **selection semantics** (`ChannelSelect` modelled as it selects on the runtime that hosts the checker — priority and re-sent losers before Groovy 6.0.0-beta-4, the claim-based select with `fair()` / `random()` from beta-4 — with starvation hazards named and the fair server's per-client liveness certified for a held `fair()`, withheld with the policy's reason otherwise), and **cyclic streams** (loops that answer each other — the client–server pair, the fair server's guarded replies — verified by rely/guarantee, so each client proves what it is answered and a wrong claim is refuted; `c.taken` / `c.sent`, the elements a loop has taken or sent so far, name the histories a token ring's closed form or a loop-written stream's law needs; a terminating partner's total bounds what may be read — a server outliving its bounded client is refuted at the read that blocks, and a server that drains its client until the close — the cycle that ends cleanly — verifies whole), and **session types** (a `@Protocol` global type on the method — messages, loops, choices, and `par` for independent sub-sessions interleaved, which types the fair server — projected onto each role and checked against every process's control flow, a violation named with its trace; a *mixed* choice — branches opened by different roles — is admitted and its coherence checked: one initiator certifies, a racing pair is refused with the collision named), and **bounded service** (`@ServedWithin(n)`: a held `fair()` over k branches certifies n >= k; `@DeliveredWithin(n, from, to)`: the end-to-end head-of-line bound summed hop by hop through the pipeline, the worst path deciding; every unbounded policy refutes with its own reason) at compile time; the runtime rungs (Lincheck / TLA+ TLC / Fray) remain the [three rungs](CONCURRENCY.md).
- **[The Kerridge gallery](examples/kerridge.md)** — the CSP teaching shapes from Jon Kerridge's *Using Concurrency and Parallelism Effectively* (JCSP/groovyJCSP, the occam plugAndPlay vocabulary) ported to `groovy.concurrent` and certified: hello-world (including the literal two-message `ProduceHW`, proved in order), GSquares, GPlus, GDelta, client-server, the GNumbers → GSquares → GPrint network (bounded, symbolic, as three looping processes, and as the book writes it — every process forever, live under weak fairness), the forever client–server, ALT one-shot and as the looping multiplexer — values proved, deadlock-freedom mechanised — with the classic student mistakes (the mutual-receive deadlock exercise, the missing poison pill, a receive with nothing left to receive) as *named compile errors*, and the streaming frontier stated honestly.
- **[Units of measurement](examples/units.md)** — the Mars-orbiter bug, three ways: JSR 385 dimensions (the unchecked `as Quantity<K>` cast), JSR 385 value/scale, and a bespoke `record` units type with verified `+`.
- **[Bean Validation](examples/validation.md)** — `jakarta.validation` / `javax.validation` constraints (`@Positive`, `@Min` / `@Max`, `@Size`, `@NotEmpty`) read as compile-time preconditions, discharged for free from annotations you already wrote.
- **[Miscellaneous](examples/miscellaneous.md)** — ring buffer, Duplets, FizzBuzz, a string-concat law, a type hierarchy (inheritance / traits / Liskov), inline `assert` lemmas, and invariant inference.
- **[Metaprogramming](examples/metaprogramming.md)** — the blog's emoji-FizzBuzz `ExpandoMetaClass` examples proved: a metaclass property and an operator overload, type-checked *and* verified from the statically-visible registration — with the compile-error teeth showing the gate stays shut.
- **[JDK specs & exceptional contracts](examples/jdk-specs.md)** — the external-specification registry end to end: the `Math.abs` skeleton and the wrap-bug refute, `clamp` proved by nested spec composition, `Math.abs` as contract vocabulary, `indexOf`-then-`charAt`, `checkIndex`-then-index via survival facts, catch-entry facts, `java.time` instance ranges, and the Unicode honesty edge.
- **[Thread-local IFC (Smith)](examples/smith.md)** — Graeme Smith's Dafny approach: information flow (a security lattice + noninterference) and rely/guarantee, combined in the §VII capstone.

## Verifying Java fragments

The algorithms above are written in Groovy, but **Java is largely a syntactic subset of Groovy** — so you can
often verify *a Java algorithm* by treating it as Groovy source. This is **not** a Java verifier: the proof is over
**Groovy semantics** (see Groovy's own [Differences with Java](https://groovy-lang.org/differences.html)), which for
a typical integer/array algorithm overlap almost entirely. The everyday Java idioms carry over **unchanged** —
semicolons, the C-style `for (int i = …; …; i++)`, typed local declarations, `return`, casts, `new int[]{…}` array
initializers — and the loop carries the same statement-level `@Invariant` / `@Decreases`. A full Java-style `max`
verifies as-is once the contract annotations are added:

<!-- doclint:case p-java-fragment/java-style-max-algorithm-verifies -->
```groovy
@Requires({ a != null && a.length > 0 })
@Ensures({ result >= a[0] })
static int max(int[] a) {
    int m = a[0];
    @Invariant({ m >= a[0] && i >= 1 && i <= a.length })
    @Decreases({ a.length - i })
    for (int i = 1; i < a.length; i++) {
        if (a[i] > m) {
            m = a[i];
        }
    }
    return m;
}
```

Be clear about what this *can't* do for you: **every proof is over Groovy semantics, and the tool has no model of
what a Java author intended** — so where your Java reading and the Groovy reading differ, it does not (and cannot)
flag it. It just proves the Groovy meaning. The discipline is to read the pasted code **as Groovy**. What helps in
practice is that the most dangerous divergence trips Groovy's *own* type system before it ever reaches a proof:

- **Integer division.** Groovy's `/` is **`BigDecimal` ("true") division**, not Java's integer division — `7 / 2`
  is `3.5`, not `3`. Because `@TypeChecked` won't put a `BigDecimal` in an `int` slot, the everyday shapes —
  `int m = (lo + hi) / 2`, a `return x / 2`, an index `a[(lo + hi) / 2]` — are a hard **compile error**
  (*"Cannot assign BigDecimal to int"*), so the commonest Java-paste trap can't slip through as a wrong proof. Note
  this is *Groovy's typing* catching it, not the tool reasoning about Java: in a context Groovy tolerates — a bare
  `BigDecimal` comparison — the verifier proves the Groovy meaning, or loud-skips it as outside the modelled fragment,
  but never re-reads it as Java. The fix is Groovy's `.intdiv()` (the call Bloch's binary-search example uses).
- **Array initializers.** `new int[]{1, 2, 3}` works; the **brace-only** `int[] a = {1, 2, 3}` does **not parse** (in
  Groovy `{…}` is a closure) — use a Groovy list `[1, 2, 3]` (it coerces to the array) or `new int[]{…}`. This is a
  parse error, again Groovy's syntax talking, not a divergence check.

Divergences Groovy's typing *doesn't* object to are simply **proved with Groovy semantics, silently** — no error, no
skip. The cleanest example is `==`: it's Groovy **value**-equality (`.equals`), so `a == b` on two equal `String`s
verifies `result == true`, and a Java author who meant reference-equality has proved a different thing. (`char`
arithmetic is only weakly modelled, so it loud-skips rather than misproves.) For `int` / array algorithms these
rarely bite — but the rule is unconditional: **it's a Groovy proof; read your fragment as Groovy.**

**Two ways to drive it, and why the contracts must compile as Groovy.** The natural idea — leave the contract
annotations on a `.java` file, let `javac` ignore them, and verify the same file as Groovy — **doesn't work**: a
contract is a *closure* (`@Requires({ x > 0 })`), and `javac` rejects that outright (*"annotation value not of an
allowable type"* — an annotation element must be a constant, not an expression over a parameter). So the verified
source is always compiled **as Groovy**. Two practical recipes:

1. **Java-subset source, compiled as Groovy.** Keep the method in Java syntax, add the `@TypeChecked(extensions =
   'verification.VerifyChecker')` and the contracts, and compile it with `groovyc`. Because the closure contracts
   live in a Groovy compile, groovy-contracts also injects the **runtime** checks — so you *keep* the runtime backup
   (the [runtime rung](BUILD.md)), you don't lose it. The trade is that this unit is Groovy-compiled (bytecode-compatible
   from Java), not `javac`-compiled.
2. **Body transplant.** Paste the Java method body into a small Groovy skeleton carrying the signature + contracts.
   The most robust option when the surrounding file isn't in the overlap — the body just has to be in the fragment.

**Closing the gap: String-valued contracts (prototype).** What blocks recipe 0 — keeping the contracts on a real
`.java` file — is only that a *closure* isn't a legal Java annotation value. A `String` is. So this project ships
Java-friendly twins, `verification.@Requires` / `@Ensures` / `@Decreases`, whose condition is a `String`:

<!-- doclint:case p-string-contract/recursive-count-verifies-from-string-contracts -->
```groovy
@Requires('n >= 0')
@Ensures('result == n')
@Decreases('n')
static int count(int n) {
    if (n == 0) return 0;
    return 1 + count(n - 1);
}
```

That exact method compiles under `javac` (the annotations become inert metadata) **and** verifies under
`VerifyChecker` when the same source is read as Groovy — the condition text is captured into the identical
reparse→prove pipeline a closure uses (so it's still parsed with Groovy semantics; a recursive method proves by
induction off the method-level `@Decreases`, and a wrong `@Ensures` refutes on the base case). It reaches **loop-free
and recursive** methods only: Java forbids annotating a statement, so a per-loop `@Invariant` has nowhere to live —
for an iterative loop you still drop to recipe 1 or 2. And being verify-only on the `javac` side, the runtime backup
is regained only by compiling as Groovy. A prototype, but it makes "annotate Java, verify it" a single source file.

## Relationship to Groovy's other checkers

groovy-verify is one of a family of `@TypeChecked` extensions, owning a narrow, deep slice — SMT-backed *functional*
verification — and it composes orthogonally with its siblings. A whole-class, *four*-checker compile:

<!-- doclint:case p-fourchecker/readme-maybe-under-four-checkers-do -->
```groovy
@Monadic(bind = 'flatMap', map = 'map')
@TypeChecked(extensions = ['groovy.typecheckers.NullChecker', 'groovy.typecheckers.MonadicChecker',
                           'groovy.typecheckers.PurityChecker', 'verification.VerifyChecker'])
class Maybe {                                              // a hand-rolled Some(value) | None
    final boolean present
    final Object value
    private Maybe(boolean present, Object value) { this.present = present; this.value = value }
    @Pure static Maybe some(Object v) { new Maybe(true, v) }   // unit
    @Pure static Maybe none()         { new Maybe(false, null) }

    @Requires({ f != null }) Maybe flatMap(Function f) { present ? (Maybe) f.apply(value) : this }
    @Requires({ g != null }) Maybe map(Function g)     { present ? some(g.apply(value)) : this }   // Vavr-style

    static Maybe addPair() { DO(a in some(2), b in some(3)) { some(((Integer) a) + ((Integer) b)) } }
}
```

Each extension does a *distinct* job on the one class: **MonadicChecker** shape-checks the `DO` comprehension,
**PurityChecker** the side-effect freedom of the `@Pure` `some` / `none`, **NullChecker** the nullness, and
**groovy-verify** proves the five monad/functor laws from `@Monadic` alone — all four compile quietly because this
`Maybe` *is* lawful. How groovy-verify relates to Groovy's null tooling, and how it pairs orthogonally with the
regex, combiner, monadic, and purity checkers — each owning *shape* or *syntax* while groovy-verify owns the
*laws* — is in **[examples/checkers.md](examples/checkers.md)**.

## Tool knobs

Nine environment variables (`VERIFY_REFUTATION`, `VERIFY_SUGGEST`, `VERIFY_EXPLAIN`, `VERIFY_VERBOSE`,
`VERIFY_CACHE_STATS`, `VERIFY_DUMP_SMT`, `VERIFY_PACKS`, `VERIFY_Z3_TIMEOUT_MS`, `VERIFY_SPECS`) tune what
the checker *runs and reports*; unset, the default path is byte-identical. Two honest asterisks: the
timeout knob moves the prove/refute-vs-undecided boundary for *slower hardware* (CI sets 8000) without
changing what an answer means, and `VERIFY_SPECS` selects which *trusted* external specifications are
consulted — trusted facts can change what proves, which is why every consumed spec is recorded. Each is documented with worked examples in
**[TOOLING.md](TOOLING.md)**.

## Encoding packs

Domain vocabularies plug in as **encoding packs** (experimental): `ServiceLoader`-discovered modules
contributing a library's recognisers and axioms — packs model *libraries*, the core models the *language*.
Three reference packs ship in tree: the number-theory spec helpers (`Fib.of`/`Gcd.of`/… — extended with
the Bézout coefficients, through which Gauss's lemma proves), the whole JSR 385 units domain, and a
combinatorics pack (`Fact.of`, Pascal-rule `Binom.of(n, k)` — the first two-argument spec primitive); each
is pinned by its own verify/refute case groups (attributed in the generated `catalog.json`). The SPI, the soundness obligations, and a worked minimum pack are in
**[PACKS.md](PACKS.md)**.

## External specifications

Where packs contribute a library's *vocabulary and axioms*, the **external-specification registry**
contributes a library's *method contracts* — the same principle one level up, and JML's `.jml`-file
idea in the project's own dialect. A spec is an ordinary Groovy **skeleton**: the target class
re-declared with the same gc annotations user code carries (`@ThrowsIf` arms included — the stock
upstream annotation since GROOVY-12135, with `woven = false, direct = false` spelling a trusted
third-party claim) and empty bodies, discovered lazily as the classpath resource `META-INF/groovy-verify/specs/<fqn>.groovy`
and parsed AST-only — never compiled, never executed. Consumption is symmetric with in-code contracts
(`@Requires` = call-site obligation, `@Ensures` = assumed result, `@Pure` = usable *inside* your own
contracts, `@ThrowsIf` = survival and catch-entry facts), with typed overload matching and both
instance and receiver-state forms. Every registry spec is **trusted by definition** — nobody proves
the JDK's bodies — so every consumption is recorded in the **trusted-spec ledger** (one inventory
across in-place spec-only contracts and registry facts, printed beside the harness perf line and
linted by DocLint), and the runtime rung cross-checks the specs against the live JDK. Skeletons for
the everyday JDK surface ship in the jar (`Math`, `Integer`, `Long`, `Character`, `Objects`,
`Arrays`, `Collections`, `List`, `String`, `java.time`); the whole arc is worked through in
**[examples/jdk-specs.md](examples/jdk-specs.md)**.

### What about dynamic Groovy?

A point that may not be obvious: everything above lives in Groovy's **statically-checkable subset** — the
verifier's front door is `@TypeChecked`, so runtime metaprogramming (metaclass changes, `methodMissing`,
categories, dynamic dispatch) has been out of scope from the start, ruled out by the type checker before
the encoder ever sees it. That is a *posture*, not an accident: you can't prove theorems about code whose
meaning is decided at runtime — unless the runtime reshaping is itself statically visible.

The **metaprogramming pack** (experimental) is that exception, and it rests on a subtle point: Groovy's
type checking is extensible in **two directions**. An STC extension can *strengthen* checking —
groovy-verify itself is exactly that, an extension that piles proof obligations on top of the type
system — and it can *selectively relax* it, typing what looks like uncheckable dynamic code when there is
evidence to type it from. The pack does both at once: when an `ExpandoMetaClass` registration is spelled
out in the same class (`Integer.metaClass.getFizzBuzz = { … }`, or an operator method
`Integer.metaClass.multiply = { String s -> … }`), it types the registration and its use sites under
`@TypeChecked` (relaxation, from the registered closure's own signature), then models them by inlining
that closure at each use and holds the result to a full functional specification (strengthening). The
blog's emoji-FizzBuzz metaclass examples prove against exact specs this way, teeth included — worked
through in **[examples/metaprogramming.md](examples/metaprogramming.md)**. The gate is deliberately narrow
and evidence-backed: no visible registration, no blessing — the code stays a compile error, exactly as
`@TypeChecked` demands. Metaprogramming the pack cannot faithfully model is not quietly admitted; it
simply remains outside.

## Building & using

Built with JDK 25 against `org.apache.groovy:6.0.0-beta-3` from Maven Central (which ships the
upstream `@ThrowsIf` / `@Requires(woven, direct)` contracts — GROOVY-12135/12136 — the build
previously tracked the ASF snapshot for); the published artifact targets Java 17 bytecode, Groovy 6's
own floor. `./gradlew verify`
runs the compact console suite (one line per case); `./gradlew test` runs the same `CASES` data list as
JUnit 6 dynamic tests, and `./gradlew check` additionally enforces the doc-drift lints. Consume it from
Maven Central — `compileOnly 'io.github.paulk-asert:groovy-verify:0.1.0'` (it's compile-time tooling;
you supply Groovy 6 and groovy-contracts) — or via a local install, a Gradle composite build, or JitPack.

The full command set (verbose / cache-stats flags, the single-source `CASES` self-test design, the doc-drift
gate) and the consumption details (scope guidance, requirements, the global-transform note) live in
**[BUILD.md](BUILD.md)**.

## Architecture

The codebase map — the component table, the compile-time pipeline (how
`ContractExpansionTransform` captures contracts at `CONVERSION` *before*
groovy-contracts erases them, the metadata handoff to `VerifyChecker`, and the
`SmtSession` solver seam) — lives in **[ARCHITECTURE.md](ARCHITECTURE.md)**.

## License

Apache-2.0.
